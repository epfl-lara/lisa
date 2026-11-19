package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers.PremiseSequentTactic
import lisa.utils.prooflib.ProofHelpers.SequentTactic

import scala.collection.mutable

/**
 * Prove congruence goals using equality explanations and proof-backed substitution.
 */
object Congruence extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  protected def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    proveFromPremises(conclusion, premises) match
      case Right(theorem) => ProofJudgement(theorem)
      case Left(message) => ProofCarrier(Set(SoftError(message, file, line)), conclusion, None, ())

  private def checked(result: Either[?, K.Thm]): Either[String, K.Thm] = result.left.map(_.toString)

  private def proveFromPremises(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): Either[String, Thm] =
    given K.Theory = library.theory
    val reusable = premises.find(premise => premise.kernel.left.subsetOf(conclusion.underlying.left) && premise.kernel.right.subsetOf(conclusion.underlying.right))
    if premises.exists(premise => !(premise.kernel.theory eq library.theory)) then Left("A premise belongs to a different theory.")
    else if premises.isEmpty then solve(conclusion)
    else if reusable.nonEmpty then
      val premise = reusable.get
      val proof = if premise.kernel.statement == conclusion.underlying then Right(premise.kernel) else checked(K.Weakening(conclusion.underlying, premise.kernel))
      proof.map(Thm(conclusion, _))
    else
      val added = premises.map(premise => premise -> betaReduce(orAllOrFalse(premise.right))).filterNot((_, formula) => conclusion.left.contains(formula))
      solve(Sequent(conclusion.left ++ added.map(_._2), conclusion.right)).flatMap { initial =>
        added
          .foldLeft(Right(initial.kernel): Either[String, K.Thm]) { case (result, (premise, assumption)) =>
            result.flatMap { current =>
              current.left.find(K.isSame(_, assumption.underlying)) match
                case None => Right(current)
                case Some(actual) =>
                  val retained = current.left - actual
                  for
                    normalized <- checked(K.Restate(K.Sequent(premise.kernel.left, Set(assumption.underlying)), premise.kernel))
                    cut <- checked(K.Cut(K.Sequent(retained ++ premise.kernel.left, current.right), normalized, current, assumption.underlying))
                    reduced <- premise.left.foldLeft(Right(cut): Either[String, K.Thm]) { (result, required) =>
                      result.flatMap { proof =>
                        if retained.exists(K.isSame(_, required.underlying)) then Right(proof)
                        else
                          proof.left.find(K.isSame(_, required.underlying)) match
                            case None => Right(proof)
                            case Some(actual) =>
                              val remaining = proof.left - actual
                              solve(Thm.liftSequent(K.Sequent(remaining, Set(required.underlying)))).flatMap { justification =>
                                checked(K.Cut(K.Sequent(remaining, proof.right), justification.kernel, proof, required.underlying))
                              }
                      }
                    }
                  yield reduced
            }
          }
          .flatMap { proof =>
            val aligned = if proof.statement == conclusion.underlying then Right(proof) else checked(K.Restate(conclusion.underlying, proof))
            aligned.map(Thm(conclusion, _))
          }
      }

  /**
   * Compute congruence closure only when direct sequent closure fails.
   */
  def solve(using library: Library)(conclusion: Sequent): Either[String, Thm] =
    given K.Theory = library.theory
    val target = conclusion.underlying
    K.RestateTrue(target).toOption match
      case Some(proof) => Right(Thm(conclusion, proof))
      case None =>
        val graph = EGraphExpr()
        graph.addAll(conclusion.left)
        graph.addAll(conclusion.right)
        conclusion.left.foreach {
          case equality(left, right) => graph.merge(left, right)
          case iff(left, right) => graph.merge(left, right)
          case _ => ()
        }
        val reconstruction = Reconstruction(graph, conclusion)
        def first[A](values: Iterator[A])(attempt: A => Option[K.Thm]): Option[K.Thm] = values.flatMap(attempt).nextOption()
        def matchingPairs(left: Set[Expr[Prop]], right: Iterable[Expr[Prop]]): Iterator[(Expr[Prop], Expr[Prop])] =
          if right.isEmpty then Iterator.empty
          else if left.size > 1 && right.size > 1 then
            val classes = left.groupBy(graph.find)
            right.iterator.flatMap(r => classes.getOrElse(graph.find(r), Set.empty).iterator.map(_ -> r))
          else left.iterator.flatMap(l => right.iterator.filter(graph.idEq(l, _)).map(l -> _))
        val matching = first(matchingPairs(conclusion.left, conclusion.right)) { (left, right) =>
          reconstruction.transport(left, right).toOption
        }
        val contradictoryLeft = matching.orElse {
          val negatives = conclusion.left.collect { case neg(negative) => negative }
          first(matchingPairs(conclusion.left, negatives)) { (positive, negative) =>
            reconstruction.contradiction(positive, negative, onLeft = true).toOption
          }
        }
        val contradictoryRight = contradictoryLeft.orElse {
          val negatives = conclusion.right.collect { case neg(negative) => negative }
          first(matchingPairs(conclusion.right, negatives)) { (positive, negative) =>
            reconstruction.contradiction(positive, negative, onLeft = false).toOption
          }
        }
        val explicitEquality = contradictoryRight.orElse {
          def comparison(formula: Expr[Prop]): Option[K.Thm] = formula match
            case equality(left, right) if graph.idEq(left, right) => reconstruction.compare(left, right).toOption
            case iff(left, right) if graph.idEq(left, right) => reconstruction.compare(left, right).toOption
            case _ => None
          first(conclusion.right.iterator)(comparison).orElse {
            first(conclusion.left.iterator.collect { case neg(formula) => formula }) { formula =>
              comparison(formula).flatMap { proof =>
                K.LeftNot(K.Sequent(proof.left + neg(formula).underlying, Set.empty), proof, formula.underlying).toOption
              }
            }
          }
        }
        explicitEquality.toRight(s"No congruence found to show sequent\n$conclusion").flatMap { proof =>
          val aligned = if proof.statement == target then Right(proof) else checked(K.Weakening(target, proof))
          aligned.map(Thm(conclusion, _))
        }

  private[prooflib] def proveEquality[S](using library: Library)(graph: EGraphExpr, left: Expr[S], right: Expr[S], base: Sequent): Either[String, Thm] =
    val goal = Sequent(base.left, base.right + makeEq(left, right))
    val result =
      if left == right then checked(K.RestateTrue(using library.theory)(goal.underlying))
      else Reconstruction(graph, base).compare(left, right)
    result.flatMap { proof =>
      val aligned = if proof.statement == goal.underlying then Right(proof) else checked(K.Weakening(using library.theory)(goal.underlying, proof))
      aligned.map(Thm(goal, _))
    }

  /**
   * Keep explanation proofs and fresh context variables local to one invocation.
   */
  private class Reconstruction(graph: EGraphExpr, conclusion: Sequent)(using library: Library):
    given K.Theory = library.theory
    private val proofs = mutable.HashMap.empty[(Expr[?], Expr[?]), Either[String, K.Thm]]
    private lazy val freshStart = (conclusion.underlying.left ++ conclusion.underlying.right).iterator.flatMap(_.freeVariables).map(_.id.no).maxOption.getOrElse(-1) + 1

    // E-graph merges are restricted to Ind and Prop, so no extensional lifting is needed.
    private def equation(left: Expr[?], right: Expr[?]): K.Expression =
      if left.sort == K.Prop then K.iff(left.underlying)(right.underlying) else K.equality(left.underlying)(right.underlying)

    def compare(left: Expr[?], right: Expr[?]): Either[String, K.Thm] =
      proofs.getOrElseUpdate(
        (left, right), {
          graph.explain(left, right).toRight("Expressions are not congruent.").flatMap {
            case Nil => checked(K.RestateTrue(K.Sequent(Set.empty, Set(equation(left, right)))))
            case head :: tail =>
              edge(head).flatMap { first =>
                tail.foldLeft(Right(first): Either[String, K.Thm]) { (result, step) =>
                  for
                    prefix <- result
                    next <- edge(step)
                    composed <- compose(left, step.between._1, step.between._2, prefix, next)
                  yield composed
                }
              }
          }
        }
      )

    private def compose(start: Expr[?], middle: Expr[?], end: Expr[?], prefix: K.Thm, edge: K.Thm): Either[String, K.Thm] =
      val target = K.Sequent(prefix.left ++ edge.left, Set(equation(start, end)))
      val hole = variable(K.Identifier("chain", freshStart), middle.sort)
      checked(K.RightSubst(target, prefix, Seq(edge), Seq((middle.underlying, end.underlying, Nil)), Seq(hole.underlying) -> equation(start, hole)))

    private def edge(step: graph.Step): Either[String, K.Thm] =
      val (left, right) = step.between
      step match
        case _: graph.ExternalStep =>
          val pivot = equation(left, right)
          val assumption = if conclusion.underlying.left.contains(pivot) then pivot else equation(right, left)
          checked(K.Hypothesis(K.Sequent(Set(assumption), Set(pivot)), pivot))
        case _: graph.CongruenceStep =>
          checked(K.RestateTrue(K.Sequent(Set.empty, Set(equation(left, left))))).flatMap { reflexive =>
            rewrite(left, right, reflexive, expression => equation(left, expression), expandRoot = true)
          }

    def transport(left: Expr[Prop], right: Expr[Prop]): Either[String, K.Thm] =
      checked(K.Hypothesis(K.Sequent(Set(left.underlying), Set(left.underlying)), left.underlying)).flatMap { identity =>
        rewrite(left, right, identity, _.underlying, expandRoot = expandable(left, right))
      }

    def contradiction(positive: Expr[Prop], negative: Expr[Prop], onLeft: Boolean): Either[String, K.Thm] =
      val formulas = Set(positive.underlying, K.neg(positive.underlying))
      val statement = if onLeft then K.Sequent(formulas, Set.empty) else K.Sequent(Set.empty, formulas)
      checked(K.RestateTrue(statement)).flatMap { proof =>
        rewrite(positive, negative, proof, expression => K.neg(expression.underlying), expandable(positive, negative), onLeft)
      }

    // External equalities need not identify arguments; unfold only congruence edges.
    private def expandable(left: Expr[?], right: Expr[?]): Boolean = graph.explain(left, right).exists {
      case List(_: graph.CongruenceStep) => true
      case _ => false
    }

    private def rewrite(left: Expr[?], right: Expr[?], premise: K.Thm, wrap: Expr[?] => K.Expression, expandRoot: Boolean, onLeft: Boolean = false): Either[String, K.Thm] =
      val holes = mutable.LinkedHashMap.empty[(Expr[?], Expr[?]), Variable[?]]
      val contexts = mutable.HashMap.empty[(Expr[?], Expr[?], Boolean), Expr[?]]
      def context(source: Expr[?], target: Expr[?], descend: Boolean): Expr[?] =
        contexts.getOrElseUpdate((source, target, descend), buildContext(source, target, descend))
      def buildContext(source: Expr[?], target: Expr[?], descend: Boolean): Expr[?] =
        if source == target then source
        else
          (source, target) match
            case (Multiapp(label, args), Multiapp(other, targets)) if descend && label == other && args.size == targets.size && args.nonEmpty =>
              Multiapp.unsafe(label, args.zip(targets).map((a, b) => context(a, b, expandable(a, b))))
            case _ => holes.getOrElseUpdate((source, target), variable(K.Identifier("hole", freshStart + holes.size), source.sort))
      val body = wrap(context(left, right, descend = expandRoot))
      holes.keysIterator
        .foldLeft(Right(Vector.empty): Either[String, Vector[K.Thm]]) { case (result, (source, target)) =>
          for accumulated <- result; proof <- compare(source, target) yield accumulated :+ proof
        }
        .flatMap { comparisons =>
          val retained = if onLeft then premise.left - wrap(left) else premise.left
          val assumptions = comparisons.foldLeft(retained)(_ ++ _.left)
          val replacements = holes.keysIterator.map((a, b) => (a.underlying, b.underlying, Seq.empty[K.Variable])).toSeq
          val schema = holes.valuesIterator.map(_.underlying).toSeq -> body
          if onLeft then checked(K.LeftSubst(K.Sequent(assumptions + wrap(right), premise.right), premise, comparisons, replacements, schema))
          else checked(K.RightSubst(K.Sequent(assumptions, (premise.right - wrap(left)) + wrap(right)), premise, comparisons, replacements, schema))
        }

/**
 * Union-find retaining an uncompressed explanation forest.
 */
final class UnionFind[T]:
  val parent: mutable.Map[T, T] = mutable.HashMap.empty
  val realParent: mutable.Map[T, (T, ((T, T), Boolean, Int))] = mutable.HashMap.empty
  val rank: mutable.Map[T, Int] = mutable.HashMap.empty
  private var unionCounter = 0

  def add(value: T): Unit =
    if !parent.contains(value) then
      parent(value) = value
      realParent(value) = value -> ((value -> value), true, 0)
      rank(value) = 0

  def find(value: T): T =
    var root = value
    while parent(root) != root do root = parent(root)
    var current = value
    while parent(current) != root do
      val next = parent(current)
      parent(current) = root
      current = next
    root

  def union(left: T, right: T): Unit =
    unionCounter += 1
    val leftRoot = find(left)
    val rightRoot = find(right)
    if leftRoot != rightRoot then
      if rank(leftRoot) < rank(rightRoot) then
        parent(leftRoot) = rightRoot
        realParent(leftRoot) = rightRoot -> ((left -> right), true, unionCounter)
      else
        parent(rightRoot) = leftRoot
        realParent(rightRoot) = leftRoot -> ((left -> right), false, unionCounter)
        if rank(leftRoot) == rank(rightRoot) then rank(leftRoot) += 1

  private def pathToRoot(value: T): List[T] =
    if value == find(value) then List(value) else value :: pathToRoot(realParent(value)._1)

  private def lowestCommonAncestor(left: T, right: T): Option[T] =
    val rightPath = pathToRoot(right).toSet
    pathToRoot(left).find(rightPath)

  /**
   * Returns original union edges forming a path from `left` to `right`.
   */
  def explain(left: T, right: T): Option[List[(T, T)]] =
    if left == right then Some(Nil)
    else
      lowestCommonAncestor(left, right).flatMap: ancestor =>
        var latest: ((T, T), Boolean, Int) = ((left -> left), true, 0)
        var current = left
        while current != ancestor do
          val (next, (edge, orientation, order)) = realParent(current)
          if order > latest._3 then latest = (edge, orientation, order)
          current = next
        current = right
        while current != ancestor do
          val (next, (edge, orientation, order)) = realParent(current)
          if order > latest._3 then latest = (edge, !orientation, order)
          current = next
        val (edgeLeft, edgeRight) = latest._1
        if latest._2 then
          for
            prefix <- explain(left, edgeLeft)
            suffix <- explain(edgeRight, right)
          yield prefix ++ ((edgeLeft, edgeRight) :: suffix)
        else
          for
            prefix <- explain(left, edgeRight)
            suffix <- explain(edgeLeft, right)
          yield prefix ++ ((edgeLeft, edgeRight) :: suffix)

  def getClasses: Set[T] = parent.keysIterator.map(find).toSet

/**
 * E-graph with explanations for external and congruence merges.
 */
final class EGraphExpr:
  val UF = UnionFind[Expr[?]]()
  private val parents = mutable.HashMap.empty[Expr[?], mutable.Set[Expr[?]]]
  private val codes = mutable.HashMap.empty[Expr[?], Int]

  sealed trait Step:
    def between: (Expr[?], Expr[?])
  final case class ExternalStep(between: (Expr[?], Expr[?])) extends Step
  final case class CongruenceStep(between: (Expr[?], Expr[?])) extends Step

  private val proofMap = mutable.HashMap.empty[(Expr[?], Expr[?]), Step]
  private type Signature = (Expr[?], List[Int])
  private val signatures = mutable.HashMap.empty[Signature, Expr[?]]

  def find[S](expression: Expr[S]): Expr[S] = UF.find(expression).asInstanceOf[Expr[S]]

  def idEq(left: Expr[?], right: Expr[?]): Boolean = find(left) == find(right)

  def explain(left: Expr[?], right: Expr[?]): Option[List[Step]] =
    UF.explain(left, right)
      .map: edges =>
        edges
          .foldLeft((left: Any) -> List.empty[Step]):
            case ((previous, result), edge) =>
              proofMap(edge) match
                case step @ ExternalStep((from, to)) if from == previous => (to: Any) -> (step :: result)
                case ExternalStep((from, to)) if to == previous => (from: Any) -> (ExternalStep(to -> from) :: result)
                case step @ CongruenceStep((from, to)) if from == previous => (to: Any) -> (step :: result)
                case CongruenceStep((from, to)) if to == previous => (from: Any) -> (CongruenceStep(to -> from) :: result)
                case _ => throw new IllegalStateException("Invalid e-graph explanation chain.")
          ._2
          .reverse

  def add[S](expression: Expr[S]): Expr[S] =
    if !codes.contains(expression) then
      codes(expression) = codes.size
      UF.add(expression)
      parents.getOrElseUpdate(expression, mutable.HashSet.empty)
      expression match
        case Multiapp(_, arguments) =>
          arguments.foreach: argument =>
            add(argument)
            parents(find(argument)) += expression
      signatures(signature(expression)) = expression
    expression

  def addAll(expressions: Iterable[Expr[Prop]]): Unit = expressions.foreach(add)

  def merge[S](left: Expr[S], right: Expr[S]): Unit =
    mergeWithStep(left, right, ExternalStep(left -> right))

  private def signature(expression: Expr[?]): Signature =
    expression match
      case Multiapp(label, arguments) => label -> arguments.map(argument => codes(find(argument))).toList

  private def mergeWithStep(left: Expr[?], right: Expr[?], step: Step): Unit =
    if left.sort != right.sort then throw new IllegalArgumentException("Cannot merge expressions of different sorts.")
    if left.sort == K.Ind || left.sort == K.Prop then
      val leftRoot = find(left)
      val rightRoot = find(right)
      if leftRoot != rightRoot then
        proofMap(left -> right) = step
        val (small, large) =
          if parents(leftRoot).size < parents(rightRoot).size then left -> right else right -> left
        val smallRoot = find(small)
        val largeRoot = find(large)
        val smallParents = parents(smallRoot).toVector
        smallParents.foreach: parent =>
          val oldSignature = signature(parent)
          if signatures.get(oldSignature).contains(parent) then signatures.remove(oldSignature)
        codes(smallRoot) = codes(largeRoot)
        UF.union(left, right)
        val newRoot = find(left)
        val work = Vector.newBuilder[(Expr[?], Expr[?], Step)]
        smallParents.foreach: parent =>
          val canonical = signature(parent)
          signatures.get(canonical) match
            case Some(other) if find(parent) != find(other) => work += ((parent, other, CongruenceStep(parent -> other)))
            case None => signatures(canonical) = parent
            case _ => ()
        parents(newRoot) = parents(largeRoot) ++ parents(smallRoot)
        work.result().foreach(mergeWithStep)

  /**
   * Reconstruct an equality or equivalence from the graph's explanation.
   */
  def proveExpr[S](using Library)(left: Expr[S], right: Expr[S], base: Sequent): Either[String, Thm] =
    Congruence.proveEquality(this, left, right, base)
