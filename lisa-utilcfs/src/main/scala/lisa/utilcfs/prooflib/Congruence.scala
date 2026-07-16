package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.collection.Extensions.*
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.Helpers.containsEq
import lisa.utilcfs.prooflib.ProofHelpers.{PremiseSequentTactic, SequentTactic}

import scala.collection.mutable

/** Congruence closure over term equality and formula equivalence. */
object Congruence extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  protected def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    proveFromPremises(conclusion, premises) match
      case Right(theorem) => ProofJudgement(theorem)
      case Left(message) => ProofCarrier(Set(SoftError(message, file, line)), conclusion, None, ())

  private def proveFromPremises(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): Either[String, Thm] =
    val addedPremises = premises.iterator
      .map(premise => premise -> betaReduce(orAllOrFalse(premise.right)))
      .filterNot((_, formula) => conclusion.left.contains(formula))
      .toSeq
    val temporary = addedPremises.map(_._2)
    val augmented = Sequent(conclusion.left ++ temporary, conclusion.right)
    solve(augmented).flatMap: initial =>
      addedPremises.foldLeft(Right(initial): Either[String, Thm]):
        case (currentResult, (premise, assumption)) =>
          currentResult.flatMap: current =>
            current.left.find(isSame(_, assumption)) match
              case None => Right(current)
              case Some(actualAssumption) =>
                val premiseAsFormula = Sequent(premise.left, Set(assumption))
                val retained = current.left - actualAssumption
                for
                  normalized <- K.Restate(using library.theory)(premiseAsFormula.underlying, premise.kernel).left.map(_.toString)
                  cutStatement = Sequent(retained ++ premise.left, current.right)
                  cut <- K.Cut(using library.theory)(cutStatement.underlying, normalized, current.kernel, assumption.underlying).left.map(_.toString)
                  reduced <- premise.left.foldLeft(Right(Thm(cutStatement, cut)): Either[String, Thm]):
                    case (stepResult, premiseAssumption) =>
                      stepResult.flatMap: step =>
                        if retained.containsEq(premiseAssumption) then Right(step)
                        else
                          step.left.find(isSame(_, premiseAssumption)) match
                            case None => Right(step)
                            case Some(actual) =>
                              val proofStatement = Sequent(step.left - actual, Set(premiseAssumption))
                              solve(proofStatement).flatMap: assumptionProof =>
                                val result = Sequent(step.left - actual, step.right)
                                K.Cut(using library.theory)(result.underlying, assumptionProof.kernel, step.kernel, premiseAssumption.underlying)
                                  .left.map(_.toString).map(Thm(result, _))
                yield reduced
      .flatMap: theorem =>
        K.Restate(using library.theory)(conclusion.underlying, theorem.kernel).left.map(_.toString).map(Thm(conclusion, _))

  /** Computes congruence closure and reconstructs a theorem when it closes the sequent. */
  def solve(using library: Library)(conclusion: Sequent): Either[String, Thm] =
    val egraph = EGraphExpr()
    egraph.addAll(conclusion.left)
    egraph.addAll(conclusion.right)
    conclusion.left.foreach:
      case equality(left, right) => egraph.merge(left, right)
      case iff(left, right) => egraph.merge(left, right)
      case _ => ()

    val result =
      K.RestateTrue(using library.theory)(conclusion.underlying).toOption
        .orElse(closeLeftRight(egraph, conclusion))
        .orElse(closeLeftContradiction(egraph, conclusion))
        .orElse(closeRightContradiction(egraph, conclusion))
        .orElse(closeExplicitEquality(egraph, conclusion))

    result.toRight(s"No congruence found to show sequent\n$conclusion").map(Thm(conclusion, _))

  private def closeLeftRight(using library: Library)(egraph: EGraphExpr, conclusion: Sequent): Option[K.Thm] =
    conclusion.left.iterator.flatMap: left =>
      conclusion.right.iterator.filter(egraph.idEq(left, _)).flatMap: right =>
        val baseStatement = Sequent(conclusion.left, conclusion.right + left)
        val equality = makeEq(left, right)
        val variable = lisa.utilcfs.fol.FOL.variable[Prop]
        for
          base <- K.Hypothesis(using library.theory)(baseStatement.underlying, left.underlying).toOption
          equalityProof <- egraph.proveExpr(left, right, conclusion).toOption.map(_.kernel)
          substituted <- K.RightSubstEq(using library.theory)(
            Sequent(conclusion.left + equality, conclusion.right).underlying,
            base,
            Seq(left.underlying -> right.underlying),
            Seq(variable.underlying) -> variable.underlying
          ).toOption
          result <- K.Cut(using library.theory)(conclusion.underlying, equalityProof, substituted, equality.underlying).toOption
        yield result
    .nextOption()

  private def closeLeftContradiction(using library: Library)(egraph: EGraphExpr, conclusion: Sequent): Option[K.Thm] =
    conclusion.left.iterator.flatMap: positive =>
      conclusion.left.iterator.collect:
        case negated @ neg(negative) if egraph.idEq(positive, negative) => positive -> negative
      .flatMap: (positive, negative) =>
        val equality = makeEq(positive, negative)
        val variable = lisa.utilcfs.fol.FOL.variable[Prop]
        val base = Sequent(conclusion.left + neg(positive), conclusion.right)
        for
          baseProof <- K.RestateTrue(using library.theory)(base.underlying).toOption
          equalityProof <- egraph.proveExpr(positive, negative, conclusion).toOption.map(_.kernel)
          substituted <- K.LeftSubstEq(using library.theory)(
            Sequent(conclusion.left + equality, conclusion.right).underlying,
            baseProof,
            Seq(positive.underlying -> negative.underlying),
            Seq(variable.underlying) -> neg(variable).underlying
          ).toOption
          result <- K.Cut(using library.theory)(conclusion.underlying, equalityProof, substituted, equality.underlying).toOption
        yield result
    .nextOption()

  private def closeRightContradiction(using library: Library)(egraph: EGraphExpr, conclusion: Sequent): Option[K.Thm] =
    conclusion.right.iterator.flatMap: positive =>
      conclusion.right.iterator.collect:
        case negated @ neg(negative) if egraph.idEq(negative, positive) => negative -> positive
      .flatMap: (negative, positive) =>
        val equality = makeEq(negative, positive)
        val variable = lisa.utilcfs.fol.FOL.variable[Prop]
        val base = Sequent(conclusion.left, conclusion.right + neg(positive))
        for
          baseProof <- K.RestateTrue(using library.theory)(base.underlying).toOption
          equalityProof <- egraph.proveExpr(negative, positive, conclusion).toOption.map(_.kernel)
          substituted <- K.RightSubstEq(using library.theory)(
            Sequent(conclusion.left + equality, conclusion.right).underlying,
            baseProof,
            Seq(positive.underlying -> negative.underlying),
            Seq(variable.underlying) -> neg(variable).underlying
          ).toOption
          result <- K.Cut(using library.theory)(conclusion.underlying, equalityProof, substituted, equality.underlying).toOption
        yield result
    .nextOption()

  private def closeExplicitEquality(using library: Library)(egraph: EGraphExpr, conclusion: Sequent): Option[K.Thm] =
    val positive = conclusion.right.iterator.collectFirstDefined:
      case equality(left, right) if egraph.idEq(left, right) => egraph.proveExpr(left, right, conclusion).toOption.map(_.kernel)
      case iff(left, right) if egraph.idEq(left, right) => egraph.proveExpr(left, right, conclusion).toOption.map(_.kernel)
      case _ => None
    positive.orElse:
      conclusion.left.iterator.collectFirstDefined:
        case neg(equality(left, right)) if egraph.idEq(left, right) =>
          egraph.proveExpr(left, right, conclusion).toOption.flatMap(thm => K.Restate(using library.theory)(conclusion.underlying, thm.kernel).toOption)
        case neg(iff(left, right)) if egraph.idEq(left, right) =>
          egraph.proveExpr(left, right, conclusion).toOption.flatMap(thm => K.Restate(using library.theory)(conclusion.underlying, thm.kernel).toOption)
        case _ => None

/** Union-find retaining an uncompressed explanation forest. */
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

  /** Returns original union edges forming a path from `left` to `right`. */
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

/** E-graph with explanations for external and congruence merges. */
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
    UF.explain(left, right).map: edges =>
      edges.foldLeft((left: Any) -> List.empty[Step]):
        case ((previous, result), edge) =>
          proofMap(edge) match
            case step @ ExternalStep((from, to)) if from == previous => (to: Any) -> (step :: result)
            case ExternalStep((from, to)) if to == previous => (from: Any) -> (ExternalStep(to -> from) :: result)
            case step @ CongruenceStep((from, to)) if from == previous => (to: Any) -> (step :: result)
            case CongruenceStep((from, to)) if to == previous => (from: Any) -> (CongruenceStep(to -> from) :: result)
            case _ => throw new IllegalStateException("Invalid e-graph explanation chain.")
      ._2.reverse

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

  /** Reconstructs an equality/iff theorem from an e-graph explanation. */
  def proveExpr[S](using library: Library)(left: Expr[S], right: Expr[S], base: Sequent): Either[String, Thm] =
    explain(left, right).toRight("Expressions are not congruent.").flatMap: steps =>
      if steps.isEmpty then reflexive(left, right, base)
      else
        steps.foldLeft(Right(None): Either[String, Option[(Expr[?], K.Thm)]]):
          case (acc, step) =>
            for
              previous <- acc
              edge <- proveEdge(step, base)
              next <- previous match
                case None => Right(Some(step.between._2 -> edge))
                case Some((current, proof)) =>
                  compose(left, current, step.between._2, proof, edge, base).map(theorem => Some(step.between._2 -> theorem))
            yield next
        .flatMap(_.toRight("Empty congruence explanation."))
        .flatMap: (_, theorem) =>
          val goal = Sequent(base.left, base.right + makeEq(left, right))
          K.Restate(using library.theory)(goal.underlying, theorem).left.map(_.toString).map(Thm(goal, _))

  private def reflexive(using library: Library)(left: Expr[?], right: Expr[?], base: Sequent): Either[String, Thm] =
    val goal = Sequent(base.left, base.right + makeEq(left, right))
    K.RestateTrue(using library.theory)(goal.underlying).left.map(_.toString).map(Thm(goal, _))

  private def proveEdge(using library: Library)(step: Step, base: Sequent): Either[String, K.Thm] =
    val (left, right) = step.between
    step match
      case _: ExternalStep =>
        val equality = makeEq(left, right)
        val goal = Sequent(base.left, base.right + equality)
        K.Hypothesis(using library.theory)(goal.underlying, equality.underlying).left.map(_.toString)
      case _: CongruenceStep => proveCongruence(left, right, base)

  private def proveCongruence(using library: Library)(left: Expr[?], right: Expr[?], base: Sequent): Either[String, K.Thm] =
    (left, right) match
      case (Multiapp(leftLabel, leftArgs), Multiapp(rightLabel, rightArgs)) if leftLabel == rightLabel && leftArgs.size == rightArgs.size =>
        val different = leftArgs.zip(rightArgs).filter((l, r) => l != r)
        val freshStart = (left.freeVars ++ right.freeVars).iterator.map(_.id.no).maxOption.getOrElse(-1) + 1
        val variables = different.zipWithIndex.map { case ((source, _), index) =>
          variable(K.Identifier("n", freshStart + index), source.sort)
        }
        val replacements = variables.iterator
        val children = leftArgs.zip(rightArgs).map: (source, target) =>
          if source == target then source else replacements.next()
        val context = makeEq(left, Multiapp.unsafe(rightLabel, children))
        val equalities = different.map((l, r) => makeEq(l, r))
        val reflexiveGoal = Sequent(base.left, base.right + makeEq(left, left))

        for
          childProofs <- different.foldLeft(Right(Vector.empty): Either[String, Vector[(Expr[Prop], K.Thm)]]):
            case (result, (childLeft, childRight)) =>
              for
                accumulated <- result
                proof <- proveExpr(childLeft, childRight.asInstanceOf, base)
              yield accumulated :+ (makeEq(childLeft, childRight) -> proof.kernel)
          reflexive <- K.RestateTrue(using library.theory)(reflexiveGoal.underlying).left.map(_.toString)
          substituted <- K.RightSubstEq(using library.theory)(
            Sequent(base.left ++ equalities, base.right + makeEq(left, right)).underlying,
            reflexive,
            different.map((l, r) => l.underlying -> r.underlying),
            variables.map(_.underlying) -> context.underlying
          ).left.map(_.toString)
          result <- childProofs.foldLeft(Right(substituted): Either[String, K.Thm]):
            case (current, (pivot, childProof)) =>
              current.flatMap: theorem =>
                if base.left.contains(pivot) then Right(theorem)
                else
                  val statement = K.Sequent(theorem.statement.left - pivot.underlying, theorem.statement.right)
                  K.Cut(using library.theory)(statement, childProof, theorem, pivot.underlying).left.map(_.toString)
        yield result
      case _ => Left("Malformed congruence explanation edge.")

  private def compose(using library: Library)(
      start: Expr[?],
      middle: Expr[?],
      end: Expr[?],
      prefix: K.Thm,
      edge: K.Thm,
      base: Sequent
  ): Either[String, K.Thm] =
    val pivot = makeEq(middle, end)
    val chainVariable = variable(K.Identifier("chain", (start.freeVars ++ end.freeVars).iterator.map(_.id.no).maxOption.getOrElse(-1) + 1), middle.sort)
    val context = makeEq(start, chainVariable)
    for
      substituted <- K.RightSubstEq(using library.theory)(
        Sequent(base.left + pivot, base.right + makeEq(start, end)).underlying,
        prefix,
        Seq(middle.underlying -> end.underlying),
        Seq(chainVariable.underlying) -> context.underlying
      ).left.map(_.toString)
      result <- K.Cut(
        using library.theory
      )(Sequent(base.left, base.right + makeEq(start, end)).underlying, edge, substituted, pivot.underlying).left.map(_.toString)
    yield result
