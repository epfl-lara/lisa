package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.ProofHelpers.{PremiseSequentTactic, SequentTactic}

import scala.collection.immutable.HashMap

/** First-order semantic tableau with proof-producing branch reconstruction. */
object Tableau extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  protected def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    Tautology.proveFromPremises(conclusion.underlying, premises.map(_.kernel)): statement =>
      solve(statement).toRight("Could not prove the statement by tableau.")
    match
      case Right(theorem) => ProofJudgement(Thm(conclusion, theorem))
      case Left(message) => ProofCarrier(Set(SoftError(message, file, line)), conclusion, None, ())

  /** Searches for a theorem of a front sequent. */
  def solve(using library: Library)(sequent: Sequent): Option[Thm] =
    solve(sequent.underlying).map(Thm(sequent, _))

  /** Searches for a theorem of a kernel sequent. */
  def solve(using library: Library)(sequent: K.Sequent): Option[K.Thm] =
    val formulas = sequent.left.iterator ++ sequent.right.iterator.map(formula => K.neg(formula))
    val combined = formulas.reduceOption((left, right) => K.and(left)(right)).getOrElse(K.top)
    val taken = combined.allVariables
    val nextId = taken.iterator.map(_.id.no).maxOption.getOrElse(-1) + 1
    val (named, freshId) = makeVariableNamesUnique(combined, nextId, combined.freeVariables)
    val normalForm = K.reducedNNFForm(named)
    val unused = K.Variable(K.Identifier("§", freshId), K.Ind)

    decide(Branch.empty(freshId + 1, unused).prepended(normalForm)).flatMap: proof =>
      K.Weakening(using library.theory)(K.Sequent(Set(normalForm), Set.empty), proof).toOption
        .flatMap(K.Restate(using library.theory)(sequent, _).toOption)

  /** Search state for a left-sided NNF tableau branch. */
  final case class Branch(
      alpha: List[K.Expression],
      beta: List[K.Expression],
      delta: List[K.Expression],
      gamma: List[K.Expression],
      atoms: (List[K.Expression], List[K.Expression]),
      unifiable: Map[K.Variable, (K.Expression, Int)],
      numberInstantiated: Map[K.Variable, Int],
      skolemized: Set[K.Variable],
      triedInstantiation: Map[K.Variable, Set[K.Expression]],
      maxIndex: Int,
      varsOrder: Map[K.Variable, Int],
      unusedVar: K.Variable
  ):
    def prepended(formula: K.Expression): Branch =
      formula match
        case K.and(_, _) => copy(alpha = formula :: alpha)
        case K.or(_, _) => copy(beta = formula :: beta)
        case K.exists(K.Lambda(_, _)) => copy(delta = formula :: delta)
        case K.forall(K.Lambda(_, _)) => copy(gamma = formula :: gamma)
        case K.neg(inner) => copy(atoms = atoms._1 -> (inner :: atoms._2))
        case _ => copy(atoms = (formula :: atoms._1) -> atoms._2)

  object Branch:
    def empty(nextId: Int, unused: K.Variable): Branch =
      Branch(Nil, Nil, Nil, Nil, Nil -> Nil, Map.empty, Map.empty, Set.empty, Map.empty, nextId, Map.empty, unused)

  /** Alpha-renames repeated binders before metavariable generation. */
  def makeVariableNamesUnique(formula: K.Expression, nextId: Int, initiallySeen: Set[K.Variable]): (K.Expression, Int) =
    var fresh = nextId
    var seen = initiallySeen
    def recurse(current: K.Expression): K.Expression =
      current match
        case K.Application(function, argument) => K.Application(recurse(function), recurse(argument))
        case K.Lambda(variable, body) if seen.contains(variable) =>
          val renamed = K.Variable(K.Identifier(variable.id.name, fresh), variable.sort)
          fresh += 1
          K.Lambda(renamed, recurse(K.substituteVariables(body, Map(variable -> renamed))))
        case K.Lambda(variable, body) =>
          seen += variable
          K.Lambda(variable, recurse(body))
        case _ => current
    recurse(formula) -> fresh

  type Substitution = Map[K.Variable, K.Expression]
  val Substitution = HashMap

  /** First-order unification restricted to branch metavariables. */
  def unify(t1: K.Expression, t2: K.Expression, current: Substitution, branch: Branch): Set[Substitution] =
    (t1, t2) match
      case (x: K.Variable, y: K.Variable) if isUnifiable(x, branch) && isUnifiable(y, branch) =>
        if x == y then Set(current)
        else if current.contains(x) then unify(current(x), t2, current, branch)
        else if current.contains(y) then unify(t1, current(y), current, branch)
        else Set(current + (x -> y), current + (y -> x))
      case (x: K.Variable, term) if isUnifiable(x, branch) =>
        val substituted = K.substituteVariables(term, current)
        if substituted.freeVariables.contains(x) then Set.empty
        else current.get(x).fold(Set(current + (x -> substituted)))(unify(_, substituted, current, branch))
      case (term, y: K.Variable) if isUnifiable(y, branch) =>
        val substituted = K.substituteVariables(term, current)
        if substituted.freeVariables.contains(y) then Set.empty
        else current.get(y).fold(Set(current + (y -> substituted)))(unify(substituted, _, current, branch))
      case (K.Application(f1, a1), K.Application(f2, a2)) =>
        unify(f1, f2, current, branch).flatMap(unify(a1, a2, _, branch))
      case _ => if t1 == t2 then Set(current) else Set.empty

  private inline def isUnifiable(variable: K.Variable, branch: Branch): Boolean =
    branch.unifiable.contains(variable) || variable.id.no > branch.maxIndex

  def unifyPred(positive: K.Expression, negative: K.Expression, branch: Branch): Set[Substitution] =
    unify(positive, negative, Substitution.empty, branch)

  /** Finds the cheapest branch-closing unifier and atoms it closes. */
  def close(branch: Branch): Option[(Substitution, Set[K.Expression])] =
    val renamed = branch.atoms._1.iterator
      .flatMap(_.freeVariables)
      .filter(branch.unifiable.contains)
      .map(variable => variable -> K.Variable(K.Identifier(variable.id.name, variable.id.no + branch.maxIndex + 1), K.Ind))
      .toMap
    val inverse = renamed.map(_.swap)
    if branch.atoms._1.contains(K.bot) then return Some(Substitution.empty -> Set(K.bot))

    val candidates = branch.atoms._1.reverseIterator
      .map(K.substituteVariables(_, renamed))
      .flatMap: positive =>
        branch.atoms._2.reverseIterator.flatMap: negative =>
          unifyPred(positive, negative, branch).iterator
            .map(substitution => substitution -> Set(positive, K.neg(negative)))

    val normalized = candidates.map: (substitution, formulas) =>
      val cleaned = substitution.flatMap: (variable, term) =>
        if variable.id.no > branch.maxIndex then
          inverse.get(variable).flatMap: original =>
            if term == original then None
            else Some(original -> K.substituteVariables(term, inverse.view.mapValues(K.substituteVariables(_, substitution)).toMap))
        else if renamed.get(variable).contains(term) then None
        else Some(variable -> K.substituteVariables(term, inverse))
      cleaned -> formulas.map(K.substituteVariables(_, inverse))

    bestSubst(
      normalized.filterNot: (substitution, _) =>
        substitution.exists((variable, term) => branch.triedInstantiation.get(variable).exists(_.contains(term))),
      branch
    )

  def bestSubst(substitutions: Iterator[(Substitution, Set[K.Expression])], branch: Branch): Option[(Substitution, Set[K.Expression])] =
    substitutions.minByOption: (substitution, _) =>
      substitution.size -> substitutionScore(substitution, branch)

  def formulaPenalty(formula: K.Expression, branch: Branch): Int =
    formula match
      case K.and(left, right) => 10 + formulaPenalty(left, branch) + formulaPenalty(right, branch)
      case K.or(left, right) => 40 + formulaPenalty(left, branch) + formulaPenalty(right, branch)
      case K.exists(K.Lambda(_, body)) => 30 + formulaPenalty(body, branch)
      case K.forall(K.Lambda(_, body)) => 200 + formulaPenalty(body, branch)
      case _ => 0

  def substitutionScore(substitution: Substitution, branch: Branch): Int =
    def termPenalty(term: K.Expression): Int =
      term match
        case variable: K.Variable => branch.unifiable.get(variable).fold(0)(_._2)
        case _: K.Constant => 40
        case K.Application(function, argument) => 100 + termPenalty(function) + termPenalty(argument)
        case K.Lambda(_, body) => 100 + termPenalty(body)
    substitution.iterator.map: (variable, term) =>
      val (formula, penalty) = branch.unifiable(variable)
      penalty + branch.numberInstantiated(variable) * 20 + termPenalty(term)
    .sum

  def alpha(branch: Branch): Branch =
    branch.alpha.head match
      case K.and(left, right) => branch.copy(alpha = branch.alpha.tail).prepended(left).prepended(right)

  def beta(branch: Branch): List[(Branch, K.Expression)] =
    branch.beta.head match
      case K.or(left, right) =>
        val rest = branch.copy(beta = branch.beta.tail)
        List(rest.prepended(left) -> left, rest.prepended(right) -> right)

  def delta(branch: Branch): (Branch, K.Variable, K.Expression) =
    branch.delta.head match
      case quantified @ K.exists(K.Lambda(variable, body)) =>
        val fresh = K.Variable(K.Identifier(variable.id.name, branch.maxIndex), K.Ind)
        val instance = K.substituteVariables(body, Map(variable -> fresh))
        (
          branch
            .copy(delta = branch.delta.tail, skolemized = branch.skolemized + variable, maxIndex = branch.maxIndex + 1)
            .prepended(instance),
          fresh,
          instance
        )

  def gamma(branch: Branch): (Branch, K.Variable, K.Expression) =
    branch.gamma.head match
      case quantified @ K.forall(K.Lambda(variable, body)) =>
        val (instance, metavariable) =
          if branch.unifiable.contains(variable) then
            val fresh = K.Variable(K.Identifier(variable.id.name, branch.maxIndex), K.Ind)
            K.substituteVariables(body, Map(variable -> fresh)) -> fresh
          else body -> variable
        val next = branch.copy(
          gamma = branch.gamma.tail,
          unifiable = branch.unifiable + (metavariable -> (quantified -> formulaPenalty(body, branch))),
          numberInstantiated = branch.numberInstantiated + (metavariable -> branch.numberInstantiated.getOrElse(variable, 0)),
          maxIndex = branch.maxIndex + 1,
          varsOrder = branch.varsOrder + (metavariable -> branch.varsOrder.size)
        )
        (next.prepended(instance), metavariable, instance)

  def applyInst(branch: Branch, variable: K.Variable, term: K.Expression): (Branch, K.Expression) =
    val quantified = branch.unifiable(variable)._1
    val tried = branch.triedInstantiation.updated(variable, branch.triedInstantiation.getOrElse(variable, Set.empty) + term)
    quantified match
      case K.forall(K.Lambda(bound, body)) =>
        val instance = instantiate(body, bound, term)
        branch
          .prepended(instance)
          .copy(
            triedInstantiation = tried,
            numberInstantiated = branch.numberInstantiated.updated(variable, branch.numberInstantiated(variable) + 1)
          ) -> instance

  /** Main tableau search, returning the theorem for the used branch subset. */
  def decide(using library: Library)(branch: Branch): Option[K.Thm] =
    val closing = close(branch)
    if closing.exists(_._1.isEmpty) then
      K.RestateTrue(using library.theory)(K.Sequent(closing.get._2, Set.empty)).toOption
    else if branch.alpha.nonEmpty then
      decide(alpha(branch)).flatMap: proof =>
        branch.alpha.head match
          case conjunction @ K.and(left, right) if proof.statement.left.contains(left) || proof.statement.left.contains(right) =>
            val statement = K.Sequent((proof.statement.left - left - right) + conjunction, proof.statement.right)
            K.Weakening(using library.theory)(statement, proof).toOption
          case _ => Some(proof)
    else if branch.delta.nonEmpty then
      val (next, fresh, instance) = delta(branch)
      decide(next).flatMap: proof =>
        if proof.statement.left.contains(instance) then
          val statement = K.Sequent((proof.statement.left - instance) + branch.delta.head, proof.statement.right)
          K.LeftExists(using library.theory)(statement, proof, instance, fresh).toOption
        else Some(proof)
    else if branch.beta.nonEmpty then
      val branches = beta(branch)
      val proofs = Vector.newBuilder[K.Thm]
      val iterator = branches.iterator
      while iterator.hasNext do
        val (next, disjunct) = iterator.next()
        decide(next) match
          case None => return None
          case Some(proof) if !proof.statement.left.contains(disjunct) => return Some(proof)
          case Some(proof) => proofs += proof
      val result = proofs.result()
      val left = result.iterator.zip(branches.iterator).flatMap((proof, branch) => proof.statement.left - branch._2).toSet + branch.beta.head
      branch.beta.head match
        case K.or(first, second) =>
          K.LeftOr(using library.theory)(K.Sequent(left, Set.empty), result, Seq(first, second)).toOption
    else if branch.gamma.nonEmpty then
      val (next, metavariable, instance) = gamma(branch)
      decide(next).flatMap: proof =>
        if proof.statement.left.contains(instance) then
          branch.gamma.head match
            case K.forall(K.Lambda(variable, body)) =>
              val statement = K.Sequent((proof.statement.left - instance) + branch.gamma.head, proof.statement.right)
              K.LeftForall(using library.theory)(statement, proof, body, variable, metavariable).toOption
        else Some(proof)
    else if closing.exists(_._1.nonEmpty) then
      val (variable, term) = closing.get._1.minBy((variable, _) => branch.varsOrder(variable))
      val (next, instance) = applyInst(branch, variable, term)
      decide(next).flatMap: proof =>
        if proof.statement.left.contains(instance) then
          branch.unifiable(variable)._1 match
            case quantified @ K.forall(K.Lambda(bound, body)) =>
              val statement = K.Sequent((proof.statement.left - instance) + quantified, proof.statement.right)
              K.LeftForall(using library.theory)(statement, proof, body, bound, term).toOption
        else Some(proof)
    else None

  def instantiate(formula: K.Expression, variable: K.Variable, term: K.Expression): K.Expression =
    K.substituteVariables(formula, Map(variable -> term))
