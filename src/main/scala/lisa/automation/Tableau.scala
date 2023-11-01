package lisa.automation
import lisa.fol.FOL as F
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.*
import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.utils.parsing.FOLPrinter.prettyFormula
import lisa.utils.parsing.FOLPrinter.prettySCProof
import lisa.utils.parsing.FOLPrinter.prettyTerm

import scala.collection.immutable.HashMap
import scala.collection.immutable.HashSet

/**
 * Now need to deal with variables unifying with terms containing themselves
 * optimiye list siye computation
 * Then, optimize unification check by not checking all pairs all the time
 * Then, shortcut branches by checking if they are OL-true or OL-false
 *
 * Next test: No quantifiers but actual terms with variables
 */

object Tableau extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic {

  def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
    solve(bot) match {
      case Some(value) => proof.ValidProofTactic(bot, value.steps, Seq())
      case None => proof.InvalidProofTactic("Could not prove the statement.")
    }
  }

  /**
   * Given a targeted conclusion sequent, try to prove it using laws of propositional logic and reflexivity and symmetry of equality.
   * Uses the given already proven facts as assumptions to reach the desired goal.
   *
   * @param proof The ongoing proof object in which the step happens.
   * @param premise A previously proven step necessary to reach the conclusion.
   * @param bot   The desired conclusion.
   */
  def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
    from(using lib, proof)(Seq(premise)*)(bot)

  def from(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
    val botK = bot.underlying
    val premsFormulas: Seq[((proof.Fact, Formula), Int)] = premises.map(p => (p, sequentToFormula(proof.getSequent(p).underlying))).zipWithIndex
    val initProof = premsFormulas.map(s => Restate(() |- s._1._2, -(1 + s._2))).toList
    val sqToProve = botK ++<< (premsFormulas.map(s => s._1._2).toSet |- ())

    solve(sqToProve) match {
      case Some(value) =>
        val subpr = SCSubproof(value)
        val stepsList = premsFormulas.foldLeft[List[SCProofStep]](List(subpr))((prev: List[SCProofStep], cur) => {
          val ((prem, form), position) = cur
          if contains(prev.head.bot.left, form) then
            Cut(prev.head.bot -<< form, position, initProof.length + prev.length - 1, form) :: prev
          else prev
        })
        val steps = (initProof ++ stepsList.reverse).toIndexedSeq
        proof.ValidProofTactic(bot, steps, premises)
      case None =>
        proof.InvalidProofTactic("Could not prove the statement.")
    }
  }

  inline def solve(sequent: F.Sequent): Option[SCProof] = solve(sequent.underlying)

  def solve(sequent: K.Sequent): Option[SCProof] = {
    val f = K.ConnectorFormula(K.And, (sequent.left.toSeq ++ sequent.right.map(f => K.ConnectorFormula(K.Neg, List(f)))))
    val taken = f.schematicTermLabels
    val nextIdNow = if taken.isEmpty then 0 else taken.maxBy(_.id.no).id.no + 1
    val (fnamed, nextId, _) = makeVariableNamesUnique(f, nextIdNow, f.freeVariables)
    val nf = reducedNNFForm(fnamed)
    val proof = decide(Branch.empty.prepended(nf))

    proof match
      case None => None
      case Some((p, _)) => Some(SCProof((Restate(sequent, p.length) :: Weakening(nf |- (), p.length - 1) :: p).reverse.toIndexedSeq, IndexedSeq.empty))

  }

  /**
   * A branch represent a sequent (whose right hand side is empty) that is being proved.
   * It is assumed that the sequent is in negation normal form, negations are only applied to atoms.
   * Formulas are sorted according to their shape :
   * Conjunctions are in alpha
   * Disjunctions are in beta
   * Existential quantifiers are in delta
   * Universal quantifiers are in gamma
   * Atoms are in atoms (split into positive and negative)
   * At each step of the procedure, a formula is deconstructed in accordance with the rules of the tableau calculus.
   * Then that formula is removed from the branch as it is no longer needed.
   * Variables coming from universal quantifiers are marked as suitable for unification in unifiable
   * Instantiations that have been done already are stored in triedInstantiation, to avoid infinite loops.
   * When a quantifier Q1 is below a universal quantifier Q2, Q2 can be instantiated multiple times.
   * Then, Q1 may also need to be instantiated multiple versions, requiring fresh variable names.
   * maxIndex stores an index that is used to generate fresh variable names.
   */
  case class Branch(
      alpha: List[ConnectorFormula], // label = And
      beta: List[ConnectorFormula], // label = Or
      delta: List[BinderFormula], // Exists(...))
      gamma: List[BinderFormula], // Forall(...)
      atoms: (List[PredicateFormula], List[PredicateFormula]), // split into positive and negatives!
      unifiable: Map[VariableLabel, BinderFormula], // map between metavariables and the original formula they came from
      skolemized: Set[VariableLabel], // set of variables that have been skolemized
      triedInstantiation: Map[VariableLabel, Set[Term]], // map between metavariables and the term they were already instantiated with
      maxIndex: Int // the maximum index used for skolemization and metavariables
  ) {
    def pop(f: Formula): Branch = f match
      case f @ ConnectorFormula(Or, args) =>
        if (beta.nonEmpty && beta.head.uniqueNumber == f.uniqueNumber) copy(beta = beta.tail) else throw Exception("First formula of beta is not f")
      case f @ BinderFormula(Exists, x, inner) =>
        if (delta.nonEmpty && delta.head.uniqueNumber == f.uniqueNumber) copy(delta = delta.tail) else throw Exception("First formula of delta is not f")
      case f @ BinderFormula(Forall, x, inner) =>
        if (gamma.nonEmpty && gamma.head.uniqueNumber == f.uniqueNumber) copy(gamma = gamma.tail) else throw Exception("First formula of gamma is not f")
      case ConnectorFormula(And, args) =>
        if (alpha.nonEmpty && alpha.head.uniqueNumber == f.uniqueNumber) copy(alpha = alpha.tail) else throw Exception("First formula of alpha is not f")
      case f @ PredicateFormula(id, args) =>
        throw Exception("Should not pop Atoms")
      case f @ ConnectorFormula(Neg, List(PredicateFormula(id, args))) =>
        throw Exception("Should not pop Atoms")
      case _ => ???

    def prepended(f: Formula): Branch = f match
      case f @ ConnectorFormula(And, args) => this.copy(alpha = f :: alpha)
      case f @ ConnectorFormula(Or, args) => this.copy(beta = f :: beta)
      case f @ BinderFormula(Exists, x, inner) => this.copy(delta = f :: delta)
      case f @ BinderFormula(Forall, x, inner) => this.copy(gamma = f :: gamma)
      case f @ PredicateFormula(id, args) =>
        this.copy(atoms = (f :: atoms._1, atoms._2))
      case ConnectorFormula(Neg, List(f @ PredicateFormula(id, args))) =>
        this.copy(atoms = (atoms._1, f :: atoms._2))
      case _ => ???

    def prependedAll(l: Seq[Formula]): Branch = l.foldLeft(this)((a, b) => a.prepended(b))

    def asSequent: Sequent = (beta ++ delta ++ gamma ++ atoms._1 ++ atoms._2.map(a => !a)).toSet |- Set() // inefficient, not used

    import Branch.*
    override def toString(): String =
      val pretUnif = unifiable.map((x, f) => x.id + " -> " + prettyFormula(f)).mkString("Unif(", ", ", ")")
      // val pretTried = triedInstantiation.map((x, t) => x.id + " -> " + prettyTerm(t, true)).mkString("Tried(", ", ", ")")
      s"Branch(${prettyIte(beta, "beta")}, ${prettyIte(delta, "delta")}, ${prettyIte(gamma, "gamma")}, ${prettyIte(atoms._1, "+")}, ${prettyIte(atoms._2, "-")}, $pretUnif, _, _)"

  }
  object Branch {
    def empty = Branch(Nil, Nil, Nil, Nil, (Nil, Nil), Map.empty, Set.empty, Map.empty, 1)
    def empty(n: Int) = Branch(Nil, Nil, Nil, Nil, (Nil, Nil), Map.empty, Set.empty, Map.empty, n)
    def prettyIte(l: Iterable[Formula], head: String): String = l match
      case Nil => "Nil"
      case _ => l.map(prettyFormula(_, true)).mkString(head + "(", ", ", ")")

  }

  def makeVariableNamesUnique(f: Formula, nextId: Int, seen: Set[VariableLabel]): (Formula, Int, Set[VariableLabel]) = f match
    case ConnectorFormula(label, args) =>
      val (nArgs, nnId, nSeen) = args.foldLeft((List(): Seq[Formula], nextId, seen))((prev, next) =>
        val (l, n, s) = prev
        val (nf, nn, ns) = makeVariableNamesUnique(next, n, s)
        (l :+ nf, nn, ns)
      )
      (ConnectorFormula(label, nArgs), nnId, nSeen)
    case pf: PredicateFormula => (pf, nextId, seen)
    case BinderFormula(label, x, inner) =>
      if (seen.contains(x))
        val (nInner, nnId, nSeen) = makeVariableNamesUnique(inner, nextId + 1, seen)
        val newX = VariableLabel(Identifier(x.id, nextId))
        (BinderFormula(label, newX, substituteVariablesInFormula(nInner, Map(x -> newX), Seq())), nnId, nSeen)
      else
        val (nInner, nnId, nSeen) = makeVariableNamesUnique(inner, nextId, seen + x)
        (BinderFormula(label, x, nInner), nnId, nSeen)

  type Substitution = Map[VariableLabel, Term]
  val Substitution = HashMap

  /**
   * Detect if two terms can be unified, and if so, return a substitution that unifies them.
   */
  def unify(t1: Term, t2: Term, current: Substitution, br: Branch): Option[Substitution] = (t1, t2) match
    case (VariableTerm(x), VariableTerm(y)) if br.unifiable.contains(x) && br.unifiable.contains(y) =>
      if (x == y) Some(current) else Some(current + (x -> substituteVariablesInTerm(t2, current)))
    case (VariableTerm(x), t2: Term) if br.unifiable.contains(x) =>
      if t2.freeVariables.contains(x) then None
      else if (current.contains(x)) unify(current(x), t2, current, br)
      else Some(current + (x -> substituteVariablesInTerm(t2, current)))
    case (t1: Term, VariableTerm(y)) if br.unifiable.contains(y) =>
      if t1.freeVariables.contains(y) then None
      else if (current.contains(y)) unify(t1, current(y), current, br)
      else Some(current + (y -> substituteVariablesInTerm(t1, current)))
    case (Term(label1, args1), Term(label2, args2)) =>
      if label1 == label2 && args1.size == args2.size then
        args1
          .zip(args2)
          .foldLeft(Some(current): Option[Substitution])((prev, next) =>
            prev match
              case None => None
              case Some(s) => unify(next._1, next._2, s, br)
          )
      else None

  /**
   * Detect if two atoms can be unified, and if so, return a substitution that unifies them.
   */
  def unifyPred(pos: PredicateFormula, neg: PredicateFormula, br: Branch): Option[Substitution] = {
    (pos, neg) match
      case (PredicateFormula(id1, args1), PredicateFormula(id2, args2)) if (id1 == id2 && args1.size == args2.size) =>
        args1
          .zip(args2)
          .foldLeft(Some(Substitution.empty): Option[Substitution])((prev, next) =>
            prev match
              case None => None
              case Some(s) => unify(next._1, next._2, s, br)
          )
      case _ => None

  }

  /**
   * Detect if a branch can be closed, and if so, return a list of substitutions that closes it along with the formulas used to close it
   * If it can't be closed, returns None
   * The substitution cannot do substitutions that were already done in branch.triedInstantiation.
   * When multiple substitutions are possible, the one with the smallest size is returned. (Maybe there is a better heuristic, like distance from the root?)
   */
  def close(branch: Branch): Option[(Substitution, Set[Formula])] = {
    val pos = branch.atoms._1.iterator
    var substitutions: List[(Substitution, Set[Formula])] = Nil

    while (pos.hasNext) {
      val p = pos.next()
      if (p.label == bot) return Some((Substitution.empty, Set(bot)))
      val neg = branch.atoms._2.iterator
      while (neg.hasNext) {
        val n = neg.next()
        unifyPred(p, n, branch) match
          case None => ()
          case Some(unif) => substitutions = (unif, Set(p, !n)) :: substitutions
      }
    }
    val cr = substitutions.filterNot(s =>
      s._1.exists((x, t) =>
        val v = branch.triedInstantiation.contains(x) && branch.triedInstantiation(x).contains(t)
        v
      )
    )
    cr.sortBy(_._1.size).headOption
  }

  /**
   * Explodes one And formula
   * The alpha list of the branch must not be empty
   */
  def alpha(branch: Branch): Branch = {
    val f = branch.alpha.head
    branch.copy(alpha = branch.alpha.tail).prependedAll(f.args)
  }

  /**
   * Explodes one Or formula, and alpha-simplifies it
   * Add the exploded formula to the used list, if one beta formula is found
   * The beta list of the branch must not be empty
   */
  def beta(branch: Branch): List[(Branch, Formula)] = {
    val f = branch.beta.head
    val b1 = branch.copy(beta = branch.beta.tail)
    val resList = f.args.toList.map(disjunct => {
      ((b1.prepended(disjunct), disjunct))
    })
    resList
  }

  /**
   * Explodes one Exists formula
   * Add the unquantified formula to the branch
   * Since the bound variable is not marked as suitable for instantiation, it behaves as a constant symbol (skolem)
   */
  def delta(branch: Branch): (Branch, VariableLabel, Formula) = {
    val f = branch.delta.head
    if branch.skolemized.contains(branch.delta.head.bound) then
      val newX = VariableLabel(Identifier(f.bound.id.name, branch.maxIndex))
      val newInner = substituteVariablesInFormula(f.inner, Map(f.bound -> newX), Seq())
      (branch.copy(delta = branch.delta.tail, maxIndex = branch.maxIndex + 1).prepended(newInner), newX, newInner)
    else (branch.copy(delta = branch.delta.tail, skolemized = branch.skolemized + f.bound).prepended(f.inner), f.bound, f.inner)
  }

  /**
   * Explodes one Forall formula
   * Add the unquantified formula to the branch and mark the bound variable as suitable for unification
   * This step will most of the time be cancelled when building the proof, unless any arbitrary instantiation is sufficient to get a proof.
   */
  def gamma(branch: Branch): (Branch, VariableLabel, Formula) = {
    val f = branch.gamma.head
    val (ni, nb) = branch.unifiable.get(f.bound) match
      case None =>
        (f.inner, f.bound)
      case Some(value) =>
        val newBound = VariableLabel(Identifier(f.bound.id.name, branch.maxIndex))
        val newInner = substituteVariablesInFormula(f.inner, Map(f.bound -> newBound), Seq())
        (newInner, newBound)
    val b1 = branch.copy(gamma = branch.gamma.tail, unifiable = branch.unifiable + (nb -> f), maxIndex = branch.maxIndex + 1)
    (b1.prepended(ni), nb, ni)
  }

  /**
   * When a closing unification has been found, apply it to the branch
   * This does not backtracking: The metavariable remains available if it needs further instantiation.
   */
  def applyInst(branch: Branch, x: VariableLabel, t: Term): (Branch, Formula) = {
    val f = branch.unifiable(x)
    val newTried = branch.triedInstantiation.get(x) match
      case None => branch.triedInstantiation + (x -> Set(t))
      case Some(s) => branch.triedInstantiation + (x -> (s + t))

    val inst = instantiate(f.inner, f.bound, t)
    val r = branch.prepended(inst).copy(triedInstantiation = newTried)
    (r, inst)
  }

  /**
   * Decide if a branch can be closed, and if not, explode it.
   * Main routine of the decision procedure. If it succeeds, return a proof of the branch.
   * Note that the proof actually proves a subset of a branch when possible, to cut short on unneeded steps and formulas.
   * The return integer is the size of the proof: Used to avoid computing the size every time in linear time.
   */
  def decide(branch: Branch): Option[(List[SCProofStep], Int)] = {
    val closeSubst = close(branch)
    if (closeSubst.nonEmpty && closeSubst.get._1.isEmpty) // If branch can be closed without Instantiation (Hyp)
      Some((List(RestateTrue(Sequent(closeSubst.get._2, Set()))), 0))
    else if (branch.alpha.nonEmpty) // If branch contains an Alpha formula (LeftAnd)
      val rec = alpha(branch)
      decide(rec).map((proof, step) =>
        if branch.alpha.head.args.exists(proof.head.bot.left.contains) then
          val sequent = proof.head.bot.copy(left = (proof.head.bot.left -- branch.alpha.head.args) + branch.alpha.head)
          (Weakening(sequent, proof.size - 1) :: proof, step + 1)
        else (proof, step)
      )
    else if (branch.delta.nonEmpty) // If branch contains a Delta formula (LeftExists)
      val rec = delta(branch)
      val upperProof = decide(rec._1)
      upperProof.map((proof, step) =>
        if proof.head.bot.left.contains(rec._3) then
          val sequent = (proof.head.bot -<< rec._3) +<< branch.delta.head
          (LeftExists(sequent, step, rec._3, rec._2) :: proof, step + 1)
        else (proof, step)
      )
    else if (branch.beta.nonEmpty) // If branch contains a Beta formula (LeftOr)
      val list = beta(branch)
      val (proof, treversed, needed) = list.foldLeft((Some(Nil): Option[List[SCProofStep]], Nil: List[Int], true: Boolean))((prev, next) =>
        prev match
          case (None, _, _) => prev // proof failed
          case (_, _, false) =>
            prev // proof succeded early
          case (Some(prevProof), t, true) =>
            val res = decide(next._1)
            res match
              case None => (None, t, true)
              case Some((nextProof, step)) =>
                if nextProof.head.bot.left.contains(next._2) then // If the disjunct was used, encapsulate the subbranch in a Subproof
                  val subproofDisj =
                    if nextProof.size == 1 then nextProof.head
                    else SCSubproof(SCProof(nextProof.toIndexedSeq.reverse, IndexedSeq.empty), IndexedSeq.empty)
                  (Some(subproofDisj :: prevProof), prevProof.size :: t, true)
                else
                  // If the disjunct was not used, then the subbranch is a proof of the whole statement and the split is not necessary.
                  (res.map(_._1), List(nextProof.size - 1), false)
      )
      proof.map(proo =>
        if needed == true then
          val sequent = ((proo.reverse.zip(list).flatMap((proof, bf) => proof.bot.left - bf._2).toSet + branch.beta.head) |- ())
          (LeftOr(sequent, treversed.reverse, branch.beta.head.args) :: proo, treversed.size)
        else (proo, proo.size - 1)
      )
    else if (branch.gamma.nonEmpty) // If branch contains a Gamma formula (LeftForall)
      val rec = gamma(branch)
      val upperProof = decide(rec._1)
      // LeftForall(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel, t: Term)
      upperProof.map((proof, step) =>
        if proof.head.bot.left.contains(rec._3) then
          val sequent = (proof.head.bot -<< rec._3) +<< branch.gamma.head
          (LeftForall(sequent, step, branch.gamma.head.inner, branch.gamma.head.bound, rec._2()) :: proof, step + 1)
        else (proof, step)
      )
    else if (closeSubst.nonEmpty && closeSubst.get._1.nonEmpty) // If branch can be closed with Instantiation (LeftForall)
      val (x, t) = closeSubst.get._1.head
      val (recBranch, instantiated) = applyInst(branch, x, t)
      val upperProof = decide(recBranch)
      upperProof.map((proof, step) =>
        if proof.head.bot.left.contains(instantiated) then
          val sequent = (proof.head.bot -<< instantiated) +<< branch.unifiable(x)
          (LeftForall(sequent, step, branch.unifiable(x).inner, branch.unifiable(x).bound, t) :: proof, step + 1)
        else (proof, step)
      )
    else None
    // End of decide
  }

  def containsAlpha(set: Set[Formula], f: Formula) = f match {
    case ConnectorFormula(And, args) => args.exists(set.contains)
    case _ => set.contains(f)
  }

  def instantiate(f: Formula, x: VariableLabel, t: Term): Formula = f match
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiate(_, x, t)))
    case PredicateFormula(id, args) => PredicateFormula(id, args.map(substituteVariablesInTerm(_, Substitution(x -> t))))
    case BinderFormula(label, y, inner) => if (x == y) f else BinderFormula(label, y, instantiate(inner, x, t))
}
