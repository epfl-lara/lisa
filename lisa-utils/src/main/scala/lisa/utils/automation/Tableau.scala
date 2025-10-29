package lisa.automation
import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.OutputManager._
import lisa.utils.prooflib.ProofTacticLib._

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

  var debug = true
  def pr(s: Object) = if debug then println(s)

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
    val premsFormulas: Seq[((proof.Fact, Expression), Int)] = premises.map(p => (p, sequentToFormula(proof.getSequent(p).underlying))).zipWithIndex
    val initProof = premsFormulas.map(s => Restate(() |- s._1._2, -(1 + s._2))).toList
    val sqToProve = botK ++<< (premsFormulas.map(s => s._1._2).toSet |- ())

    solve(sqToProve) match {
      case Some(value) =>
        val subpr = SCSubproof(value)
        val stepsList = premsFormulas.foldLeft[List[SCProofStep]](List(subpr))((prev: List[SCProofStep], cur) => {
          val ((prem, form), position) = cur
          Cut(prev.head.bot -<< form, position, initProof.length + prev.length - 1, form) :: prev
        })
        val steps = (initProof ++ stepsList.reverse).toIndexedSeq
        proof.ValidProofTactic(bot, steps, premises)
      case None =>
        proof.InvalidProofTactic("Could not prove the statement.")
    }
  }

  /*
  def from(premises: Seq[K.Sequent], bot: K.Sequent): Option[SCProof] = {
    val botK = bot.underlying
    val premsFormulas: Seq[((proof.Fact, Expression), Int)] = premises.map(p => (p, sequentToFormula(proof.getSequent(p).underlying))).zipWithIndex
    val initProof = premsFormulas.map(s => Restate(() |- s._1._2, -(1 + s._2))).toList
    val sqToProve = botK ++<< (premsFormulas.map(s => s._1._2).toSet |- ())

    solve(sqToProve) match {
      case Some(value) =>
        val subpr = SCSubproof(value)
        val stepsList = premsFormulas.foldLeft[List[SCProofStep]](List(subpr))((prev: List[SCProofStep], cur) => {
          val ((prem, form), position) = cur
          Cut(prev.head.bot -<< form, position, initProof.length + prev.length - 1, form) :: prev
        })
        val steps = (initProof ++ stepsList.reverse).toIndexedSeq
        proof.ValidProofTactic(bot, steps, premises)
      case None =>
        proof.InvalidProofTactic("Could not prove the statement.")
    }
  }*/

  inline def solve(sequent: F.Sequent): Option[SCProof] = solve(sequent.underlying)

  def solve(sequent: K.Sequent): Option[SCProof] = {
    val f = K.multiand(sequent.left.toSeq ++ sequent.right.map(f => K.neg(f)))
    val taken = f.allVariables
    val nextIdNow = if taken.isEmpty then 0 else taken.maxBy(_.id.no).id.no + 1
    val (fnamed, nextId) = makeVariableNamesUnique(f, nextIdNow, f.freeVariables)
    val nf = reducedNNFForm(fnamed)
    val uv = Variable(Identifier("§", nextId), Ind)
    val proof = decide(Branch.empty(nextId + 1, uv).prepended(nf))
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
      alpha: List[Expression], // label = And
      beta: List[Expression], // label = Or
      delta: List[Expression], // Exists(...))
      gamma: List[Expression], // Forall(...)
      atoms: (List[Expression], List[Expression]), // split into positive and negatives!
      unifiable: Map[Variable, (Expression, Int)], // map between metavariables and the original formula they came from, with the penalty associated to the complexity of the formula.
      numberInstantiated: Map[Variable, Int], // map between variables and the number of times they have been instantiated

      skolemized: Set[Variable], // set of variables that have been skolemized
      triedInstantiation: Map[Variable, Set[Expression]], // map between metavariables and the term they were already instantiated with
      maxIndex: Int, // the maximum index used for skolemization and metavariables
      varsOrder: Map[Variable, Int], // the order in which variables were instantiated. In particular, if the branch contained the formula ∀x. ∀y. ... then x > y.
      unusedVar: Variable // a variable the is neither free nor bound in the original formula.
  ) {
    def pop(f: Expression): Branch = f match
      case f @ Or(l, r) =>
        if (beta.nonEmpty && beta.head.uniqueNumber == f.uniqueNumber) copy(beta = beta.tail) else throw Exception("First formula of beta is not f")
      case f @ Exists(x, inner) =>
        if (delta.nonEmpty && delta.head.uniqueNumber == f.uniqueNumber) copy(delta = delta.tail) else throw Exception("First formula of delta is not f")
      case f @ Forall(x, inner) =>
        if (gamma.nonEmpty && gamma.head.uniqueNumber == f.uniqueNumber) copy(gamma = gamma.tail) else throw Exception("First formula of gamma is not f")
      case And(left, right) =>
        if (alpha.nonEmpty && alpha.head.uniqueNumber == f.uniqueNumber) copy(alpha = alpha.tail) else throw Exception("First formula of alpha is not f")
      case _ =>
        throw Exception("Should not pop Atoms: " + f.repr)

    def prepended(f: Expression): Branch = f match
      case And(left, right) => this.copy(alpha = f :: alpha)
      case Or(left, right) => this.copy(beta = f :: beta)
      case Exists(x, inner) => this.copy(delta = f :: delta)
      case Forall(x, inner) => this.copy(gamma = f :: gamma)
      case Neg(f) =>
        this.copy(atoms = (atoms._1, f :: atoms._2))
      case _ =>
        this.copy(atoms = (f :: atoms._1, atoms._2))

    def prependedAll(l: Seq[Expression]): Branch = l.foldLeft(this)((a, b) => a.prepended(b))

    def asSequent: Sequent = (beta ++ delta ++ gamma ++ atoms._1 ++ atoms._2.map(a => !a)).toSet |- Set() // inefficient, not used

    import Branch.*
    override def toString(): String =
      val pretUnif = unifiable.map((x, f) => x.id + " -> " + f._1.repr + " : " + f._2).mkString("Unif(", ", ", ")")
      // val pretTried = triedInstantiation.map((x, t) => x.id + " -> " + prettyTerm(t, true)).mkString("Tried(", ", ", ")")
      (s"Branch(" +
        s"${RED(prettyIte(alpha, "alpha"))}, " +
        s"${GREEN(prettyIte(beta, "beta"))}, " +
        s"${BLUE(prettyIte(delta, "delta"))}, " +
        s"${YELLOW(prettyIte(gamma, "gamma"))}, " +
        s"${MAGENTA(prettyIte(atoms._1, "+"))}, ${CYAN(prettyIte(atoms._2, "-"))}, " +
        s"$pretUnif, _, _)").split("'").mkString("").split("_").mkString("")

  }
  object Branch {
    def empty = Branch(Nil, Nil, Nil, Nil, (Nil, Nil), Map.empty, Map.empty, Set.empty, Map.empty, 1, Map.empty, Variable(Identifier("§uv", 0), Ind))
    def empty(n: Int, uv: Variable) = Branch(Nil, Nil, Nil, Nil, (Nil, Nil), Map.empty, Map.empty, Set.empty, Map.empty, n, Map.empty, uv)
    def prettyIte(l: Iterable[Expression], head: String): String = l match
      case Nil => "Nil"
      case _ => l.map(_.repr).mkString(head + "(", ", ", ")")

  }

  def makeVariableNamesUnique(f: Expression, nextId: Int, seen2: Set[Variable]): (Expression, Int) = {
    var nextId2: Int = nextId
    var seen = seen2
    def recurse(f: Expression): Expression = f match
      case Application(f, a) =>
        Application(recurse(f), recurse(a))
      case Lambda(v, body) =>
        if seen.contains(v) then
          val newV = Variable(Identifier(v.id, nextId2), Ind)
          nextId2 += 1
          Lambda(newV, substituteVariables(recurse(body), Map(v -> newV)))
        else
          seen += v
          Lambda(v, recurse(body))
      case _ => f
    (recurse(f), nextId2)
  }
  type Substitution = Map[Variable, Expression]
  val Substitution = HashMap
  def prettySubst(s: Substitution): String = s.map((x, t) => x.id + " -> " + t.repr).mkString("Subst(", ", ", ")")

  /**
   * Detect if two terms can be unified, and if so, return a substitution that unifies them.
   */
  def unify(t1: Expression, t2: Expression, current: Substitution, br: Branch): Option[Substitution] = (t1, t2) match
    case (x: Variable, y: Variable) if (br.unifiable.contains(x) || x.id.no > br.maxIndex) && (br.unifiable.contains(y) || y.id.no > br.maxIndex) =>
      if x == y then Some(current)
      else if current.contains(x) then unify(current(x), t2, current, br)
      else if current.contains(y) then unify(t1, current(y), current, br)
      else Some(current + (x -> y))
    case (x: Variable, t2: Expression) if br.unifiable.contains(x) || x.id.no > br.maxIndex =>
      val newt2 = substituteVariables(t2, current)
      if newt2.freeVariables.contains(x) then None
      else if (current.contains(x)) unify(current(x), newt2, current, br)
      else Some(current + (x -> newt2))
    case (t1: Expression, y: Variable) if br.unifiable.contains(y) || y.id.no > br.maxIndex =>
      val newt1 = substituteVariables(t1, current)
      if newt1.freeVariables.contains(y) then None
      else if (current.contains(y)) unify(newt1, current(y), current, br)
      else Some(current + (y -> newt1))
    case (Application(f1, a1), Application(f2, a2)) =>
      unify(f1, f2, current, br).flatMap(s => unify(a1, a2, s, br))
    case _ => if t1 == t2 then Some(current) else None

  /**
   * Detect if two atoms can be unified, and if so, return a substitution that unifies them.
   */
  def unifyPred(pos: Expression, neg: Expression, br: Branch): Option[Substitution] = {
    assert(pos.sort == Prop && neg.sort == Prop)
    unify(pos, neg, Substitution.empty, br)

  }

  /**
   * Detect if a branch can be closed, and if so, return a list of substitutions that closes it along with the formulas used to close it
   * If it can't be closed, returns None
   * The substitution cannot do substitutions that were already done in branch.triedInstantiation.
   * When multiple substitutions are possible, the one with the smallest size is returned. (Maybe there is a better heuristic, like distance from the root?)
   */
  def close(branch: Branch): Option[(Substitution, Set[Expression])] = {
    val newMap = branch.atoms._1
      .flatMap(pred => pred.freeVariables.filter(v => branch.unifiable.contains(v)))
      .map(v => v -> Variable(Identifier(v.id.name, v.id.no + branch.maxIndex + 1), Ind))
      .toMap
    val inverseNewMap = newMap.map((k, v) => v -> k).toMap
    val pos = branch.atoms._1.map(pred => substituteVariables(pred, newMap)).iterator
    var substitutions: List[(Substitution, Set[Expression])] = Nil

    while (pos.hasNext) {
      val p = pos.next()
      if (p == bot) return Some((Substitution.empty, Set(bot)))
      val neg = branch.atoms._2.iterator
      while (neg.hasNext) {
        val n = neg.next()
        unifyPred(p, n, branch) match
          case None => ()
          case Some(unif) =>
            substitutions = (unif, Set(p, !n)) :: substitutions
      }
    }

    val cr1 = substitutions.map((sub, set) =>
      (
        sub.flatMap((v, t) =>
          if v.id.no > branch.maxIndex then
            if t == inverseNewMap(v) then None
            else Some(inverseNewMap(v) -> substituteVariables(t, inverseNewMap.map((v, t) => v -> substituteVariables(t, sub))))
          else if newMap.contains(v) && t == newMap(v) then None
          else Some(v -> substituteVariables(t, inverseNewMap))
        ),
        set.map(f => substituteVariables(f, inverseNewMap))
      )
    )

    val cr = cr1.filterNot(s =>
      s._1.exists((x, t) =>
        val v = branch.triedInstantiation.contains(x) && branch.triedInstantiation(x).contains(t)
        v
      )
    )

    bestSubst(cr, branch)

  }

  def bestSubst(substs: List[(Substitution, Set[Expression])], branch: Branch): Option[(Substitution, Set[Expression])] = {
    if substs.isEmpty then return None
    val minSize = substs.minBy(_._1.size)
    val smallSubst = substs.filter(_._1.size == minSize._1.size)
    // Up to this, it is necessary for completeness. From this, it is heuristic.

    val best = smallSubst.minBy(s => substitutionScore(s._1, branch))
    Some(best)
  }
  def formulaPenalty(f: Expression, branch: Branch): Int = f match
    case And(left, right) => 10 + formulaPenalty(left, branch) + formulaPenalty(right, branch)
    case Or(left, right) => 40 + formulaPenalty(left, branch) + formulaPenalty(right, branch)
    case Exists(x, inner) => 30 + formulaPenalty(inner, branch)
    case Forall(x, inner) => 200 + formulaPenalty(inner, branch)
    case _ => 0

  def substitutionScore(subst: Substitution, branch: Branch): Int = {
    def pairPenalty(v: Variable, t: Expression) = {
      val variablePenalty = branch.unifiable(v)._2 + branch.numberInstantiated(v) * 20
      def termPenalty(t: Expression): Int = t match
        case x: Variable => if branch.unifiable.contains(x) then branch.unifiable(x)._2 * 1 else 0
        case c: Constant => 40
        case Application(f, a) => 100 + termPenalty(f) + termPenalty(a)
        case Lambda(v, inner) => 100 + termPenalty(inner)
      1 * variablePenalty + 1 * termPenalty(t)
    }
    subst.map((v, t) => pairPenalty(v, t)).sum
  }

  /**
   * Explodes one And formula
   * The alpha list of the branch must not be empty
   */
  def alpha(branch: Branch): Branch = {
    val f = branch.alpha.head
    f match
      case And(l, r) => branch.copy(alpha = branch.alpha.tail).prepended(l).prepended(r)
      case _ => throw Exception("Error: First formula of alpha is not an And")
  }

  /**
   * Explodes one Or formula, and alpha-simplifies it
   * Add the exploded formula to the used list, if one beta formula is found
   * The beta list of the branch must not be empty
   */
  def beta(branch: Branch): List[(Branch, Expression)] = {
    val f = branch.beta.head
    val b1 = branch.copy(beta = branch.beta.tail)
    f match
      case Or(l, r) =>
        List((b1.prepended(l), l), (b1.prepended(r), r))
      case _ => throw Exception("Error: First formula of beta is not an Or")
  }

  /**
   * Explodes one Exists formula
   * Add the unquantified formula to the branch
   * Since the bound variable is not marked as suitable for instantiation, it behaves as a constant symbol (skolem)
   */
  def delta(branch: Branch): (Branch, Variable, Expression) = {
    val f = branch.delta.head
    f match
      case Exists(v, body) =>
        if branch.skolemized.contains(v) then
          val newV = Variable(Identifier(v.id.name, branch.maxIndex), Ind)
          val newInner = substituteVariables(body, Map(v -> newV))
          (branch.copy(delta = branch.delta.tail, maxIndex = branch.maxIndex + 1).prepended(newInner), newV, newInner)
        else (branch.copy(delta = branch.delta.tail, skolemized = branch.skolemized + v).prepended(body), v, body)
      case _ => throw Exception("Error: First formula of delta is not an Exists")
  }

  /**
   * Explodes one Forall formula
   * Add the unquantified formula to the branch and mark the bound variable as suitable for unification
   * This step will most of the time be cancelled when building the proof, unless any arbitrary instantiation is sufficient to get a proof.
   */
  def gamma(branch: Branch): (Branch, Variable, Expression) = {
    val f = branch.gamma.head
    f match
      case Forall(v, body) =>
        val (ni, nb) = branch.unifiable.get(v) match
          case None =>
            (body, v)
          case Some(value) =>
            val newBound = Variable(Identifier(v.id.name, branch.maxIndex), Ind)
            val newInner = substituteVariables(body, Map(v -> newBound))
            (newInner, newBound)
        val b1 = branch.copy(
          gamma = branch.gamma.tail,
          unifiable = branch.unifiable + (nb -> (f, formulaPenalty(body, branch))),
          numberInstantiated = branch.numberInstantiated + (nb -> (branch.numberInstantiated.getOrElse(v, 0))),
          maxIndex = branch.maxIndex + 1,
          varsOrder = branch.varsOrder + (nb -> branch.varsOrder.size)
        )
        (b1.prepended(ni), nb, ni)
      case _ => throw Exception("Error: First formula of gamma is not a Forall")

  }

  /**
   * When a closing unification has been found, apply it to the branch
   * This does not do backtracking: The metavariable remains available if it needs further instantiation.
   */
  def applyInst(branch: Branch, x: Variable, t: Expression): (Branch, Expression) = {
    val f = branch.unifiable(x)._1
    val newTried = branch.triedInstantiation.get(x) match
      case None => branch.triedInstantiation + (x -> Set(t))
      case Some(s) => branch.triedInstantiation + (x -> (s + t))

    val inst = f match
      case Forall(v, body) => instantiate(body, v, t)
      case _ => throw Exception("Error: Prop in unifiable is not a Forall")
    val r = branch
      .prepended(inst)
      .copy(
        triedInstantiation = newTried,
        numberInstantiated = branch.numberInstantiated + (x -> (branch.numberInstantiated(x) + 1))
      )
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
        branch.alpha.head match
          case Application(Application(and, left), right) =>
            if proof.head.bot.left.contains(left) || proof.head.bot.left.contains(right) then
              val sequent = proof.head.bot.copy(left = (proof.head.bot.left - left - right) + branch.alpha.head)
              (Weakening(sequent, proof.size - 1) :: proof, step + 1)
            else (proof, step)
          case _ => throw Exception("Error: First formula of alpha is not an And")
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
          branch.beta.head match
            case Or(left, right) =>
              (LeftOr(sequent, treversed.reverse, Seq(left, right)) :: proo, treversed.size)
            case _ => throw Exception("Error: First formula of beta is not an Or")
        else (proo, proo.size - 1)
      )
    else if (branch.gamma.nonEmpty) // If branch contains a Gamma formula (LeftForall)
      val rec = gamma(branch)
      val upperProof = decide(rec._1)
      // LeftForall(bot: Sequent, t1: Int, phi: Expression, x: Variable, t: Expression)
      upperProof.map((proof, step) =>
        if proof.head.bot.left.contains(rec._3) then
          val sequent = (proof.head.bot -<< rec._3) +<< branch.gamma.head
          branch.gamma.head match
            case Forall(v, body) =>
              (LeftForall(sequent, step, body, v, rec._2()) :: proof, step + 1)
            case _ => throw Exception("Error: First formula of gamma is not a Forall")
        else (proof, step)
      )
    else if (closeSubst.nonEmpty && closeSubst.get._1.nonEmpty) // If branch can be closed with Instantiation (LeftForall)
      val (x, t) = closeSubst.get._1.minBy((x, t) => branch.varsOrder(x))
      val (recBranch, instantiated) = applyInst(branch, x, t)
      val upperProof = decide(recBranch)
      upperProof.map((proof, step) =>
        if proof.head.bot.left.contains(instantiated) then
          val sequent = (proof.head.bot -<< instantiated) +<< branch.unifiable(x)._1
          branch.unifiable(x)._1 match
            case Forall(v, body) =>
              (LeftForall(sequent, step, body, v, t) :: proof, step + 1)
            case _ => throw Exception("Error: Prop in unifiable is not a Forall")
        else (proof, step)
      )
    else None
    // End of decide
  }

  def containsAlpha(set: Set[Expression], f: Expression): Boolean = f match {
    case And(left, right) => containsAlpha(set, left) || containsAlpha(set, right)
    case _ => set.contains(f)
  }

  def instantiate(f: Expression, x: Variable, t: Expression): Expression = f match
    case v: Variable => if v == x then t else v
    case c: Constant => c
    case Application(f, a) => Application(instantiate(f, x, t), instantiate(a, x, t))
    case Lambda(v, inner) => if (v == x) f else Lambda(v, instantiate(inner, x, t))
}
