package lisa.automation
import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.OutputManager._
import lisa.utils.prooflib.ProofTacticLib._
import lisa.kernel.proof.SCProofChecker

import scala.collection.immutable.HashMap

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
    // Iterative deepening: increase maxInstPerVar and budget to allow more work per iteration
    // Faster escalation through low inst levels; more levels for higher inst discovery
    val instLimits = Seq(1, 2, 3, 5, 8, 12)
    val budgetLimits = Seq(200000, 1000000, 5000000, 20000000, 50000000, 100000000)
    // Per-level wall-clock time limits: fast at low levels, generous at high levels
    val levelTimeLimits = Seq(5000L, 5000L, 5000L, 5000L, 15000L, 30000L)
    var proof: Option[(List[SCProofStep], Int)] = None
    var i = 0
    while (proof.isEmpty && i < instLimits.length) {
      if debug then { profileDecideCalls = 0; profileGroundCloses = 0; profileCloseAllCalls = 0; profileCloseAllTimeNs = 0; profileCloseWithInst = 0; profileCloseAllSetupNs = 0; profileCloseAllUnifyNs = 0; profileCloseAllPostNs = 0; profileCloseAllFilterNs = 0; profileCloseAllSubstCount = 0 }
      decideBudget.set(budgetLimits(i))
      instAttemptBudget.set(budgetLimits(i)) // unused placeholder
      concreteGammaBudget.set(5) // max 5 concrete gamma probes per level
      levelDeadline.set(System.currentTimeMillis() + levelTimeLimits(i))
      proof = decide(Branch.empty(nextId + 1, uv, instLimits(i)).prepended(nf))
      if debug then pr(s"  Level $i (inst=${instLimits(i)}, budget=${budgetLimits(i)}): decides=$profileDecideCalls, groundCloses=$profileGroundCloses, closeAllCalls=$profileCloseAllCalls, closeAllMs=${profileCloseAllTimeNs/1000000}, substCount=$profileCloseAllSubstCount, setupMs=${profileCloseAllSetupNs/1000000}, unifyMs=${profileCloseAllUnifyNs/1000000}, postMs=${profileCloseAllPostNs/1000000}, filterMs=${profileCloseAllFilterNs/1000000}")
      i += 1
    }
    proof match
      case None => None
      case Some((p, _)) =>
        val scProof = SCProof((Restate(sequent, p.length) :: Weakening(nf |- (), p.length - 1) :: p).reverse.toIndexedSeq, IndexedSeq.empty)
        val selfCheck = debug
        if selfCheck then
          val checkResult = SCProofChecker.checkSCProof(scProof)
          if !checkResult.isValid then
            def ep(s: String) = System.err.println(s)
            ep(s"=== PROOF VALIDATION FAILED ===")
            ep(s"Original sequent: ${sequent.left.map(_.repr).mkString(", ")} |- ${sequent.right.map(_.repr).mkString(", ")}")
            ep(s"NNF formula nf: ${nf.repr}")
            ep(s"Proof has ${scProof.steps.length} steps")
            def validateStep(proof: SCProof, step: SCProofStep, idx: Int): Boolean =
              SCProofChecker.checkSingleSCStep(idx, step, (i: Int) => proof.getSequent(i), proof.imports.size).isValid
            def stepName(step: SCProofStep): String = step match
              case RestateTrue(bot) => "RestateTrue"
              case Weakening(bot, t1) => s"Weakening(ref=$t1)"
              case Restate(bot, t1) => s"Restate(ref=$t1)"
              case LeftForall(bot, t1, phi, x, t) => s"LeftForall(ref=$t1, x=${x.repr}, t=${t.repr})"
              case LeftExists(bot, t1, phi, x) => s"LeftExists(ref=$t1, x=${x.repr})"
              case LeftOr(bot, ts, _) => s"LeftOr(refs=${ts.mkString(",")})"
              case SCSubproof(sp, premises) => s"SCSubproof(${sp.steps.length} steps)"
              case _ => step.getClass.getSimpleName
            def printProofSteps(proof: SCProof, indent: String): Unit =
              proof.steps.zipWithIndex.foreach { (step, idx) =>
                val stepValid = validateStep(proof, step, idx)
                val tag = if stepValid then "OK" else "FAIL"
                val leftFmls = step.bot.left.map(_.repr).mkString(", ")
                val rightFmls = step.bot.right.map(_.repr).mkString(", ")
                ep(s"${indent}Step $idx [$tag]: ${stepName(step)}  bot: $leftFmls |- $rightFmls")
                step match
                  case SCSubproof(sp, _) =>
                    printProofSteps(sp, indent + "  ")
                  case _ => ()
              }
            printProofSteps(scProof, "  ")
            ep(s"=== END PROOF VALIDATION ===")
        Some(scProof)

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
      atoms: (Set[Expression], Set[Expression]), // split into positive and negatives!
      unifiable: Map[Variable, (Expression, Int)], // map between metavariables and the original formula they came from, with the penalty associated to the complexity of the formula.
      numberInstantiated: Map[Variable, Int], // map between variables and the number of times they have been instantiated

      skolemized: Set[Variable], // set of variables that have been skolemized
      triedInstantiation: Map[Variable, Set[Expression]], // map between metavariables and the term they were already instantiated with
      maxIndex: Int, // the maximum index used for skolemization and metavariables
      varsOrder: Map[Variable, Int], // the order in which variables were instantiated. In particular, if the branch contained the formula ∀x. ∀y. ... then x > y.
      unusedVar: Variable, // a variable the is neither free nor bound in the original formula.
      gammaRound: Int = 0, // unused - kept for compatibility
      maxInstPerVar: Int = 1, // maximum instantiations per metavariable (iterative deepening parameter)
      instDepth: Int = 0, // depth of nested close-with-instantiation chains
      negByHead: Map[Expression, Set[Expression]] = Map.empty // negative atoms indexed by head predicate
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
        val head = headPred(f)
        this.copy(atoms = (atoms._1, atoms._2 + f), negByHead = negByHead.updated(head, negByHead.getOrElse(head, Set.empty) + f))
      case _ =>
        this.copy(atoms = (atoms._1 + f, atoms._2))

    def prependedAll(l: Seq[Expression]): Branch = l.foldLeft(this)((a, b) => a.prepended(b))

    def asSequent: Sequent = (beta ++ delta ++ gamma ++ atoms._1 ++ atoms._2.map(a => !a)).toSet |- Set() // inefficient, not used

    import Branch.*
    override def toString(): String =
      val pretUnif = unifiable.map((x, f) => x.repr + " -> " + f._1.repr + " : " + f._2).mkString("Unif(", ", ", ")")
      // val pretTried = triedInstantiation.map((x, t) => x.id + " -> " + prettyTerm(t, true)).mkString("Tried(", ", ", ")")
      (s"Branch(" +
        s"${RED(prettyIte(alpha, "alpha"))}, " +
        s"${GREEN(prettyIte(beta, "beta"))}, " +
        s"${BLUE(prettyIte(delta, "delta"))}, " +
        s"${YELLOW(prettyIte(gamma, "gamma"))}, " +
        s"${MAGENTA(prettyIte(atoms._1, "+"))}, ${CYAN(prettyIte(atoms._2, "-"))}, " + ""
        // s"$pretUnif, _, _)"
      ).split("'").mkString("").split("_").mkString("")

  }
  object Branch {
    def empty = Branch(Nil, Nil, Nil, Nil, (Set.empty, Set.empty), Map.empty, Map.empty, Set.empty, Map.empty, 1, Map.empty, Variable(Identifier("§uv", 0), Ind))
    def empty(n: Int, uv: Variable, maxInst: Int = 1) = Branch(Nil, Nil, Nil, Nil, (Set.empty, Set.empty), Map.empty, Map.empty, Set.empty, Map.empty, n, Map.empty, uv, maxInstPerVar = maxInst)
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
  def prettySubst(s: Substitution): String = s.map((x, t) => x.repr + " -> " + t.repr).mkString("Subst(", ", ", ")")

  /**
   * Transitively resolve a substitution so that metavariable-to-metavariable
   * chains are collapsed to their final concrete terms.
   * E.g., {X → Z1, Z1 → c} becomes {X → c, Z1 → c}.
   */
  def resolveSubstitution(subst: Substitution): Substitution = {
    def resolve(t: Expression, visited: Set[Variable]): Expression = t match
      case v: Variable if subst.contains(v) && !visited.contains(v) =>
        resolve(subst(v), visited + v)
      case Application(f, a) => Application(resolve(f, visited), resolve(a, visited))
      case _ => t
    subst.map((v, t) => v -> resolve(t, Set(v)))
  }

  /**
   * Check if a variable occurs anywhere in an expression (for occurs check in unification).
   * Short-circuits on first match — faster than t.freeVariables.contains(x).
   */
  private def occursIn(x: Variable, t: Expression): Boolean = t match
    case v: Variable => v == x
    case Application(f, a) => occursIn(x, f) || occursIn(x, a)
    case Lambda(v, body) => v != x && occursIn(x, body)
    case _ => false

  /**
   * Detect if two terms can be unified, and if so, return a substitution that unifies them.
   * Returns Iterator for lazy evaluation — unification stops when consumer stops iterating.
   */
  def unify(t1: Expression, t2: Expression, current: Substitution, br: Branch): Iterator[Substitution] = (t1, t2) match
    case (x: Variable, y: Variable) if (br.unifiable.contains(x) || x.id.no > br.maxIndex) && (br.unifiable.contains(y) || y.id.no > br.maxIndex) =>
      if x == y then Iterator.single(current)
      else if current.contains(x) then unify(current(x), t2, current, br)
      else if current.contains(y) then unify(t1, current(y), current, br)
      else
        // Commit to one direction to avoid exponential branching.
        // Map renamed (higher-index) variable to the other to keep original variables free.
        if x.id.no > y.id.no then Iterator.single(current + (x -> y))
        else Iterator.single(current + (y -> x))
    case (x: Variable, t2: Expression) if br.unifiable.contains(x) || x.id.no > br.maxIndex =>
      val newt2 = if current.isEmpty then t2 else substituteVariables(t2, current)
      if occursIn(x, newt2) then Iterator.empty
      else if (current.contains(x)) unify(current(x), newt2, current, br)
      else Iterator.single(current + (x -> newt2))
    case (t1: Expression, y: Variable) if br.unifiable.contains(y) || y.id.no > br.maxIndex =>
      val newt1 = if current.isEmpty then t1 else substituteVariables(t1, current)
      if occursIn(y, newt1) then Iterator.empty
      else if (current.contains(y)) unify(newt1, current(y), current, br)
      else Iterator.single(current + (y -> newt1))
    case (Application(f1, a1), Application(f2, a2)) =>
      unify(f1, f2, current, br).flatMap(s => unify(a1, a2, s, br))
    case _ => if t1 == t2 then Iterator.single(current) else Iterator.empty

  /**
   * Detect if two atoms can be unified, and if so, return a substitution that unifies them.
   */
  def unifyPred(pos: Expression, neg: Expression, br: Branch): Iterator[Substitution] = {
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
    bestSubst(closeAll(branch), branch)
  }

  /**
   * Extract the head predicate symbol of an atom (unwrap applications).
   */
  def headPred(e: Expression): Expression = e match
    case Application(f, _) => headPred(f)
    case _ => e

  /**
   * Return ALL valid closing substitutions for the branch, after filtering already-tried ones.
   */
  def closeAll(branch: Branch): List[(Substitution, Set[Expression])] = {
    val tSetup = if debug then System.nanoTime() else 0L
    val newMap = branch.atoms._1
      .flatMap(pred => pred.freeVariables.filter(v => branch.unifiable.contains(v)))
      .map(v => v -> Variable(Identifier(v.id.name, v.id.no + branch.maxIndex + 1), Ind))
      .toMap
    val inverseNewMap = newMap.map((k, v) => v -> k).toMap
    val renamedPos = branch.atoms._1.map(pred => substituteVariables(pred, newMap))

    // Check for ⊥ in positive atoms
    if renamedPos.contains(bot) then return List((Substitution.empty, Set(bot)))

    // Use pre-computed negative atom index by head predicate
    val negByHead = branch.negByHead

    val tUnify = if debug then System.nanoTime() else 0L

    // Merged unification + post-processing with cap to avoid processing millions of substitutions.
    // The decide function only uses at most 15 substitutions, so moderate caps are safe.
    // Adaptive caps: reduce when many metavariables to prevent combinatorial explosion
    val nUnifiable = branch.unifiable.size
    val maxSubstitutions = if nUnifiable > 10 then 30 else 100
    val maxPerPair = if nUnifiable > 10 then 3 else if nUnifiable > 6 then 5 else 10
    val maxRawTotal = if nUnifiable > 10 then 500 else if nUnifiable > 6 then 2000 else 5000
    // Time cap: prevent any single closeAll from dominating (3ms for heavy, 5ms otherwise)
    val closeAllDeadlineNs = System.nanoTime() + (if nUnifiable > 6 then 3_000_000L else 5_000_000L)
    var result: List[(Substitution, Set[Expression])] = Nil
    var rawCount = 0
    var done = false

    for (p <- renamedPos if !done) {
      val pHead = headPred(p)
      for (n <- negByHead.getOrElse(pHead, Set.empty) if !done) {
        // Pre-compute resolvedSet once per (p, n) pair (same for all substitutions)
        lazy val resolvedSet = Set(p, !n).map(f => substituteVariables(f, inverseNewMap))
        val unifs = unifyPred(p, n, branch)
        var pairRaw = 0
        for (s <- unifs if !done && pairRaw < maxPerPair && rawCount < maxRawTotal) {
          pairRaw += 1
          rawCount += 1
          // Periodic time check to cap expensive unification
          if (rawCount % 50 == 0 && System.nanoTime() > closeAllDeadlineNs) then { done = true }
          else {
            // Quick check: does this substitution map back to identity (ground closure)?
            val isIdentity = s.forall((v, t) =>
              (inverseNewMap.contains(v) && t == inverseNewMap(v)) ||
              (newMap.contains(v) && t == newMap(v))
            )
            if isIdentity then
              if debug then {
                val tEnd = System.nanoTime()
                profileCloseAllSetupNs += (tUnify - tSetup)
                profileCloseAllUnifyNs += (tEnd - tUnify)
                profileCloseAllSubstCount += rawCount
              }
              return List((Substitution.empty, resolvedSet))
            else
              // Post-process immediately: resolve through inverseNewMap
              // Optimization: composedInverse = inverseNewMap in the common case where no original
              // positive variables are bound in the substitution (avoids K substituteVariables calls)
              val needsComposed = inverseNewMap.valuesIterator.exists(v => s.contains(v))
              val resolveMap = if needsComposed then inverseNewMap.map((v, t) => v -> substituteVariables(t, s)) else inverseNewMap
              val resolvedSubst = s.flatMap((v, t) =>
                if inverseNewMap.contains(v) then
                  if t == inverseNewMap(v) then None
                  else Some(inverseNewMap(v) -> substituteVariables(t, resolveMap))
                else if newMap.contains(v) && t == newMap(v) then None
                else Some(v -> substituteVariables(t, inverseNewMap))
              )
              // Filter: non-empty, all variables in unifiable and varsOrder, not already tried
              if resolvedSubst.nonEmpty
                && resolvedSubst.forall((v, _) => branch.unifiable.contains(v) && branch.varsOrder.contains(v))
                && !resolvedSubst.exists((x, t) =>
                  branch.triedInstantiation.contains(x) && branch.triedInstantiation(x).contains(t))
              then
                result = (resolvedSubst, resolvedSet) :: result
                if result.size >= maxSubstitutions then done = true
          } // end else
        }
      }
    }

    if debug then {
      val tEnd = System.nanoTime()
      profileCloseAllSetupNs += (tUnify - tSetup)
      profileCloseAllUnifyNs += (tEnd - tUnify)
      profileCloseAllPostNs += 0 // merged into unify phase
      profileCloseAllFilterNs += 0 // merged into unify phase
      profileCloseAllSubstCount += rawCount
    }

    result
  }

  def bestSubst(substs: List[(Substitution, Set[Expression])], branch: Branch): Option[(Substitution, Set[Expression])] = {
    if substs.isEmpty then return None
    val minSize = substs.minBy(_._1.size)
    val smallSubst = substs.filter(_._1.size == minSize._1.size)
    // Up to this, it is necessary for completeness. From this, it is heuristic.
    // println("subst_with_score: " + smallSubst.map(s => prettySubst(s._1) + " using " + s._2.map(_.repr).mkString("{", ", ", "}") + " score: " + substitutionScore(s._1, branch)).mkString(" | "))

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
        case c: Constant => 5
        case Application(f, a) => 50 + termPenalty(f) + termPenalty(a)
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
   * Flatten nested Or into a list of disjuncts.
   * Or(A, Or(B, C)) => [A, B, C]
   */
  private def flattenOr(e: Expression): List[Expression] = e match
    case Or(l, r) => flattenOr(l) ++ flattenOr(r)
    case _ => List(e)

  /**
   * Score a disjunct by structural complexity.
   * Lower = simpler = should be tried first.
   * Atoms/propositional constants are cheapest, foralls are most expensive.
   */
  private def disjunctComplexity(f: Expression): Int = f match
    case Forall(_, _) => 100
    case Exists(_, _) => 80
    case Or(_, _) => 60
    case And(_, _) => 40
    case _ => 1 // atoms, negated atoms, propositional constants

  /**
   * Explodes one Or formula into n-ary disjuncts, sorted by complexity.
   * Flattens nested Or and sorts: atoms first, foralls last.
   * The beta list of the branch must not be empty.
   */
  def beta(branch: Branch): List[(Branch, Expression)] = {
    val f = branch.beta.head
    val b1 = branch.copy(beta = branch.beta.tail)
    f match
      case Or(l, r) =>
        val disjuncts = flattenOr(f).sortBy(disjunctComplexity)
        disjuncts.map(d => (b1.prepended(d), d))
      case _ => throw Exception("Error: First formula of beta is not an Or")
  }

  /**
   * Explodes one Exists formula
   * Add the unquantified formula to the branch
   * Since the bound variable is not marked as suitable for instantiation, it behaves as a constant symbol (skolem)
   * Always uses a fresh variable to avoid clashes with gamma metavariables that may share the same name.
   */
  def delta(branch: Branch): (Branch, Variable, Expression) = {
    val f = branch.delta.head
    f match
      case Exists(v, body) =>
        val newV = Variable(Identifier(v.id.name, branch.maxIndex), Ind)
        val newInner = substituteVariables(body, Map(v -> newV))
        (branch.copy(delta = branch.delta.tail, skolemized = branch.skolemized + v, maxIndex = branch.maxIndex + 1).prepended(newInner), newV, newInner)
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
        // Check if this is a re-expansion (v already known to unifiable)
        val isReExpansion = branch.unifiable.contains(v)
        val (actualBody, actualVar) =
          if !isReExpansion then (body, v)
          else
            // Create a fresh metavariable for re-expansion
            val newBound = Variable(Identifier(v.id.name, branch.maxIndex), Ind)
            val newBody = substituteVariables(body, Map(v -> newBound))
            (newBody, newBound)
        // Track the number of gamma expansions of this original formula on the original variable
        val origExpansions = branch.numberInstantiated.getOrElse(v, -1) + 1
        // Re-add the formula to the tail if we haven't reached the limit
        val newGamma = if origExpansions < branch.maxInstPerVar - 1 then branch.gamma.tail :+ f else branch.gamma.tail
        val b1 = branch.copy(
          gamma = newGamma,
          unifiable = branch.unifiable + (actualVar -> (f, formulaPenalty(body, branch))),
          numberInstantiated = branch.numberInstantiated ++ Map(actualVar -> 0, v -> origExpansions),
          maxIndex = branch.maxIndex + 1,
          varsOrder = branch.varsOrder + (actualVar -> branch.varsOrder.size)
        )
        (b1.prepended(actualBody), actualVar, actualBody)
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
  // Thread-local budget for decide calls within one solve invocation
  val decideBudget = new java.util.concurrent.atomic.AtomicInteger(0)
  // Separate budget for close-with-instantiation attempts (prevents Skolem explosion)
  val instAttemptBudget = new java.util.concurrent.atomic.AtomicInteger(0)
  // Per-level wall-clock deadline to prevent early levels from consuming all time
  val levelDeadline = new java.util.concurrent.atomic.AtomicLong(Long.MaxValue)
  // Budget for concrete gamma probes per level (limits total overhead from speculative ground instantiation)
  val concreteGammaBudget = new java.util.concurrent.atomic.AtomicInteger(0)
  // Profiling counters (only active when debug=true)
  var profileDecideCalls = 0L
  var profileGroundCloses = 0L
  var profileCloseAllCalls = 0L
  var profileCloseAllTimeNs = 0L
  var profileCloseWithInst = 0L
  var profileCloseAllSetupNs = 0L
  var profileCloseAllUnifyNs = 0L
  var profileCloseAllPostNs = 0L
  var profileCloseAllFilterNs = 0L
  var profileCloseAllSubstCount = 0L

  def decide(branch: Branch): Option[(List[SCProofStep], Int)] = {
    // Decrement and check the global call budget and wall-clock deadline
    if (decideBudget.decrementAndGet() < 0 || System.currentTimeMillis() > levelDeadline.get()) return None
    if debug then profileDecideCalls += 1

    // Check for ⊥ in positive atoms (handles OL-simplified tautologies)
    if branch.atoms._1.contains(bot) then
      if debug then profileGroundCloses += 1
      return Some((List(RestateTrue(Sequent(Set(bot), Set()))), 0))

    // Fast ground closure using structural equality (atoms are Sets, O(1) contains)
    if branch.atoms._1.nonEmpty && branch.atoms._2.nonEmpty then
      val groundMatch = branch.atoms._2.find(branch.atoms._1.contains)
      if groundMatch.isDefined then
        if debug then profileGroundCloses += 1
        val n = groundMatch.get
        return Some((List(RestateTrue(Sequent(Set(n, !n), Set()))), 0))

    if (branch.alpha.nonEmpty) // If branch contains an Alpha formula (LeftAnd)
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
    else if (branch.beta.nonEmpty) // If branch contains a Beta formula (LeftOr) — with unit propagation
      // Beta ordering: prefer formulas where at least one disjunct trivially closes (ground closure).
      // Only reorder when there's a guaranteed win (ground closure score = 0).
      val selectedBranch = if branch.beta.size <= 1 then branch else {
        val scored = branch.beta.map(f => (f, betaScore(f, branch)))
        val bestScore = scored.minBy(_._2)._2
        // Only reorder if best score indicates at least one ground closure (score component = 0)
        if bestScore <= 1 then // at least one disjunct has ground closure (0) + other may not (0 or 1)
          val best = scored.find(_._2 == bestScore).get._1
          if best.uniqueNumber != branch.beta.head.uniqueNumber then
            branch.copy(beta = best :: branch.beta.filterNot(_.uniqueNumber == best.uniqueNumber))
          else branch
        else branch // keep original order when no clear winner
      }
      val list = beta(selectedBranch)
      val (proof, treversed, needed) = list.foldLeft((Some(Nil): Option[List[SCProofStep]], Nil: List[Int], true: Boolean))((prev, next) =>
        prev match
          case (None, _, _) => prev // proof failed
          case (_, _, false) =>
            prev // proof succeded early
          case (Some(prevProof), t, true) =>
            // Unit propagation: skip decide if this disjunct trivially conflicts with branch atoms
            val trivialClose = findLiteralClosure(next._2, branch.atoms)
            val res = trivialClose match
              case Some(closureSet) =>
                Some((List(RestateTrue(Sequent(closureSet, Set()))), 0))
              case None =>
                decide(next._1)
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
          val sequent = ((proo.reverse.zip(list).flatMap((proof, bf) => proof.bot.left - bf._2).toSet + selectedBranch.beta.head) |- ())
          // Use flattened disjunct list matching processing order for n-ary LeftOr.
          // Kernel accepts reordered disjuncts via OL equivalence (Or commutativity+associativity).
          (LeftOr(sequent, treversed.reverse, list.map(_._2)) :: proo, treversed.size)
        else (proo, proo.size - 1)
      )
    else if (branch.gamma.nonEmpty) // If branch contains a Gamma formula (LeftForall)
      // Connection-guided gamma selection: prefer gamma formulas whose body mentions branch atom predicates
      val posHeads = branch.atoms._1.map(headPred)
      val negHeads = branch.atoms._2.map(headPred)
      val selectedBranch = if posHeads.isEmpty && negHeads.isEmpty then branch
        else branch.gamma.find(f => f match
          case Forall(_, body) => hasConnectionToAtoms(body, posHeads, negHeads)
          case _ => false
        ) match
          case Some(f) if f.uniqueNumber != branch.gamma.head.uniqueNumber =>
            branch.copy(gamma = f :: branch.gamma.filterNot(_.uniqueNumber == f.uniqueNumber))
          case _ => branch

      // Try concrete gamma instantiation with ground terms (budget-limited probe)
      var concreteResult: Option[(List[SCProofStep], Int)] = None
      // Only try concrete gamma for first expansion of this formula and if probe budget remains
      val isFirstExpansion = selectedBranch.numberInstantiated.getOrElse(
        selectedBranch.gamma.head match { case Forall(v, _) => v; case _ => null }, -1) == -1
      val groundTerms = if isFirstExpansion && concreteGammaBudget.get() > 0 then collectGroundTerms(selectedBranch) else Nil
      if groundTerms.nonEmpty then
        selectedBranch.gamma.head match
          case Forall(v, body) =>
            val concreteProbeMaxBudget = 200
            val concreteProbeMaxTime = 100L // ms
            val gIter = groundTerms.iterator.take(2)
            val savedBudget = decideBudget.get()
            val savedDeadline = levelDeadline.get()
            concreteGammaBudget.decrementAndGet() // consume one probe from the per-level budget
            while (concreteResult.isEmpty && gIter.hasNext && decideBudget.get() > 0 && System.currentTimeMillis() < savedDeadline) {
              val term = gIter.next()
              val concBody = substituteVariables(body, Map(v -> term))
              val origExpansions = selectedBranch.numberInstantiated.getOrElse(v, -1) + 1
              val newGamma = if origExpansions < selectedBranch.maxInstPerVar - 1 then selectedBranch.gamma.tail :+ selectedBranch.gamma.head else selectedBranch.gamma.tail
              val concBranch = selectedBranch.copy(
                gamma = newGamma,
                numberInstantiated = selectedBranch.numberInstantiated + (v -> origExpansions),
                maxIndex = selectedBranch.maxIndex
              ).prepended(concBody)
              val probeBudget = math.min(savedBudget, concreteProbeMaxBudget)
              decideBudget.set(probeBudget)
              val probeDeadline = math.min(savedDeadline, System.currentTimeMillis() + concreteProbeMaxTime)
              levelDeadline.set(probeDeadline)
              val probeResult = decide(concBranch)
              val usedBudget = probeBudget - math.max(0, decideBudget.get())
              decideBudget.set(math.max(0, savedBudget - usedBudget))
              levelDeadline.set(savedDeadline)
              concreteResult = probeResult.map((proof, step) =>
                val conclusionLeft = proof.head.bot.left
                if conclusionLeft.contains(concBody) then
                  val sequent = (proof.head.bot -<< concBody) +<< selectedBranch.gamma.head
                  (LeftForall(sequent, step, body, v, term) :: proof, step + 1)
                else
                  val matchOpt = conclusionLeft.iterator
                    .map(f => (f, matchBody(body, v, f)))
                    .collectFirst { case (f, Some(resolvedT)) => (f, resolvedT) }
                  matchOpt match
                    case Some((actual, resolvedT)) =>
                      val sequent = (proof.head.bot -<< actual) +<< selectedBranch.gamma.head
                      (LeftForall(sequent, step, body, v, resolvedT) :: proof, step + 1)
                    case None =>
                      (proof, step)
              )
            }
          case _ => ()

      if concreteResult.nonEmpty then concreteResult
      else
        // Normal free-variable gamma expansion
        val rec = gamma(selectedBranch)
        val upperProof = decide(rec._1)
        // LeftForall(bot: Sequent, t1: Int, phi: Expression, x: Variable, t: Expression)
        upperProof.map((proof, step) =>
          val conclusionLeft = proof.head.bot.left
          selectedBranch.gamma.head match
            case Forall(v, body) =>
              if conclusionLeft.contains(rec._3) then
                val sequent = (proof.head.bot -<< rec._3) +<< selectedBranch.gamma.head
                (LeftForall(sequent, step, body, v, rec._2()) :: proof, step + 1)
              else
                val matchOpt = conclusionLeft.iterator
                  .map(f => (f, matchBody(body, v, f)))
                  .collectFirst { case (f, Some(resolvedT)) => (f, resolvedT) }
                matchOpt match
                  case Some((actual, resolvedT)) =>
                    val sequent = (proof.head.bot -<< actual) +<< selectedBranch.gamma.head
                    (LeftForall(sequent, step, body, v, resolvedT) :: proof, step + 1)
                  case None =>
                    (proof, step)
            case _ => throw Exception("Error: First formula of gamma is not a Forall")
        )
    else // No more alpha/delta/beta/gamma — try instantiation strategies
      var result: Option[(List[SCProofStep], Int)] = None
      val t0 = if debug then System.nanoTime() else 0L
      val allClosingSubsts = if branch.unifiable.isEmpty then Nil else closeAll(branch)
      if debug then { profileCloseAllCalls += 1; profileCloseAllTimeNs += System.nanoTime() - t0 }

      if allClosingSubsts.nonEmpty then
        val sorted = allClosingSubsts.sortBy(s => substitutionScore(s._1, branch))
        val maxAttempts = 15
        var attempts = 0
        val iter = sorted.iterator
        while (result.isEmpty && iter.hasNext && attempts < maxAttempts) {
          val (subst, set) = iter.next()
          attempts += 1
          instAttemptBudget.decrementAndGet()
          val sortedBindings = subst.toList.sortBy((x, _) => -branch.varsOrder(x))
          var currentBranch = branch
          var appliedBindings: List[(Variable, Expression, Expression)] = Nil
          for ((x, t) <- sortedBindings) {
            val (newBranch, inst) = applyInst(currentBranch, x, t)
            appliedBindings = (x, t, inst) :: appliedBindings
            currentBranch = newBranch
          }
          result = decide(currentBranch).map((proof, step) =>
            var currentProof = proof
            var currentStep = step
            for ((x, t, instantiated) <- appliedBindings) {
              val forallFormula = branch.unifiable(x)._1
              forallFormula match
                case Forall(v, body) =>
                  val conclusionLeft = currentProof.head.bot.left
                  if conclusionLeft.contains(instantiated) then
                    val sequent = (currentProof.head.bot -<< instantiated) +<< forallFormula
                    currentProof = LeftForall(sequent, currentStep, body, v, t) :: currentProof
                    currentStep += 1
                  else
                    val matchOpt = conclusionLeft.iterator
                      .map(f => (f, matchBody(body, v, f)))
                      .collectFirst { case (f, Some(resolvedT)) => (f, resolvedT) }
                    matchOpt match
                      case Some((actual, resolvedT)) =>
                        val sequent = (currentProof.head.bot -<< actual) +<< forallFormula
                        currentProof = LeftForall(sequent, currentStep, body, v, resolvedT) :: currentProof
                        currentStep += 1
                      case None =>
                        ()
                case _ => throw Exception("Error: Prop in unifiable is not a Forall")
            }
            (currentProof, currentStep)
          )
        }

      result
    // End of decide
  }

  /**
   * Try to match `target` against `pattern` where `v` is a pattern variable.
   * Returns Some(term) if target = pattern[v → term] for some term.
   * Returns None if no match.
   */
  def matchBody(pattern: Expression, v: Variable, target: Expression): Option[Expression] = {
    var result: Option[Expression] = null // null = not yet found, Some = found, None = failed

    def go(p: Expression, t: Expression): Boolean = (p, t) match
      case (pv: Variable, _) if pv == v =>
        result match
          case null => result = Some(t); true
          case Some(prev) => prev == t
          case None => false
      case (pv: Variable, tv: Variable) => pv == tv
      case (pc: Constant, tc: Constant) => pc == tc
      case (Application(pf, pa), Application(tf, ta)) =>
        go(pf, tf) && go(pa, ta)
      case (Lambda(pv, pb), Lambda(tv, tb)) =>
        pv == tv && go(pb, tb)
      case _ => false

    if go(pattern, target) then
      result match
        case null => None // v didn't appear in pattern - no useful match
        case Some(term) => Some(term)
        case None => None
    else None
  }

  def containsAlpha(set: Set[Expression], f: Expression): Boolean = f match {
    case And(left, right) => containsAlpha(set, left) || containsAlpha(set, right)
    case _ => set.contains(f)
  }

  /**
   * Check if a formula body contains a literal whose head predicate matches branch atoms.
   * Used for connection-guided gamma selection.
   */
  private def hasConnectionToAtoms(body: Expression, posHeads: Set[Expression], negHeads: Set[Expression]): Boolean = body match
    case And(l, r) => hasConnectionToAtoms(l, posHeads, negHeads) || hasConnectionToAtoms(r, posHeads, negHeads)
    case Or(l, r) => hasConnectionToAtoms(l, posHeads, negHeads) || hasConnectionToAtoms(r, posHeads, negHeads)
    case Exists(_, inner) => hasConnectionToAtoms(inner, posHeads, negHeads)
    case Forall(_, inner) => hasConnectionToAtoms(inner, posHeads, negHeads)
    case Neg(inner) => posHeads.contains(headPred(inner)) // ¬p(...) can close with positive p(...)
    case _ => negHeads.contains(headPred(body)) // p(...) can close with negative ¬p(...)

  /**
   * Check if a formula, when added to a branch as a literal, would immediately
   * create a contradiction with existing atoms (exact structural match).
   * Returns Some(closureSet) for a trivial RestateTrue proof, or None.
   * This enables unit propagation: in Or(A, B), if A trivially conflicts, only B needs exploration.
   */
  private def findLiteralClosure(f: Expression, atoms: (Set[Expression], Set[Expression])): Option[Set[Expression]] = f match
    case And(_, _) | Or(_, _) | Exists(_, _) | Forall(_, _) => None
    case Neg(inner) =>
      inner match
        case And(_, _) | Or(_, _) | Exists(_, _) | Forall(_, _) => None
        case _ =>
          if atoms._1.contains(inner) then Some(Set(inner, f))
          else None
    case _ =>
      if f == bot then Some(Set(f))
      else if atoms._2.contains(f) then Some(Set(f, !f))
      else None

  /**
   * Score a disjunct for how likely it is to close quickly.
   * Lower score = easier to close.
   * 0 = trivial ground closure, 1 = potential unification closure, 2 = complex formula, 3 = no closure potential
   */
  private def disjunctClosureScore(f: Expression, atoms: (Set[Expression], Set[Expression]), negByHead: Map[Expression, Set[Expression]]): Int = f match
    case And(_, _) | Or(_, _) | Exists(_, _) | Forall(_, _) => 2 // complex formula, needs further expansion
    case Neg(inner) =>
      inner match
        case And(_, _) | Or(_, _) | Exists(_, _) | Forall(_, _) => 2
        case _ =>
          if atoms._1.contains(inner) then 0 // ground closure
          else if atoms._1.exists(p => headPred(p) == headPred(inner)) then 1 // potential unification
          else 3 // no closure potential
    case _ =>
      if f == bot then 0
      else if atoms._2.contains(f) then 0 // ground closure
      else if negByHead.getOrElse(headPred(f), Set.empty).nonEmpty then 1 // potential unification
      else 3 // no closure potential

  /**
   * Score a beta formula (disjunction) for priority ordering.
   * Lower score = should be processed first.
   * The score combines both disjuncts' closure potential:
   *   both trivially close (0+0=0) > one trivially closes (0+x) > both have potential > neither
   */
  private def betaScore(f: Expression, branch: Branch): Int = {
    // Flatten nested Or and use minimum closure score of any disjunct.
    // If any disjunct has ground closure (score 0), this formula should be processed first.
    val disjuncts = flattenOr(f)
    if disjuncts.isEmpty then 10
    else disjuncts.map(d => disjunctClosureScore(d, branch.atoms, branch.negByHead)).min
  }

  /**
   * Collect all ground terms of sort Ind (Skolem constants and other individual constants) from atoms.
   * Excludes metavariables (in unifiable) and predicate/function symbols (non-Ind sort).
   */
  private def collectGroundTerms(branch: Branch): Set[Expression] = {
    def extract(e: Expression): Set[Expression] = e match
      case v: Variable if v.sort == Ind && !branch.unifiable.contains(v) => Set(v)
      case c: Constant if c.sort == Ind => Set(c)
      case Application(f, a) => extract(a) ++ (if f.sort != Ind then extract(f) else Set.empty)
      case _ => Set.empty
    (branch.atoms._1.flatMap(extract) ++ branch.atoms._2.flatMap(extract)).toSet
  }

  /**
   * Fallback strategy: try instantiating metavariables with known ground terms.
   * This handles cases where closeAll can't find the right substitution because
   * the binding isn't discoverable through positive-negative pair unification alone.
   * For example, binding M_V → z₀ when z₀ appears only in ¬p(z₀) but M_V is in q(S_U, M_V).
   */
  private def tryGroundInstantiation(branch: Branch): Option[(List[SCProofStep], Int)] = {
    if decideBudget.get() < 0 || System.currentTimeMillis() > levelDeadline.get() then return None

    val groundTerms = collectGroundTerms(branch)
    if groundTerms.isEmpty then return None

    // Generate candidate (metavar, ground_term) pairs not yet tried
    val candidates = branch.unifiable.toList.flatMap { case (metaVar, (formula, penalty)) =>
      groundTerms.flatMap { term =>
        if branch.triedInstantiation.getOrElse(metaVar, Set.empty).contains(term) then None
        else Some((metaVar, term, penalty))
      }
    }
    if candidates.isEmpty then return None

    // Sort by penalty (prefer cheap / low-penalty metavariables first)
    val sorted = candidates.sortBy(_._3)
    val maxGroundAttempts = 5
    var result: Option[(List[SCProofStep], Int)] = None

    for ((x, t, _) <- sorted.take(maxGroundAttempts) if result.isEmpty) {
      if decideBudget.get() < 0 || System.currentTimeMillis() > levelDeadline.get() then return result
      val (newBranch, inst) = applyInst(branch, x, t)
      result = decide(newBranch).map { (proof, step) =>
        val forallFormula = branch.unifiable(x)._1
        forallFormula match
          case Forall(v, body) =>
            val conclusionLeft = proof.head.bot.left
            if conclusionLeft.contains(inst) then
              val sequent = (proof.head.bot -<< inst) +<< forallFormula
              (LeftForall(sequent, step, body, v, t) :: proof, step + 1)
            else
              val matchOpt = conclusionLeft.iterator
                .map(f => (f, matchBody(body, v, f)))
                .collectFirst { case (f, Some(resolvedT)) => (f, resolvedT) }
              matchOpt match
                case Some((actual, resolvedT)) =>
                  val sequent = (proof.head.bot -<< actual) +<< forallFormula
                  (LeftForall(sequent, step, body, v, resolvedT) :: proof, step + 1)
                case None =>
                  (proof, step)
          case _ => (proof, step)
      }
    }
    result
  }

  def instantiate(f: Expression, x: Variable, t: Expression): Expression =
    substituteVariables(f, Map(x -> t))
}
