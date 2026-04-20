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

  var debug = false
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

  /**
   * SInE (Sumo Inference Engine) relevance filtering.
   * Selects axioms (left-side formulas) likely relevant to the conjecture (right-side formulas).
   * Returns indices of selected axioms from the input sequence.
   */
  private def sineFilter(axioms: Seq[Expression], conjecture: Seq[Expression], depthLimit: Int = 3): Seq[Int] = {
    import scala.collection.mutable

    // Extract non-variable constant/function symbols from an expression
    def symbols(e: Expression): Set[Identifier] = {
      val syms = mutable.Set.empty[Identifier]
      def collect(e: Expression): Unit = e match {
        case Variable(_, _) => ()
        case Constant(id, _) => syms += id
        case Application(f, a) => collect(f); collect(a)
        case Lambda(_, body) => collect(body)
      }
      collect(e)
      syms.toSet
    }

    val axiomSyms = axioms.zipWithIndex.map((a, i) => (i, symbols(a)))
    // Symbol frequency = number of axioms containing the symbol
    val symbolFreq = mutable.Map.empty[Identifier, Int].withDefaultValue(0)
    for ((_, syms) <- axiomSyms; s <- syms) symbolFreq(s) += 1

    val conjectureSyms = conjecture.flatMap(symbols).toSet
    val activeSyms = mutable.Set.empty[Identifier] ++= conjectureSyms
    val selected = mutable.Set.empty[Int]

    for (_ <- 0 until depthLimit) {
      var newSyms = mutable.Set.empty[Identifier]
      for ((idx, syms) <- axiomSyms if !selected(idx)) {
        // Trigger = rarest symbol in the axiom
        val triggerOpt = syms.minByOption(s => symbolFreq(s))
        triggerOpt match {
          case Some(trigger) if activeSyms(trigger) =>
            selected += idx
            newSyms ++= (syms -- activeSyms)
          case _ => ()
        }
      }
      if (newSyms.isEmpty) return selected.toSeq.sorted
      activeSyms ++= newSyms
    }

    selected.toSeq.sorted
  }

  /**
   * Core iterative deepening tableau search. Returns proof steps or None.
   */
  /**
   * Core iterative deepening tableau search with optional global time limit.
   * Returns proof steps, proof size, and NNF formula, or None.
   */
  /**
   * Ground forward chaining preprocessing: discovers useful instantiation terms
   * by iteratively grounding gamma formulas with connection-guided terms.
   * Returns a map from gamma formula unique numbers to ordered lists of useful terms.
   * This avoids metavariables and finds multi-step proofs through iterative grounding.
   */
  private def groundSaturation(initPosAtoms: Set[Expression], initNegAtoms: Set[Expression], initGammas: List[Expression], maxRounds: Int = 25, gsTimeLimitMs: Long = 3000L): Map[Long, List[Expression]] = {
    // Use pre-decomposed atoms and gammas (already in main solver namespace)
    var posAtoms = initPosAtoms
    var negAtoms = initNegAtoms // stored without negation (inner of Neg)
    var gammas = initGammas // ∀x.body

    // Skolem index for existentials found INSIDE gamma bodies during forward chaining
    var nextSkolemIdx = 100000 // high index to avoid clashes (only for inner existentials)

    // Quick exit: no ground atoms → nothing to drive forward chaining
    if (posAtoms.isEmpty && negAtoms.isEmpty) return Map.empty

    // Build head indexes
    def headPredLocal(e: Expression): Expression = e match
      case Application(f, _) => headPredLocal(f)
      case _ => e
    var posByHead = posAtoms.groupBy(headPredLocal)
    var negByHead = negAtoms.groupBy(headPredLocal)
    // Collect all ground terms
    def extractTerms(e: Expression): Set[Expression] = e match
      case v: Variable if v.sort == Ind => Set(v)
      case c: Constant if c.sort == Ind => Set(c)
      case Application(f, a) => extractTerms(a) ++ (if f.sort != Ind then extractTerms(f) else Set.empty)
      case _ => Set.empty
    var groundTerms = (posAtoms.flatMap(extractTerms) ++ negAtoms.flatMap(extractTerms)).toSet

    // Track discovered hints: gamma uniqueNumber → list of useful terms
    val hints = scala.collection.mutable.Map.empty[Long, List[Expression]]
    // Track original gamma uniqueNumbers (only these get hints stored)
    val originalGammaKeys = gammas.map(_.uniqueNumber).toSet
    var totalGammasProcessed = 0
    val maxTotalGammas = 500 // cap to prevent combinatorial explosion
    // Track processed (gamma.uniqueNumber, term.uniqueNumber) to avoid redundant work
    val processedPairs = scala.collection.mutable.Set.empty[(Long, Long)]
    val gsDeadlineMs = System.currentTimeMillis() + gsTimeLimitMs // adaptive time limit for ground saturation

    // Phase 2: iterative grounding
    var prevGammaCount = gammas.size
    for (round <- 0 until maxRounds if gammas.nonEmpty && System.currentTimeMillis() < gsDeadlineMs) {
      var newAtoms = false
      val roundStartGammas = gammas.size
      var roundNewHints = 0
      var roundNewAtomCount = 0

      val currentGammas = gammas
      gammas = Nil  // reset: new inner gammas go to next round

      for (gf <- currentGammas if totalGammasProcessed < maxTotalGammas) {
        totalGammasProcessed += 1
        gf match
          case Forall(v, body) =>
            // Extract connection terms from body vs current atoms
            def extractBodyAtoms(e: Expression): List[(Expression, Boolean)] = e match
              case And(l, r) => extractBodyAtoms(l) ++ extractBodyAtoms(r)
              case Or(l, r) => extractBodyAtoms(l) ++ extractBodyAtoms(r)
              case Neg(inner) => List((inner, true))
              case Forall(_, inner) => extractBodyAtoms(inner)
              case Exists(_, inner) => extractBodyAtoms(inner)
              case _ if e.sort == Prop => List((e, false))
              case _ => Nil

            val bodyAtoms = extractBodyAtoms(body)
            val termCounts = scala.collection.mutable.Map.empty[Expression, Int]
            for ((atom, isNegated) <- bodyAtoms) {
              val matchSet = if isNegated then posAtoms else negAtoms
              val atomHead = headPredLocal(atom)
              val headSet = if isNegated then posByHead.getOrElse(atomHead, Set.empty) else negByHead.getOrElse(atomHead, Set.empty)
              for (ba <- headSet) {
                matchBodyPartial(atom, v, ba) match
                  case Some(t) => termCounts(t) = termCounts.getOrElse(t, 0) + 1
                  case None => ()
              }
            }
            val candidateTerms = termCounts.toList.sortBy(-_._2).map(_._1)

            // Handle vacuous quantifiers: if v doesn't appear in body, strip and add inner directly
            if (candidateTerms.isEmpty && !body.freeVariables.contains(v)) {
              body match
                case Forall(_, _) => gammas = body :: gammas // inner gamma for next round
                case _ => () // non-gamma body: would be processed as alpha/beta/atom, skip for now
            }

            for (t <- candidateTerms.take(5) if processedPairs.add((gf.uniqueNumber, t.uniqueNumber))) {
              // Record hint for this gamma (works for both top-level and inner gammas
              // since structurally identical expressions share the same uniqueNumber)
              val key = gf.uniqueNumber
              val existing = hints.getOrElse(key, Nil)
              if (!existing.contains(t)) {
                hints(key) = existing :+ t
              }
              // Instantiate and decompose the body
              val inst = substOpt(body, Map(v -> t))
              var instPending = List(inst)
              while (instPending.nonEmpty) {
                val f = instPending.head
                instPending = instPending.tail
                f match
                  case And(l, r) => instPending = l :: r :: instPending
                  case Exists(vv, bb) =>
                    val sk = Variable(Identifier(vv.id.name, nextSkolemIdx), Ind)
                    nextSkolemIdx += 1
                    instPending = substOpt(bb, Map(vv -> sk)) :: instPending
                  case Forall(_, _) =>
                    // Inner gamma: add to gammas list for next round
                    gammas = f :: gammas
                  case Or(_, _) =>
                    // Beta: check if all but one disjunct can be resolved
                    val disjuncts = flattenOr(f)
                    val unresolved = disjuncts.filter { d =>
                      d match
                        case Neg(inner) => !posAtoms.contains(inner) // can't resolve ¬P if P not in posAtoms
                        case _ if d == bot => false // ⊥ always resolvable
                        case _ => !negAtoms.contains(d) // can't resolve P if P not in negAtoms
                    }
                    if (unresolved.isEmpty) {
                      // All disjuncts resolve against current atoms — contradiction!
                      return hints.toMap
                    } else if (unresolved.size <= 2) {
                      // Most disjuncts resolve — add remaining as new formulas
                      for (u <- unresolved) instPending = u :: instPending
                    }
                    // else: too many unresolved, skip this beta
                  case Neg(inner) =>
                    if (!negAtoms.contains(inner)) {
                      negAtoms = negAtoms + inner
                      val h = headPredLocal(inner)
                      negByHead = negByHead.updated(h, negByHead.getOrElse(h, Set.empty) + inner)
                      groundTerms = groundTerms ++ extractTerms(inner)
                      newAtoms = true
                      // Check for ground closure
                      if (posAtoms.contains(inner)) return hints.toMap // found contradiction!
                    }
                  case _ =>
                    if (!posAtoms.contains(f)) {
                      posAtoms = posAtoms + f
                      val h = headPredLocal(f)
                      posByHead = posByHead.updated(h, posByHead.getOrElse(h, Set.empty) + f)
                      groundTerms = groundTerms ++ extractTerms(f)
                      newAtoms = true
                      // Check for ground closure
                      if (negAtoms.contains(f)) return hints.toMap // found contradiction!
                    }
              }
            }
          case _ => ()
      }

      if (debug) pr(s"    GS round $round: gammas=${gammas.size + currentGammas.size} (was $roundStartGammas), posAtoms=${posAtoms.size}, negAtoms=${negAtoms.size}, hints=${hints.values.map(_.size).sum}, processed=$totalGammasProcessed")
      // Merge new inner gammas with previously existing ones for next round
      gammas = gammas ++ currentGammas
      // Stop only if no new atoms AND no new gammas were generated (no progress at all)
      val currentGammaCount = gammas.size
      if (!newAtoms && currentGammaCount == prevGammaCount) return hints.toMap
      prevGammaCount = currentGammaCount
    }

    hints.toMap
  }

  // Thread-local storage for ground saturation hints (gamma uniqueNumber → probe terms)
  private val groundHints = new ThreadLocal[Map[Long, List[Expression]]] {
    override def initialValue(): Map[Long, List[Expression]] = Map.empty
  }

  // Thread-local global deadline for the solver (set by the benchmark harness or external caller)
  private val solverDeadline = new ThreadLocal[Long] {
    override def initialValue(): Long = Long.MaxValue
  }

  /** Set the global deadline for the solver. Call before solve(). */
  def setDeadline(deadlineMs: Long): Unit = solverDeadline.set(deadlineMs)

  /**
   * Rewrite biconditional NNF patterns to implicational form.
   * The OL NNF converts A ⇔ B into Or(And(A, B), And(¬A, ¬B)).
   * This creates compound beta branches that defeat unit propagation.
   * Rewriting to And(Or(¬A, B), Or(A, ¬B)) is OL-equivalent and produces
   * simple alpha + beta decomposition instead of exponential branching.
   *
   * Also handles the negated biconditional: Or(And(A, ¬B), And(¬A, B))
   * → And(Or(¬A, ¬B), Or(A, B))
   */
  private def rewriteBiconditionals(e: Expression): Expression = {
    def negate(f: Expression): Expression = f match
      case Neg(inner) => inner
      case _ => neg(f)

    def isNegOf(a: Expression, b: Expression): Boolean = (a, b) match
      case (Neg(inner), _) => inner.uniqueNumber == b.uniqueNumber
      case (_, Neg(inner)) => inner.uniqueNumber == a.uniqueNumber
      case _ => false

    // Check if two NNF formulas are DeMorgan negations of each other.
    // Handles patterns like And(A,B) vs Or(¬A,¬B) and Neg(A) vs A.
    def isNNFNeg(a: Expression, b: Expression): Boolean = (a, b) match
      case (Neg(inner), _) => inner.uniqueNumber == b.uniqueNumber
      case (_, Neg(inner)) => inner.uniqueNumber == a.uniqueNumber
      case (And(l1, r1), Or(l2, r2)) => isNNFNeg(l1, l2) && isNNFNeg(r1, r2)
      case (Or(l1, r1), And(l2, r2)) => isNNFNeg(l1, l2) && isNNFNeg(r1, r2)
      case _ => false

    // Produce NNF negation of a formula (applies DeMorgan when needed)
    def nnfNegate(f: Expression): Expression = f match
      case Neg(inner) => inner
      case And(l, r) => or(nnfNegate(l))(nnfNegate(r))
      case Or(l, r) => and(nnfNegate(l))(nnfNegate(r))
      case _ => neg(f)

    e match
      case Or(And(a1, b1), And(a2, b2)) =>
        val ra1 = rewriteBiconditionals(a1)
        val rb1 = rewriteBiconditionals(b1)
        val ra2 = rewriteBiconditionals(a2)
        val rb2 = rewriteBiconditionals(b2)
        // Check both simple negation and DeMorgan negation patterns
        val pairsMatch = (isNegOf(ra1, ra2) || isNNFNeg(ra1, ra2)) && (isNegOf(rb1, rb2) || isNNFNeg(rb1, rb2))
        val crossMatch = (isNegOf(ra1, rb2) || isNNFNeg(ra1, rb2)) && (isNegOf(rb1, ra2) || isNNFNeg(rb1, ra2))
        if pairsMatch then
          and(or(nnfNegate(ra1))(rb1))(or(ra1)(nnfNegate(rb1)))
        else if crossMatch then
          and(or(nnfNegate(ra1))(rb1))(or(ra1)(nnfNegate(rb1)))
        else if (ra1 eq a1) && (rb1 eq b1) && (ra2 eq a2) && (rb2 eq b2) then e
        else or(and(ra1)(rb1))(and(ra2)(rb2))
      case And(l, r) =>
        val rl = rewriteBiconditionals(l)
        val rr = rewriteBiconditionals(r)
        if (rl eq l) && (rr eq r) then e else and(rl)(rr)
      case Or(l, r) =>
        val rl = rewriteBiconditionals(l)
        val rr = rewriteBiconditionals(r)
        if (rl eq l) && (rr eq r) then e else or(rl)(rr)
      case Application(`forall`, Lambda(v, body)) =>
        val rb = rewriteBiconditionals(body)
        if rb eq body then e else Application(forall, Lambda(v, rb))
      case Application(`exists`, Lambda(v, body)) =>
        val rb = rewriteBiconditionals(body)
        if rb eq body then e else Application(exists, Lambda(v, rb))
      case _ => e
  }

  private def solveFormula(formulas: Seq[Expression], globalDeadlineMs: Long = Long.MaxValue): Option[(List[SCProofStep], Int, Expression)] = {
    val f = K.multiand(formulas)
    val taken = f.allVariables
    val nextIdNow = if taken.isEmpty then 0 else taken.maxBy(_.id.no).id.no + 1
    val (fnamed, nextId) = makeVariableNamesUnique(f, nextIdNow, f.freeVariables)
    val nf = rewriteBiconditionals(reducedNNFForm(fnamed))
    val uv = Variable(Identifier("§", nextId), Ind)
    val instLimits = Seq(1, 2, 3, 5, 8, 12, 20, 30)
    val budgetLimits = Seq(200000, 1000000, 5000000, 20000000, 50000000, 100000000, 200000000, 500000000)
    // Reduced early level times to leave more budget for higher inst depths
    val baseLevelTimeLimits = Seq(800L, 1500L, 3000L, 5000L, 10000L, 20000L, 35000L, 60000L)

    // Effective deadline: use the passed-in deadline OR the thread-local solver deadline (whichever is sooner)
    val effectiveGlobalDeadline = math.min(globalDeadlineMs, solverDeadline.get())

    // Pre-decompose NNF into a branch to extract atoms and gammas for GS.
    // This ensures GS uses the SAME Skolem constants as the main solver.
    val dummyBranch = Branch.empty(nextId + 1, uv, 1).prepended(nf)
    val decomposed = decomposeAlphaDelta(dummyBranch)
    // Extract atoms and gammas from the decomposed branch
    val gsInitPosAtoms = decomposed.atoms._1
    val gsInitNegAtoms = decomposed.atoms._2
    val gsInitGammas = decomposed.gamma

    // Run ground saturation to discover useful instantiation terms
    // GS budget: at most 25% of remaining time, capped at 5s
    val gsTimeMs = math.min(5000L, math.max(500L, ((effectiveGlobalDeadline - System.currentTimeMillis()) * 0.25).toLong))
    val hints = groundSaturation(gsInitPosAtoms, gsInitNegAtoms, gsInitGammas, gsTimeLimitMs = gsTimeMs)
    groundHints.set(hints)
    if debug && hints.nonEmpty then pr(s"  Ground saturation: ${hints.values.map(_.size).sum} hints for ${hints.size} gammas")
    val hintCount = hints.values.map(_.size).sum

    var proof: Option[(List[SCProofStep], Int)] = None
    var i = 0
    var savedTimeMs = 0L
    while (proof.isEmpty && i < instLimits.length && System.currentTimeMillis() < effectiveGlobalDeadline && !Thread.currentThread().isInterrupted) {
      if debug then { profileDecideCalls = 0; profileGroundCloses = 0; profileCloseAllCalls = 0; profileCloseAllTimeNs = 0; profileCloseWithInst = 0; profileCloseAllSetupNs = 0; profileCloseAllUnifyNs = 0; profileCloseAllPostNs = 0; profileCloseAllFilterNs = 0; profileCloseAllSubstCount = 0 }
      decideBudget.set(budgetLimits(i))
      instAttemptBudget.set(budgetLimits(i))
      // Scale probe budget based on hint count: more hints → forward-chaining problem → more probing needed
      val probeBudget = if hintCount > 50 then math.min(200, hintCount) else 30
      concreteGammaBudget.set(probeBudget)
      val levelStart = System.currentTimeMillis()
      val remaining = (effectiveGlobalDeadline - levelStart).max(0)
      // Don't start a level if less than 200ms remain
      if (remaining < 200) then { i = instLimits.length }
      else {
        val effectiveTimeMs = math.min(baseLevelTimeLimits(i) + savedTimeMs, remaining)
        levelDeadline.set(levelStart + effectiveTimeMs)
        proof = decide(Branch.empty(nextId + 1, uv, instLimits(i)).prepended(nf))
        val levelElapsed = System.currentTimeMillis() - levelStart
        savedTimeMs = math.max(0L, effectiveTimeMs - levelElapsed)
        if debug then pr(s"  Level $i (inst=${instLimits(i)}, budget=${budgetLimits(i)}): decides=$profileDecideCalls, groundCloses=$profileGroundCloses, closeAllCalls=$profileCloseAllCalls, closeAllMs=${profileCloseAllTimeNs/1000000}, substCount=$profileCloseAllSubstCount, setupMs=${profileCloseAllSetupNs/1000000}, unifyMs=${profileCloseAllUnifyNs/1000000}, postMs=${profileCloseAllPostNs/1000000}, filterMs=${profileCloseAllFilterNs/1000000}")
        i += 1
      }
    }
    proof.map((p, n) => (p, n, nf))
  }

  def solve(sequent: K.Sequent): Option[SCProof] = {
    // Apply SInE relevance filtering for large problems (>30 axioms)
    val leftSeq = sequent.left.toSeq
    val rightSeq = sequent.right.toSeq
    val negGoals = rightSeq.map(f => K.neg(f))
    val useFiltering = leftSeq.size > 30 && rightSeq.nonEmpty
    val (filteredLeft, wasFiltered) = if useFiltering then
      val selected = sineFilter(leftSeq, rightSeq)
      val fl = selected.map(leftSeq)
      if fl.nonEmpty && fl.size < leftSeq.size * 3 / 4 then
        if debug then pr(s"  SInE: ${leftSeq.size} -> ${fl.size} axioms (${leftSeq.size - fl.size} filtered)")
        (fl, true)
      else (leftSeq, false)
    else
      (leftSeq, false)
    
    // Try filtered version first (with half the total time budget to leave room for fallback)
    val filteredSequent = if wasFiltered then K.Sequent(filteredLeft.toSet, sequent.right) else sequent
    val solveStart = System.currentTimeMillis()
    val result = solveFormula(filteredLeft ++ negGoals)
    val filteredElapsed = System.currentTimeMillis() - solveStart

    // Fallback: if SInE filtered and no proof found, retry with full problem
    // Give fallback the same amount of time as the filtered attempt used (but at least 10s)
    val (finalResult, finalFiltered, finalFilteredSequent) = result match
      case Some(_) => (result, wasFiltered, filteredSequent)
      case None if wasFiltered =>
        if debug then pr(s"  SInE fallback: retrying with full ${leftSeq.size} axioms")
        val fallbackBudgetMs = math.max(10000L, filteredElapsed)
        (solveFormula(leftSeq ++ negGoals, System.currentTimeMillis() + fallbackBudgetMs), false, sequent)
      case None => (None, false, sequent)

    finalResult match
      case None => None
      case Some((p, _, nf)) =>
        val scProof = if finalFiltered then
          SCProof((Weakening(sequent, p.length + 1) :: Restate(finalFilteredSequent, p.length) :: Weakening(nf |- (), p.length - 1) :: p).reverse.toIndexedSeq, IndexedSeq.empty)
        else
          SCProof((Restate(sequent, p.length) :: Weakening(nf |- (), p.length - 1) :: p).reverse.toIndexedSeq, IndexedSeq.empty)
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
      negByHead: Map[Expression, Set[Expression]] = Map.empty, // negative atoms indexed by head predicate
      posByHead: Map[Expression, Set[Expression]] = Map.empty, // positive atoms indexed by head predicate
      posMetaVars: Set[Variable] = Set.empty, // metavariables appearing in positive atoms (cached)
      negMetaVars: Set[Variable] = Set.empty  // metavariables appearing in negative atoms (cached)
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
        val newMetas = scala.collection.mutable.HashSet[Variable]()
        collectMetaVars(f, unifiable, newMetas)
        this.copy(atoms = (atoms._1, atoms._2 + f),
          negByHead = negByHead.updated(head, negByHead.getOrElse(head, Set.empty) + f),
          negMetaVars = if newMetas.isEmpty then negMetaVars else negMetaVars ++ newMetas)
      case _ =>
        val head = headPred(f)
        val newMetas = scala.collection.mutable.HashSet[Variable]()
        collectMetaVars(f, unifiable, newMetas)
        this.copy(atoms = (atoms._1 + f, atoms._2),
          posByHead = posByHead.updated(head, posByHead.getOrElse(head, Set.empty) + f),
          posMetaVars = if newMetas.isEmpty then posMetaVars else posMetaVars ++ newMetas)

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
   * Like substituteVariables but returns the same object reference when no substitution applies.
   * Avoids creating new Application objects for ground subexpressions, reducing GC pressure.
   */
  private def substOpt(e: Expression, m: Map[Variable, Expression]): Expression =
    e match
      case v: Variable => m.getOrElse(v, v)
      case _: Constant => e
      case app @ Application(f, arg) =>
        val newF = substOpt(f, m)
        val newArg = substOpt(arg, m)
        if (newF eq f) && (newArg eq arg) then app
        else Application(newF, newArg)
      case _ => substituteVariables(e, m) // Lambda: fallback to kernel (capture avoidance)

  /**
   * Collect metavariables (variables in unifiable) that appear in an expression.
   * More efficient than e.freeVariables.filter(unifiable.contains) because it uses
   * a mutable set and avoids creating intermediate Set objects at each tree level.
   */
  private def collectMetaVars(e: Expression, unifiable: Map[Variable, ?], result: scala.collection.mutable.Set[Variable]): Unit = e match
    case v: Variable => if unifiable.contains(v) then result += v
    case _: Constant => ()
    case Application(f, a) => collectMetaVars(f, unifiable, result); collectMetaVars(a, unifiable, result)
    case Lambda(_, body) => collectMetaVars(body, unifiable, result)

  /**
   * Quick check: can two atoms possibly unify based on top-level constant arguments?
   * Returns false if any argument position has two different constants (guaranteed unification failure).
   * This avoids calling the full unify() for obviously incompatible atom pairs.
   */
  private def topLevelCompatible(e1: Expression, e2: Expression): Boolean = (e1, e2) match
    case (Application(f1, a1), Application(f2, a2)) =>
      val argsOk = (a1, a2) match
        case (c1: Constant, c2: Constant) => c1 == c2
        case _ => true // at least one non-constant → might unify
      argsOk && topLevelCompatible(f1, f2)
    case (c1: Constant, c2: Constant) => c1 == c2
    case _ => true

  /**
   * Enhanced compatibility check that also detects ground Variable (Skolem constant) mismatches.
   * In LISA, Skolem constants are Variables with low indices (id.no <= maxIndex) that are NOT
   * in the unifiable map. Two such ground variables at the same argument position can never
   * unify, so their atoms can be skipped. Also detects ground Variable vs Constant mismatches
   * (these are different expression types and can never be equal).
   * Used within closeAll where unifiable/maxIndex context is available.
   */
  private def deepCompatible(e1: Expression, e2: Expression,
      unifiable: Map[Variable, (Expression, Int)], maxIndex: Int): Boolean =
    def isGround(v: Variable): Boolean = !unifiable.contains(v) && v.id.no <= maxIndex
    (e1, e2) match
      case (Application(f1, a1), Application(f2, a2)) =>
        val argsOk = (a1, a2) match
          case (c1: Constant, c2: Constant) => c1 == c2
          case (v1: Variable, v2: Variable) => !(isGround(v1) && isGround(v2) && v1 != v2)
          case (v: Variable, _: Constant) => !isGround(v) // ground var can't match constant
          case (_: Constant, v: Variable) => !isGround(v) // ground var can't match constant
          case _ => true
        argsOk && deepCompatible(f1, f2, unifiable, maxIndex)
      case (c1: Constant, c2: Constant) => c1 == c2
      case (v1: Variable, v2: Variable) => !(isGround(v1) && isGround(v2) && v1 != v2)
      case (v: Variable, _: Constant) => !isGround(v)
      case (_: Constant, v: Variable) => !isGround(v)
      case _ => true

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
      val newt2 = if current.isEmpty then t2 else substOpt(t2, current)
      if occursIn(x, newt2) then Iterator.empty
      else if (current.contains(x)) unify(current(x), newt2, current, br)
      else Iterator.single(current + (x -> newt2))
    case (t1: Expression, y: Variable) if br.unifiable.contains(y) || y.id.no > br.maxIndex =>
      val newt1 = if current.isEmpty then t1 else substOpt(t1, current)
      if occursIn(y, newt1) then Iterator.empty
      else if (current.contains(y)) unify(newt1, current(y), current, br)
      else Iterator.single(current + (y -> newt1))
    case (Application(f1, a1), Application(f2, a2)) =>
      unify(f1, f2, current, br).flatMap(s => unify(a1, a2, s, br))
    case _ => if t1 == t2 then Iterator.single(current) else Iterator.empty

  /**
   * Option-based unification: returns Some(substitution) or None.
   * Avoids Iterator/flatMap allocation overhead since unification is deterministic (0 or 1 results).
   */
  private def unifyOpt(t1: Expression, t2: Expression, current: Substitution, br: Branch): Option[Substitution] = (t1, t2) match
    case (x: Variable, y: Variable) if (br.unifiable.contains(x) || x.id.no > br.maxIndex) && (br.unifiable.contains(y) || y.id.no > br.maxIndex) =>
      if x == y then Some(current)
      else if current.contains(x) then unifyOpt(current(x), t2, current, br)
      else if current.contains(y) then unifyOpt(t1, current(y), current, br)
      else
        if x.id.no > y.id.no then Some(current + (x -> y))
        else Some(current + (y -> x))
    case (x: Variable, t2: Expression) if br.unifiable.contains(x) || x.id.no > br.maxIndex =>
      val newt2 = if current.isEmpty then t2 else substOpt(t2, current)
      if occursIn(x, newt2) then None
      else if current.contains(x) then unifyOpt(current(x), newt2, current, br)
      else Some(current + (x -> newt2))
    case (t1: Expression, y: Variable) if br.unifiable.contains(y) || y.id.no > br.maxIndex =>
      val newt1 = if current.isEmpty then t1 else substOpt(t1, current)
      if occursIn(y, newt1) then None
      else if current.contains(y) then unifyOpt(newt1, current(y), current, br)
      else Some(current + (y -> newt1))
    case (Application(f1, a1), Application(f2, a2)) =>
      unifyOpt(f1, f2, current, br) match
        case Some(s) => unifyOpt(a1, a2, s, br)
        case None => None
    case _ => if t1 == t2 then Some(current) else None

  /**
   * Detect if two atoms can be unified, and if so, return a substitution that unifies them.
   */
  def unifyPred(pos: Expression, neg: Expression, br: Branch): Iterator[Substitution] = {
    assert(pos.sort == Prop && neg.sort == Prop)
    unify(pos, neg, Substitution.empty, br)

  }

  /**
   * Option-based atom unification. Returns Some(substitution) or None.
   * Preferred in closeAll for performance (avoids Iterator allocation).
   */
  private def unifyPredOpt(pos: Expression, neg: Expression, br: Branch): Option[Substitution] = {
    unifyOpt(pos, neg, Substitution.empty, br)
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
    // Quick pre-check: skip closeAll if no positive atom head matches any negative atom head
    val matchingHeads = branch.posByHead.keySet.intersect(branch.negByHead.keySet)
    if matchingHeads.isEmpty && !branch.atoms._1.contains(bot) then return Nil

    val tSetup = if debug then System.nanoTime() else 0L
    // Use cached metavar sets for shared-var computation (incremental, no full-atom-set scan)
    val sharedVars = branch.posMetaVars.intersect(branch.negMetaVars)
    val newMap = sharedVars.iterator
      .map(v => v -> Variable(Identifier(v.id.name, v.id.no + branch.maxIndex + 1), Ind))
      .toMap
    val inverseNewMap = newMap.map((k, v) => v -> k).toMap

    // Check for ⊥ in positive atoms (before rename; ⊥ has no variables so rename is a no-op)
    if branch.atoms._1.contains(bot) then return List((Substitution.empty, Set(bot)))

    val negByHead = branch.negByHead
    val tUnify = if debug then System.nanoTime() else 0L

    // Adaptive caps based on number of metavariables
    val nUnifiable = branch.unifiable.size
    val maxSubstitutions = if nUnifiable > 10 then 30 else 100
    val closeAllDeadlineNs = System.nanoTime() + (if nUnifiable > 6 then 3_000_000L else 5_000_000L)
    var result: List[(Substitution, Set[Expression])] = Nil
    var rawCount = 0
    var done = false

    // Iterate all positive atoms with lazy rename: only substOpt atoms that have matching negative heads
    for (posOrig <- branch.atoms._1.iterator if !done) {
      val pHead = headPred(posOrig) // headPred is invariant under variable rename
      val negCandidates = negByHead.getOrElse(pHead, Set.empty)
      if (negCandidates.nonEmpty) then
        val p = if newMap.isEmpty then posOrig else substOpt(posOrig, newMap)
        for (n <- negCandidates if !done) {
          rawCount += 1
        // Check deadline every 32 pairs (regardless of whether unification succeeded)
        // This ensures the time budget is enforced even when all unifications fail.
        if (rawCount & 31) == 0 && System.nanoTime() > closeAllDeadlineNs then { done = true }
        else if !deepCompatible(p, n, branch.unifiable, branch.maxIndex) then ()
        else {
          lazy val resolvedSet = Set(p, !n).map(f => substOpt(f, inverseNewMap))
          val sOpt = unifyPredOpt(p, n, branch)
          if sOpt.isDefined && !done then {
            val s = sOpt.get
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
                val needsComposed = inverseNewMap.valuesIterator.exists(v => s.contains(v))
                val resolveMap = if needsComposed then inverseNewMap.map((v, t) => v -> substOpt(t, s)) else inverseNewMap
                val resolvedSubst = s.flatMap((v, t) =>
                  if inverseNewMap.contains(v) then
                    if t == inverseNewMap(v) then None
                    else Some(inverseNewMap(v) -> substOpt(t, resolveMap))
                  else if newMap.contains(v) && t == newMap(v) then None
                  else Some(v -> substOpt(t, inverseNewMap))
                )
                if resolvedSubst.nonEmpty
                  && resolvedSubst.forall((v, _) => branch.unifiable.contains(v) && branch.varsOrder.contains(v))
                  && !resolvedSubst.exists((x, t) =>
                    branch.triedInstantiation.contains(x) && branch.triedInstantiation(x).contains(t))
                then
                  result = (resolvedSubst, resolvedSet) :: result
                  if result.size >= maxSubstitutions then done = true
          }
        } // end topLevelCompatible else
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
        // Heavily penalize metavar-to-metavar bindings: these are "renaming" substitutions
        // that don't ground anything. Grounding substitutions (target is a constant/Skolem)
        // should be tried first since they make more progress toward branch closure.
        case x: Variable => if branch.unifiable.contains(x) || x.id.no > branch.maxIndex then 100 + branch.unifiable.getOrElse(x, (null, 0))._2 else 0
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
   * Fully decompose all alpha (And) and delta (Exists) formulas on a branch.
   * Returns a branch with only beta, gamma, and atomic formulas remaining.
   * Used to pre-decompose the NNF for ground saturation initialization,
   * ensuring GS uses the same Skolem constants as the main solver.
   */
  private def decomposeAlphaDelta(branch: Branch): Branch = {
    var current = branch
    var changed = true
    while (changed) {
      changed = false
      while (current.alpha.nonEmpty) {
        current = alpha(current)
        changed = true
      }
      while (current.delta.nonEmpty) {
        val rec = delta(current)
        current = rec._1
        changed = true
      }
    }
    current
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
        val newInner = substOpt(body, Map(v -> newV))
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
            val newBody = substOpt(body, Map(v -> newBound))
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
  // Depth counter for concrete probes: prevents deep cascading (probe within probe within probe...)
  // which causes exponential time consumption on biconditional-heavy problems.
  // Probing allowed at depth 0 (top-level) and 1 (one level nested), disabled at depth 2+.
  private val probeDepth = new ThreadLocal[Int] {
    override def initialValue(): Int = 0
  }
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
    if (decideBudget.decrementAndGet() < 0 || System.currentTimeMillis() > levelDeadline.get() || Thread.currentThread().isInterrupted) return None
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

    // Defer beta splitting when there are gamma formulas not yet expanded at all.
    // This ensures definition atoms are on the branch BEFORE beta splitting,
    // enabling much better unit propagation for biconditional-heavy problems (SET, SEU, GEO).
    val hasFirstTimeGamma = branch.gamma.nonEmpty && branch.gamma.exists {
      case Forall(v, _) => branch.numberInstantiated.getOrElse(v, -1) == -1
      case _ => false
    }

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
    else {
      // Early unification closure: before beta processing, check if the branch can already close
      // via metavariable instantiation. This avoids exploring exponential beta trees when a
      // unification-based closure exists at the current point.
      // Only activate when: many betas (big tree savings), no pending gammas, and match potential exists.
      val earlyClose = if (branch.beta.size >= 4 && !hasFirstTimeGamma && branch.gamma.isEmpty
                           && branch.unifiable.nonEmpty
                           && branch.atoms._1.nonEmpty && branch.atoms._2.nonEmpty
                           && branch.posByHead.keySet.exists(branch.negByHead.contains))
        then tryInstantiations(branch, 3) else None
      if earlyClose.isDefined then earlyClose
      else if (branch.beta.nonEmpty && !hasFirstTimeGamma) then { // Beta AFTER all gammas expanded once
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
      } // end beta processing block
      else if (branch.gamma.nonEmpty) then { // If branch contains a Gamma formula (LeftForall)
      // Gamma selection: when hasFirstTimeGamma, prefer unexpanded formulas to get definitions
      // on the branch before beta splitting. Then apply connection-guided selection within that set.
      val posHeads = branch.atoms._1.map(headPred)
      val negHeads = branch.atoms._2.map(headPred)
      val selectedBranch = {
        // Step 1: If deferring beta (hasFirstTimeGamma), select an unexpanded gamma first
        val afterUnexpandedPriority = if hasFirstTimeGamma then
          val unexpanded = branch.gamma.find {
            case Forall(v, _) => branch.numberInstantiated.getOrElse(v, -1) == -1
            case _ => false
          }
          unexpanded match
            case Some(f) if f.uniqueNumber != branch.gamma.head.uniqueNumber =>
              branch.copy(gamma = f :: branch.gamma.filterNot(_.uniqueNumber == f.uniqueNumber))
            case _ => branch
        else branch
        // Step 2: Connection-guided selection (refine within current head candidates)
        if posHeads.isEmpty && negHeads.isEmpty then afterUnexpandedPriority
        else afterUnexpandedPriority.gamma.find(f => f match
          case Forall(_, body) => hasConnectionToAtoms(body, posHeads, negHeads)
          case _ => false
        ) match
          case Some(f) if f.uniqueNumber != afterUnexpandedPriority.gamma.head.uniqueNumber =>
            afterUnexpandedPriority.copy(gamma = f :: afterUnexpandedPriority.gamma.filterNot(_.uniqueNumber == f.uniqueNumber))
          case _ => afterUnexpandedPriority
      }

      // Early close attempt: try to close using existing atoms and metavariables
      // BEFORE expanding more gamma formulas. This helps problems with many gamma formulas
      // (e.g., KRS/DL problems with 60+ definitional axioms) by finding proofs without
      // needing to expand all gammas first.
      // Only activate for large gamma lists to avoid overhead on simple problems.
      if branch.gamma.size > 30 && branch.unifiable.size >= 3 && branch.atoms._1.nonEmpty && branch.atoms._2.nonEmpty then
        val earlyClose = tryInstantiations(branch, 3)
        if earlyClose.isDefined then return earlyClose

      val hints = groundHints.get()
      // Try concrete gamma instantiation with ground terms (budget-limited probe)
      var concreteResult: Option[(List[SCProofStep], Int)] = None
      // Probe when: (1) first expansion with budget, OR (2) many hint terms available (forward-chaining problem)
      // Probing is gated by probeDepth to prevent cascading: probes within probes waste budget
      // without finding proofs. Only probe at depth 0 (top-level) and 1 (one nested level).
      val currentProbeDepth = probeDepth.get()
      val isFirstExpansion = selectedBranch.numberInstantiated.getOrElse(
        selectedBranch.gamma.head match { case Forall(v, _) => v; case _ => null }, -1) == -1
      val hasHints = groundHints.get().contains(selectedBranch.gamma.head.uniqueNumber)
      val hintCount = groundHints.get().values.map(_.size).sum
      val isForwardChaining = hasHints && hintCount > 80
      val canProbe = (isFirstExpansion || isForwardChaining) && concreteGammaBudget.get() > 0 && currentProbeDepth < 2
      val groundTerms = if canProbe then collectGroundTerms(selectedBranch) else Set.empty[Expression]
      // Connection-guided terms: extract terms from gamma body that match branch atoms.
      val connectionTerms = if canProbe then
        selectedBranch.gamma.head match
          case Forall(v, body) => extractConnectionTerms(v, body, selectedBranch)
          case _ => Nil
      else Nil
      // Ground saturation hints: terms discovered by forward chaining preprocessing.
      // Note: GS hint terms use GS-internal Skolem constants (index >= 100000) which are 
      // in a different namespace from the main solver's delta-decomposed constants. Filter
      // out terms containing GS-only variables since they won't match branch atoms.
      val rawHintTerms = if canProbe && hints.nonEmpty then
        hints.getOrElse(selectedBranch.gamma.head.uniqueNumber, Nil)
      else Nil
      val maxSolverIdx = selectedBranch.maxIndex
      def containsGsSkolem(e: Expression): Boolean = e match
        case v: Variable => v.id.no >= 100000 && v.id.no > maxSolverIdx
        case Application(f, a) => containsGsSkolem(f) || containsGsSkolem(a)
        case _ => false
      val hintTerms = rawHintTerms.filterNot(containsGsSkolem)
      // Priority: connection terms first (from main solver context, always correct),
      // then filtered hint terms, then general ground terms.
      val allProbeTerms = {
        val seen = scala.collection.mutable.Set.empty[Long]
        val result = scala.collection.mutable.ListBuffer.empty[Expression]
        val orderedTerms = connectionTerms ++ hintTerms ++ groundTerms.toList
        for (t <- orderedTerms if result.size < 16) {
          if (seen.add(t.uniqueNumber)) result += t
        }
        result.toList
      }
      if allProbeTerms.nonEmpty then
        selectedBranch.gamma.head match
          case Forall(v, body) =>
            // Scale probe budget based on remaining work: more pending gammas/deltas = deeper proof needed
            // When many hints are available (forward-chaining), allow more budget
            val pendingWork = selectedBranch.gamma.size + selectedBranch.delta.size
            val concreteProbeMaxBudget = if isForwardChaining then 2000
              else if pendingWork <= 5 then 600 else if pendingWork <= 15 then 300 else 150
            val concreteProbeMaxTime = if isForwardChaining then 500L
              else if pendingWork <= 5 then 150L else if pendingWork <= 15 then 80L else 40L
            val maxProbeTerms = if isForwardChaining then 16 else if pendingWork <= 10 then 12 else 8
            val gIter = allProbeTerms.iterator.take(maxProbeTerms)
            val savedBudget = decideBudget.get()
            val savedDeadline = levelDeadline.get()
            concreteGammaBudget.decrementAndGet() // consume one probe from the per-level budget
            while (concreteResult.isEmpty && gIter.hasNext && decideBudget.get() > 0 && System.currentTimeMillis() < savedDeadline) {
              val term = gIter.next()
              val concBody = substOpt(body, Map(v -> term))
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
              probeDepth.set(currentProbeDepth + 1)
              val probeResult = decide(concBranch)
              probeDepth.set(currentProbeDepth)
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
      } // end gamma processing block
      else // No more alpha/delta/beta/gamma — try instantiation strategies
        tryInstantiations(branch, 15)
    } // End of else block with early unification closure
    // End of decide
  }

  /**
   * Try to close a branch by finding unification-based substitutions and applying them.
   * This is called both from the bottom of decide() (after all formulas are decomposed)
   * and from the gamma section (early close attempt to avoid unnecessary gamma expansion).
   */
  private def tryInstantiations(branch: Branch, maxAttempts: Int): Option[(List[SCProofStep], Int)] = {
    var result: Option[(List[SCProofStep], Int)] = None
    val t0 = if debug then System.nanoTime() else 0L
    // Skip closeAll when no metavariables appear in atoms (unification can't bind anything beyond ground closure)
    val allClosingSubsts = if branch.unifiable.isEmpty || (branch.posMetaVars.isEmpty && branch.negMetaVars.isEmpty) then Nil else closeAll(branch)
    if debug then { profileCloseAllCalls += 1; profileCloseAllTimeNs += System.nanoTime() - t0 }

    if allClosingSubsts.nonEmpty then
      val sorted = allClosingSubsts.sortBy(s => substitutionScore(s._1, branch))
      var attempts = 0
      // Adaptive: reduce backtracking when budget is low to enable broader tree exploration
      val budgetRemaining = decideBudget.get()
      val effectiveMaxAttempts = math.min(maxAttempts, math.max(3, budgetRemaining / 1000))
      val iter = sorted.iterator
      while (result.isEmpty && iter.hasNext && attempts < effectiveMaxAttempts) {
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

  /**
   * Like matchBody but treats all non-v variables as wildcards.
   * Useful for multi-variable gamma formulas where inner quantifier variables
   * should be ignored during connection matching.
   */
  private def matchBodyPartial(pattern: Expression, v: Variable, target: Expression): Option[Expression] = {
    var result: Option[Expression] = null
    def go(p: Expression, t: Expression): Boolean = (p, t) match
      case (pv: Variable, _) if pv == v =>
        result match
          case null => result = Some(t); true
          case Some(prev) => prev == t
          case None => false
      case (pv: Variable, _) => true // treat other variables as wildcards
      case (pc: Constant, tc: Constant) => pc == tc
      case (Application(pf, pa), Application(tf, ta)) => go(pf, tf) && go(pa, ta)
      case _ => false
    if go(pattern, target) then result match
      case null => None
      case Some(t) => Some(t)
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
   * Count how many atom connections a formula body has.
   * Higher score = more predicates shared with current branch atoms.
   */
  private def connectionScore(body: Expression, posHeads: Set[Expression], negHeads: Set[Expression]): Int = body match
    case And(l, r) => connectionScore(l, posHeads, negHeads) + connectionScore(r, posHeads, negHeads)
    case Or(l, r) => connectionScore(l, posHeads, negHeads) + connectionScore(r, posHeads, negHeads)
    case Exists(_, inner) => connectionScore(inner, posHeads, negHeads)
    case Forall(_, inner) => connectionScore(inner, posHeads, negHeads)
    case Neg(inner) => if posHeads.contains(headPred(inner)) then 1 else 0
    case _ => if negHeads.contains(headPred(body)) then 1 else 0

  /**
   * Flatten nested And into a list of conjuncts.
   * And(A, And(B, C)) => [A, B, C]
   */
  private def flattenAnd(e: Expression): List[Expression] = e match
    case And(l, r) => flattenAnd(l) ++ flattenAnd(r)
    case _ => List(e)

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
    case And(_, _) =>
      // For conjunctions as disjuncts (from biconditional rewriting), check if any conjunct closes
      val conjuncts = flattenAnd(f)
      val bestConjunctScore = conjuncts.iterator.map(c => disjunctClosureScore(c, atoms, negByHead)).min
      if bestConjunctScore == 0 then 1 // slightly more expensive than raw ground closure (alpha decomposition needed)
      else 2 // complex, needs expansion
    case Or(_, _) | Exists(_, _) | Forall(_, _) => 2 // complex formula, needs further expansion
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
      case Application(f, a) =>
        extract(a) ++ (if f.sort != Ind then extract(f) else Set.empty)
      case _ => Set.empty
    (branch.atoms._1.flatMap(extract) ++ branch.atoms._2.flatMap(extract)).toSet
  }

  /**
   * Extract candidate instantiation terms for a gamma variable by finding connections
   * between the gamma body's atoms and existing branch atoms.
   *
   * For a gamma ∀v. body(v), this walks the body (already in NNF) to find atoms:
   * - Negated body atoms ¬P(v,...) → need P(t,...) on positive branch → match against atoms._1
   * - Positive body atoms P(v,...) → need ¬P(t,...) on negative branch → match against atoms._2
   *
   * Uses matchBody to extract the term that v should be instantiated with.
   * Returns terms ordered by number of connections (most connections first).
   */
  private def extractConnectionTerms(v: Variable, body: Expression, branch: Branch): List[Expression] = {
    // Extract atoms from NNF body with their negation status
    // (innerAtom, isNegated): isNegated=true means body has ¬innerAtom
    // Recurse into nested quantifiers so multi-variable gamma formulas find connections
    def extractAtoms(e: Expression): List[(Expression, Boolean)] = e match
      case And(l, r) => extractAtoms(l) ++ extractAtoms(r)
      case Or(l, r) => extractAtoms(l) ++ extractAtoms(r)
      case Neg(inner) => List((inner, true))
      case Forall(_, inner) => extractAtoms(inner) // recurse into nested quantifiers
      case Exists(_, inner) => extractAtoms(inner)
      case _ if e.sort == Prop => List((e, false))
      case _ => Nil

    val bodyAtoms = extractAtoms(body)
    if bodyAtoms.isEmpty then return Nil

    val termCounts = scala.collection.mutable.Map[Expression, Int]()

    for ((atom, isNegated) <- bodyAtoms) do
      // isNegated: body has ¬atom → will go to atoms._2 → close with atoms._1
      // !isNegated: body has atom → will go to atoms._1 → close with atoms._2
      val branchAtoms = if isNegated then branch.atoms._1 else branch.atoms._2
      val atomHead = headPred(atom)
      for (ba <- branchAtoms if headPred(ba) == atomHead) do
        matchBody(atom, v, ba) match
          case Some(t) => termCounts(t) = termCounts.getOrElse(t, 0) + 1
          case None =>
            // Fallback: try partial matching (wildcards for non-v variables)
            // This is needed for nested gammas ∀A∀B∀C.body(A,B,C) where inner
            // bound variables won't match branch constants exactly.
            matchBodyPartial(atom, v, ba) match
              case Some(t) => termCounts(t) = termCounts.getOrElse(t, 0) + 1
              case None => ()

    // Sort by connection count (most connections first), then return
    termCounts.toList.sortBy(-_._2).map(_._1)
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
    substOpt(f, Map(x -> t))
}
