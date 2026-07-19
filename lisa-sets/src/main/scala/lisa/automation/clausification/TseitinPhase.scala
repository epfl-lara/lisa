package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

private[clausification] object TseitinPhase:

  /** `∀v_0...∀v_{n-1}. body` (innermost-first foldRight). */
  def quantifyAll(body: Expression, vars: Seq[Variable]): Expression =
    vars.foldRight(body)((v, acc) => forall(Lambda(v, acc)))

  /** `λv_0...λv_{n-1}. body` (innermost-first foldRight). */
  def lambdifyAll(body: Expression, vars: Seq[Variable]): Expression =
    vars.foldRight(body)((v, acc) => Lambda(v, acc))

  /** Lift `n` quantifiers onto the LHS of a sequent via [[LeftForall]] (innermost first).
    *
    * Given a step at `srcRef` with bot `equiv |- rhsFormula`, append `n = freeVars.size`
    * `LeftForall` steps to `builder`, producing successively
    * `∀v_{n-1}. equiv |- rhsFormula`, ..., `quantified |- rhsFormula`. Returns the
    * index of the final lifted step in `builder`. */
  def liftLeftForall(
      builder: scala.collection.mutable.ArrayBuffer[SCProofStep],
      srcRef: Int,
      freeVars: Seq[Variable],
      innerLeft: Expression,
      rhsFormula: Expression
  ): Int = {
    val n = freeVars.size
    var ref = srcRef
    var body = innerLeft
    for (k <- 0 until n) {
      val v = freeVars(n - 1 - k)
      val phi = body
      val nextBody = forall(Lambda(v, body))
      builder += LeftForall(Sequent(Set(nextBody), Set(rhsFormula)), ref, phi, v, v)
      ref = builder.size - 1
      body = nextBody
    }
    ref
  }

  /** Bridge subproof producing `() ⊢ tsRewrite` from `() ⊢ phi` and `() ⊢ quantified`.
    *
    * Imports (in order):
    *   - `axImported = () ⊢ phi`
    *   - `quantifiedImported = () ⊢ quantified`
    *
    * Algorithm:
    *   - [[RightSubstIff]] uses the local `equiv` (about to be derived from quantified)
    *     to rewrite `phi` (containing `subst`) into `tsRewrite` (containing `tsApp`),
    *     producing `equiv ⊢ tsRewrite`.
    *   - [[LeftForall]] × |fv| lifts `equiv` to `quantified`, giving `quantified ⊢ tsRewrite`.
    *   - [[Cut]] against the quantified import discharges `quantified`.
    */
  def proveTsRewriteFromQuantified(
      axImported: Sequent,
      tseitin: TseitinStep
  ): SCProof = {
    val phi        = singleRightFormula(axImported, "Tseitin axiom")
    val tsRewrite  = tseitin.tsRewrite
    val equiv      = tseitin.tsApp <=> tseitin.subst
    val quantified = quantifyAll(equiv, tseitin.freeVars)
    val nFv        = tseitin.freeVars.size
    // Pre-size: 0=Restate, 1=RightSubstIff, 2..2+nFv-1=LeftForall×nFv, 2+nFv=Restate, 2+nFv+1=Cut
    val steps = new scala.collection.mutable.ArrayBuffer[SCProofStep](4 + nFv)
    // 0: bring ax into the proof
    steps += Restate(() |- phi, -1)
    // 1: RightSubstIff to rewrite subst → tsApp
    steps += RightSubstIff(
      Sequent(Set(equiv), Set(tsRewrite)),
      0,
      Seq((tseitin.subst, tseitin.tsApp)),
      (Seq(tseitin.hole), tseitin.contextBody)
    )
    // 2..n+1: LeftForall × |fv| to lift equiv to quantified
    val liftedRef = liftLeftForall(steps, 1, tseitin.freeVars, equiv, tsRewrite)
    // n+2: bring quantified import
    val quantImportRef = steps.size
    steps += Restate(() |- quantified, -2)
    // n+3: Cut against quantified
    steps += Cut(() |- tsRewrite, quantImportRef, liftedRef, quantified)

    SCProof(steps.toIndexedSeq, IndexedSeq(axImported, () |- quantified))
  }

  /** Bridge subproof producing `() ⊢ newClause` from `() ⊢ quantified`.
    *
    * The new clause is a Tseitin definitional clause: for AND case `subst = a ∧ b`,
    * either `¬tsApp ∨ a` or `¬tsApp ∨ b`; for OR case, `¬tsApp ∨ a ∨ b`. We prove
    * the corresponding tautology with `subst` in place of `tsApp` (using
    * [[Hypothesis]]/[[LeftAnd]]/[[RightNot]]/[[RightOr]]), then [[RightSubstIff]] to
    * rewrite `subst → tsApp`, then [[LeftForall]] × |fv| to lift `equiv` to
    * `quantified`, then [[Cut]] to discharge `quantified`.
    *
    * `sideExpr` is `a` (or `b`) for the AND case, or `subst` itself for the OR case
    * (since the OR case rewrites the whole `a ∨ b` into `tsApp`, leaving the disjunction
    * literal-flat on the right).
    */
  def proveNewClauseFromQuantified(
      newClauseLiterals: Seq[Expression],
      tseitin: TseitinStep,
      sideExpr: Expression
  ): SCProof = {
    val tsApp      = tseitin.tsApp
    val subst      = tseitin.subst
    val equiv      = tsApp <=> subst
    val quantified = quantifyAll(equiv, tseitin.freeVars)
    val nFv        = tseitin.freeVars.size
    // Pre-size: tautology steps (3 or 4) + RightSubstIff + nFv LeftForall + Restate + Cut + Restate
    val steps = new scala.collection.mutable.ArrayBuffer[SCProofStep](8 + nFv)

    // Build a tautology proof of `() ⊢ ¬subst ∨ sideExpr`.
    val negSubst = neg(subst)
    val tautRhs  = or(negSubst)(sideExpr)

    if (tseitin.isAndCase) {
      // subst = a ∧ b. Goal: () ⊢ ¬(a ∧ b) ∨ sideExpr  (sideExpr is `a` or `b`).
      steps += Hypothesis(sideExpr |- sideExpr, sideExpr)
      val (phiPart, psiPart) =
        if (isSame(sideExpr, tseitin.leftSide)) (tseitin.leftSide, tseitin.rightSide)
        else (tseitin.rightSide, tseitin.leftSide)
      steps += LeftAnd(subst |- sideExpr, 0, phiPart, psiPart)
      steps += RightNot(Sequent(Set.empty, Set(sideExpr, negSubst)), 1, subst)
      steps += RightOr(() |- tautRhs, 2, negSubst, sideExpr)
    } else {
      // subst = a ∨ b. Goal: () ⊢ ¬(a ∨ b) ∨ (a ∨ b)  (sideExpr == subst).
      steps += Hypothesis(subst |- subst, subst)
      steps += RightNot(Sequent(Set.empty, Set(subst, negSubst)), 0, subst)
      steps += RightOr(() |- tautRhs, 1, negSubst, subst)
    }

    val tautRef = steps.size - 1
    // RightSubstIff: rewrite (¬subst ∨ sideExpr) into (¬tsApp ∨ sideExpr).
    val rewritten = or(neg(tsApp))(sideExpr)
    steps += RightSubstIff(
      Sequent(Set(equiv), Set(rewritten)),
      tautRef,
      Seq((subst, tsApp)),
      (Seq(tseitin.hole), or(neg(tseitin.hole))(sideExpr))
    )
    val rewrittenRef = steps.size - 1

    // LeftForall × |fv| to lift equiv to quantified.
    val liftedRef = liftLeftForall(steps, rewrittenRef, tseitin.freeVars, equiv, rewritten)

    // Bring quantified import in, then Cut.
    val quantImportRef = steps.size
    steps += Restate(() |- quantified, -1)
    steps += Cut(() |- rewritten, quantImportRef, liftedRef, quantified)

    // Final Restate to bring `rewritten` to the requested clause shape
    // (set-of-literals on RHS). OL handles associativity/commutativity.
    steps += Restate(Sequent(Set.empty, newClauseLiterals.toSet), steps.size - 1)

    SCProof(steps.toIndexedSeq, IndexedSeq(() |- quantified))
  }

  /** Closed proof of `() ⊢ ∀fv. (subst ⇔ subst)`. Used to discharge the
    * quantified-iff assumption after [[InstSchema]] turns it reflexive. */
  def proveQuantifiedReflIff(subst: Expression, freeVars: Seq[Variable]): SCProof = {
    // 0: Hypothesis(subst |- subst)
    // 1: RightImplies: () |- subst → subst
    // 2: RightIff: () |- subst ⇔ subst
    // 3..n+2: RightForall × |fv| (innermost first)
    val n = freeVars.size
    val totalSteps = 3 + n
    val steps = new Array[SCProofStep](totalSteps)
    steps(0) = Hypothesis(subst |- subst, subst)
    val implFormula = implies(subst)(subst)
    steps(1) = RightImplies(() |- implFormula, 0, subst, subst)
    val iffFormula = subst <=> subst
    steps(2) = RightIff(() |- iffFormula, 1, 1, subst, subst)
    var body: Expression = iffFormula
    var ref = 2
    for (k <- 0 until n) {
      val v = freeVars(n - 1 - k)
      val phi = body
      body = forall(Lambda(v, body))
      steps(3 + k) = RightForall(() |- body, ref, phi, v)
      ref = 3 + k
    }
    SCProof(steps.toIndexedSeq, IndexedSeq.empty)
  }

  /** Flat cross-axiom Tseitin certifier: pre-processes every axiom (running `tseitinStep` until clausal), gathers
    * ALL `Q = ∑ K_i` quantified-iff assumptions into ONE outer [[ClausificationSubproof]], then discharges them in a
    * single block of `Q` InstSchema/refl/Cut triples. Gathering across axioms keeps proof size linear (one
    * [[Weakening]] block per import instead of one per nested level): each axiom's `K_i` Tseitin IFFs are discharged
    * latest-first, and cross-axiom order is irrelevant because a Tseitin variable from one axiom never appears in
    * another axiom's `subst` (each axiom is processed with a private starting position in [[tseitinStep]]). */
  def certifyTseitin(problem: Problem, prover: ClausificationProver): ClausificationProof = {
    require(problem.conjecture.isEmpty, "certifyTseitin expects a conjecture-free problem (consumed by certifyNegated)")
    val counter = Counter()
    val outerImports: IndexedSeq[Sequent] = problem.hypotheses.toIndexedSeq ++ libImports
    val n = problem.hypotheses.size
    val L = libImports.size

    // Per-axiom Tseitin data, in original axiom order.
    final case class AxData(
        axIdx: Int,                          // index into problem.hypotheses
        ax: Sequent,                          // original `() |- phi`
        tseitins: IndexedSeq[TseitinStep],    // possibly empty (already clausal)
        newClauseSeqs: IndexedSeq[Sequent],   // flat across all K
        finalSeq: Sequent                     // residual clause in literal-set form: Sequent(∅, {literals})
    )

    val allAxData: IndexedSeq[AxData] = problem.hypotheses.zipWithIndex.map { case (ax, i) =>
      checkInterrupted()
      val phi = singleRightFormula(ax, "axiom")
      val buf = scala.collection.mutable.ArrayBuffer.empty[TseitinStep]
      var current: Expression = phi
      var continue = true
      while (continue) {
        checkInterrupted()
        tseitinStep(current, counter, problem.frozen) match
          case None    => continue = false
          case Some(t) => buf += t; current = t.tsRewrite
      }
      val tseitins = buf.toIndexedSeq
      val newClauseSeqs = tseitins.flatMap(_.newClauses).map(lits => Sequent(Set.empty, lits.toSet)).toIndexedSeq
      // The residual top-level clause (the untouched axiom when K=0, else the last Tseitin rewrite) is
      // emitted in the SAME literal-set form as the Tseitin new-clauses, so every clause handed to the
      // prover is uniform: a `Sequent(∅, {literals})` with negatives written `¬A`. The proof bridges the
      // original `() ⊢ formula` to this set form with a single `Restate` (see `clauseSetRef` below).
      val finalFormula = if (tseitins.isEmpty) phi else tseitins.last.tsRewrite
      val finalSeq = Sequent(Set.empty, clauseLiterals(finalFormula).toSet)
      AxData(i, ax, tseitins, newClauseSeqs, finalSeq)
    }.toIndexedSeq

    val flatTseitins: IndexedSeq[TseitinStep] = allAxData.flatMap(_.tseitins)
    val Q = flatTseitins.size

    // Final clausal problem for the downstream prover, in interleaved axiom order:
    // for each axiom either the original axiom (if already clausal) or its newClauses
    // followed by its final rewritten form.
    val finalAxioms: IndexedSeq[Sequent] = allAxData.flatMap { ad =>
      if (ad.tseitins.isEmpty) IndexedSeq(ad.finalSeq)
      else ad.newClauseSeqs ++ IndexedSeq(ad.finalSeq)
    }
    val newProblem = Problem(finalAxioms.toList, None, problem.frozen)

    // Bridge the proof of a residual clause (proved in `curSeq` form) to its literal-set `litSeq` with a
    // single `Restate`, appended to `buf`; a no-op returning `ref` when they already coincide (unit clause).
    def clauseSetRef(buf: scala.collection.mutable.ArrayBuffer[ClausificationProofStep], ref: Int, curSeq: Sequent, litSeq: Sequent): Int =
      if (curSeq == litSeq) ref
      else { buf += KernelStep(Restate(litSeq, ref)); buf.size - 1 }

    // Fast path: no Tseitin work at all (every axiom already clausal). Each axiom is still restated into
    // literal-set form (only when multi-literal), then the prover proof is wrapped in one subproof so the
    // outer imports remain the user hypotheses.
    if (Q == 0) {
      val downstream = prover(newProblem)
      require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
      val steps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
      val axRefs = allAxData.map(ad => clauseSetRef(steps, -(ad.axIdx + 1), ad.ax, ad.finalSeq))
      steps += ClausificationSubproof(downstream, axRefs.toIndexedSeq ++ libRefs(n))
      return ClausificationProof(steps.toIndexedSeq, outerImports)
    }

    val quantifieds: IndexedSeq[Expression] = flatTseitins.map(t => quantifyAll(t.tsApp <=> t.subst, t.freeVars))

    // ── Inner ClausificationProof (under Q local assumptions) ────────────────
    // Inner imports layout (indices in `innerImports`):
    //   [0..n-1]              problem.hypotheses    ← inner ref -(i+1)
    //   [n..n+L-1]            libImports            ← inner ref -(n+k+1)
    //   [n+L..n+L+Q-1]        quantifieds           ← inner ref -(n+L+j+1)
    val innerImports: IndexedSeq[Sequent] =
      problem.hypotheses.toIndexedSeq ++ libImports ++ quantifieds.map(q => () |- q)
    def innerAxRef(i: Int): Int   = -(i + 1)
    def innerLibRef(k: Int): Int  = -(n + k + 1)
    def innerQuantRef(j: Int): Int = -(n + L + j + 1)

    val innerSteps   = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val finalAxRefs  = scala.collection.mutable.ArrayBuffer.empty[Int]   // matches `finalAxioms` order

    var jBase = 0  // running base into flatTseitins
    for (ad <- allAxData) {
      checkInterrupted()
      if (ad.tseitins.isEmpty) {
        finalAxRefs += clauseSetRef(innerSteps, innerAxRef(ad.axIdx), ad.ax, ad.finalSeq)
      } else {
        // (1) New-clause sub-proofs for this axiom.
        for (k <- ad.tseitins.indices) {
          val ts = ad.tseitins(k)
          val sideExprs: IndexedSeq[Expression] =
            if (ts.isAndCase) IndexedSeq(ts.leftSide, ts.rightSide) else IndexedSeq(ts.subst)
          ts.newClauses.zip(sideExprs).foreach { case (lits, sideExpr) =>
            val sp = proveNewClauseFromQuantified(lits, ts, sideExpr)
            finalAxRefs += innerSteps.size
            innerSteps += KernelStep(SCSubproof(sp, IndexedSeq(innerQuantRef(jBase + k))))
          }
        }
        // (2) Chain of K rewrite sub-proofs from this axiom's import.
        var prevAxRef: Int = innerAxRef(ad.axIdx)
        var prevAxBot: Sequent = ad.ax
        var lastRewriteRef = -1
        for (k <- ad.tseitins.indices) {
          val ts = ad.tseitins(k)
          val sp = proveTsRewriteFromQuantified(prevAxBot, ts)
          lastRewriteRef = innerSteps.size
          innerSteps += KernelStep(SCSubproof(sp, IndexedSeq(prevAxRef, innerQuantRef(jBase + k))))
          prevAxRef = lastRewriteRef
          prevAxBot = () |- ts.tsRewrite
        }
        // `prevAxBot` now proves `() ⊢ last.tsRewrite`; restate it into `ad.finalSeq`'s literal-set form.
        finalAxRefs += clauseSetRef(innerSteps, lastRewriteRef, prevAxBot, ad.finalSeq)
        jBase += ad.tseitins.size
      }
    }

    // (3) Final downstream prover call.
    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    val recPremises: IndexedSeq[Int] = finalAxRefs.toIndexedSeq ++ (0 until L).map(innerLibRef)
    innerSteps += ClausificationSubproof(downstream, recPremises)
    val innerProof = ClausificationProof(innerSteps.toIndexedSeq, innerImports)

    // ── Outer ClausificationProof: ONE csub holding all Q assumptions, then Q
    //    InstSchema/refl/Cut packages discharging them latest-first. ───────────
    // csub.bot = innerProof.conclusion +<< quantified_0 +<< ... +<< quantified_{Q-1}
    val csubPremises: IndexedSeq[Int] = negRange(0, n) ++ negRange(n, L)
    val assumptions: IndexedSeq[Assumption] =
      (0 until Q).toIndexedSeq.map(j => Assumption(quantifieds(j), n + L + j))
    val csub = ClausificationSubproof(innerProof, csubPremises, assumptions)

    val outerSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    outerSteps += csub
    val rhs: Set[Expression] = csub.bot.right
    // Use a mutable HashSet for currentLhs so that each discharge iteration performs
    // an O(1) remove+add instead of allocating a new immutable Set (which would be
    // O(log Q) with path-copying, and O(Q log Q) total for the Q-iteration loop).
    val mutableLhs = scala.collection.mutable.HashSet.from(csub.bot.left)
    var prevBotRef: Int = 0
    // Discharge Q assumptions, latest-introduced first. Each tsi_j only appears in
    // quantifieds(j) at this point: assumptions for j' < j were created BEFORE
    // tsi_j existed (so cannot mention it), and assumptions for j' > j have already
    // been discharged.
    for (j <- (Q - 1) to 0 by -1) {
      checkInterrupted()
      val ts          = flatTseitins(j)
      val schemaSubst = Map(ts.tsi -> lambdifyAll(ts.subst, ts.freeVars))
      // Optimisation: `ts.tsi` is fresh and unique, so only `quantifieds(j)` in
      // `currentLhs` contains it.  Compute the substituted LHS by directly replacing
      // the one affected formula instead of applying `substSequent` to every formula
      // (the naive approach would be O(Q) per iteration = O(Q²) total).
      val quantReflFormula = substituteVariablesOpti(quantifieds(j), schemaSubst)
      mutableLhs -= quantifieds(j)
      mutableLhs += quantReflFormula
      val instLhs     = mutableLhs.toSet  // snapshot for the immutable Sequent
      val instBot     = Sequent(instLhs, rhs)
      outerSteps     += KernelStep(InstSchema(instBot, prevBotRef, schemaSubst))
      val instRef     = outerSteps.size - 1
      outerSteps     += KernelStep(SCSubproof(proveQuantifiedReflIff(ts.subst, ts.freeVars), IndexedSeq.empty))
      val reflRef     = outerSteps.size - 1
      mutableLhs -= quantReflFormula
      val cutLhs      = mutableLhs.toSet  // snapshot for the immutable Sequent
      val cutBot      = Sequent(cutLhs, rhs)
      outerSteps     += KernelStep(Cut(cutBot, reflRef, instRef, quantReflFormula))
      prevBotRef      = outerSteps.size - 1
    }

    ClausificationProof(outerSteps.toIndexedSeq, outerImports)
  }

  /**
    * Result of one Tseitin step on a formula.
    *
    *   - `tsRewrite`    : original formula with the chosen subformula `subst`
    *                      (a binary AND/OR with two literal-clause sides)
    *                      replaced by the fresh Tseitin application `tsApp`.
    *   - `newClauses`   : clauses defining `tsApp` as the chosen connector applied
    *                      to its sides; each clause is a list of literals (the
    *                      multi-formula RHS form `⊢ {l₁, l₂, …}`).
    *   - `tsi`          : fresh schematic [[Variable]] of sort `s_1 -> ... -> s_n -> Prop`
    *                      where `s_i` are the sorts of the free variables of `subst`.
    *                      Schematic so that [[InstSchema]] can later substitute it.
    *   - `freeVars`     : the free variables of `subst`, in the order applied to `tsi`.
    *   - `tsApp`        : `tsi(freeVars_0)...(freeVars_{n-1})`.
    *   - `subst`        : the original `g op h` subformula being abstracted.
    *   - `hole`         : a fresh propositional [[Variable]] used as substitution hole.
    *   - `contextBody`  : original formula with `subst` replaced by `hole` (the lambda
    *                      body for [[RightSubstIff]]).
    *   - `isAndCase`    : `true` if the abstracted connector is `∧`, `false` if `∨`.
    *   - `leftSide`     : `g`, the left operand of the abstracted connector.
    *   - `rightSide`    : `h`, the right operand of the abstracted connector.
    */
  case class TseitinStep(
      tsRewrite: Expression,
      newClauses: Seq[Seq[Expression]],
      tsi: Variable,
      freeVars: Seq[Variable],
      tsApp: Expression,
      subst: Expression,
      hole: Variable,
      contextBody: Expression,
      isAndCase: Boolean,
      leftSide: Expression,
      rightSide: Expression
  )

  /**
    * Single-step Tseitin: locates the deepest connector with literal-clause children
    * and replaces it with a fresh schematic Tseitin atom application, returning the
    * rewritten formula together with the freshly generated clauses and all the data
    * needed to certify the step (see [[TseitinStep]]). Returns None if `f` is already
    * a clause.
    */
  def tseitinStep(f: Expression, counter: Counter, frozen: Set[Variable] = Set.empty): Option[TseitinStep] = {
    checkInterrupted()
    case class Hit(
        contextBody: Expression,
        subst: Expression,
        tsi: Variable,
        freeVars: Seq[Variable],
        tsApp: Expression,
        hole: Variable,
        isAndCase: Boolean,
        leftSide: Expression,
        rightSide: Expression
    )

    def hit(g: Expression, h: Expression, isAnd: Boolean): Hit = {
      val sub = if (isAnd) and(g)(h) else or(g)(h)
      val (tsi, freeVars, tsApp) = freshTseitinAtom(sub, counter, frozen)
      val hole = Variable(Identifier(s"_th${counter.next()}", 0), Prop)
      Hit(hole, sub, tsi, freeVars, tsApp, hole, isAnd, g, h)
    }

    def descend(g: Expression): Option[Hit] =
      def bin(g1: Expression, g2: Expression, isAnd: Boolean): Option[Hit] =
        val op: (Expression, Expression) => Expression = if isAnd then and(_)(_) else or(_)(_)
        descend(g1).map(h => h.copy(contextBody = op(h.contextBody, g2)))
          .orElse(descend(g2).map(h => h.copy(contextBody = op(g1, h.contextBody))))
          .orElse(Some(hit(g1, g2, isAnd)))
      g match
        case _ if isClause(g) => None
        case And(g1, g2)      => bin(g1, g2, isAnd = true)
        case Or(g1, g2)       => bin(g1, g2, isAnd = false)
        case _                => None

    descend(f).map { h =>
      val tsRewrite = substituteVariablesOpti(h.contextBody, Map(h.hole -> h.tsApp))
      val newClauses: Seq[Seq[Expression]] =
        if h.isAndCase then
          Seq(neg(h.tsApp) +: clauseLiterals(h.leftSide),
              neg(h.tsApp) +: clauseLiterals(h.rightSide))
        else
          Seq(neg(h.tsApp) +: (clauseLiterals(h.leftSide) ++ clauseLiterals(h.rightSide)))
      TseitinStep(
        tsRewrite, newClauses,
        h.tsi, h.freeVars, h.tsApp, h.subst, h.hole, h.contextBody, h.isAndCase, h.leftSide, h.rightSide
      )
    }
  }

  def isLiteral(f: Expression): Boolean = f match
    case Neg(g) => isAtom(g)
    case _      => isAtom(f)

  def isAtom(f: Expression): Boolean = f match
    case `top` | `bot` => true
    case Neg(_) | And(_, _) | Or(_, _) | Implies(_, _) | Iff(_, _) | Forall(_, _) | Exists(_, _) => false
    case _ => f.sort == Prop

  def isClause(f: Expression): Boolean = f match
    case Or(g, h) => isClause(g) && isClause(h)
    case other    => isLiteral(other)

  def clauseLiterals(f: Expression): Seq[Expression] = f match
    case Or(g, h) => clauseLiterals(g) ++ clauseLiterals(h)
    case lit      => Seq(lit)

  /** Build a fresh schematic Tseitin atom over `f`'s free variables.
    *
    * Returns `(tsi, freeVars, tsApp)` where:
    *   - `tsi` is a fresh [[Variable]] (NOT a [[Constant]]) of sort
    *     `s_1 -> ... -> s_n -> Prop` so that [[InstSchema]] can later substitute
    *     it with a Lambda body.
    *   - `freeVars = [v_1, ..., v_n]` are the free variables of `f` in a fixed order.
    *   - `tsApp = tsi(v_1)...(v_n)` is the application that replaces `f` in the
    *     rewritten formula.
    */
  def freshTseitinAtom(f: Expression, counter: Counter, frozen: Set[Variable] = Set.empty): (Variable, Seq[Variable], Expression) = {
    // Only the Ind-sorted free variables are abstracted into `tsi` — higher-sorted
    // free variables (e.g. predicate or function variables like `P : Ind → Prop`)
    // cannot be `forall`-quantified by the kernel, so they remain free in the
    // iff/quantified definitional context (acting as opaque parameters). They are
    // still substituted correctly by [[InstSchema]] since `tsi` is fresh and
    // substituting it cannot capture any other free variable.
    // `frozen` variables (Skolem-function symbols from [[SkolemPhase]]) are excluded too: they are uninterpreted
    // constants pinned by a defining equality, so a nullary one (Ind-sorted) must NOT be ∀-closed here either.
    val freeVars = f.freeVariables.toSeq.filter(v => v.sort == Ind && !frozen.contains(v)).sortBy(_.id.toString)
    val tsId = Identifier(s"Ts${counter.next()}", 0)
    val tsSort = freeVars.foldRight(Prop: Sort)((v, acc) => v.sort -> acc)
    val tsi = Variable(tsId, tsSort)
    val tsApp = freeVars.foldLeft(tsi: Expression)((acc, v) => acc(v))
    (tsi, freeVars, tsApp)
  }
