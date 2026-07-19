package lisa.automation.clausification
import lisa.utils.K
import lisa.utils.K.{_, given}

/** Certified clausification for Lisa, following the SC-TPTP pipeline structure.
  *
  * The reusable proof IR (`ClausificationProof`, `ClausificationSubproof`,
  * lowering, etc.) lives in [[ProofIR]] (same package). This module hosts the
  * clausification-specific certification pipeline. */
object Clausification {

  // ─────────────────────────────────────────────────────────────────────────────
  // Library theorem statements used by the certified bridges.
  //
  // The clausification proof uses these as *imports*, to be discharged later by
  // the corresponding library theorem when the pipeline is wrapped as a tactic.
  // They are kept in fixed positions at the *end* of the proof's imports list,
  // so that bridge subproofs can reference them by stable negative indices.
  // ─────────────────────────────────────────────────────────────────────────────

  /** Schema variable `P` of sort `Ind → Prop` appearing in the library statements. */
  private[clausification] val schemaP: Variable = Variable(Identifier("P", 0), Ind >>: Prop)
  private[clausification] val schemaQ: Variable = Variable(Identifier("Q", 0), Ind >>: Prop)
  private val schemaX: Variable = Variable(Identifier("x", 0), Ind)

  /** Statement of `lisa.maths.Quantifiers.existsEpsilonIff`: `() ⊢ ∃(λx.P(x)) ⇔ P(ε(λx.P(x)))`. */
  val existsEpsilonIffStatement: Sequent = {
    val lambdaPx = Lambda(schemaX, schemaP(schemaX))
    () |- (exists(lambdaPx) <=> schemaP(epsilon(lambdaPx)))
  }

  // Prenex-lifting equivalences (∀ commutes with ∧/∨ over a closed side).
  // Each matches one of the four [[LiftLayer]] cases.
  val forallAndLeftStatement: Sequent  = () |- (and(forall(Lambda(schemaX, schemaP(schemaX))))(schemaQ(schemaX)) <=> forall(Lambda(schemaX, and(schemaP(schemaX))(schemaQ(schemaX)))))
  val forallAndRightStatement: Sequent = () |- (and(schemaP(schemaX))(forall(Lambda(schemaX, schemaQ(schemaX)))) <=> forall(Lambda(schemaX, and(schemaP(schemaX))(schemaQ(schemaX)))))
  val forallOrLeftStatement: Sequent   = () |- (or(forall(Lambda(schemaX, schemaP(schemaX))))(schemaQ(schemaX)) <=> forall(Lambda(schemaX, or(schemaP(schemaX))(schemaQ(schemaX)))))
  val forallOrRightStatement: Sequent  = () |- (or(schemaP(schemaX))(forall(Lambda(schemaX, schemaQ(schemaX)))) <=> forall(Lambda(schemaX, or(schemaP(schemaX))(schemaQ(schemaX)))))

  /** Library imports threaded to every clausification proof, in fixed order. */
  val libImports: IndexedSeq[Sequent] = IndexedSeq(
    existsEpsilonIffStatement,
    forallAndLeftStatement, forallAndRightStatement,
    forallOrLeftStatement,  forallOrRightStatement
  )
  private[clausification] val libExistsEpsilonIffIdx: Int = 0
  private[clausification] val libForallAndLeftIdx: Int    = 1
  private[clausification] val libForallAndRightIdx: Int   = 2
  private[clausification] val libForallOrLeftIdx: Int     = 3
  private[clausification] val libForallOrRightIdx: Int    = 4

  // ─────────────────────────────────────────────────────────────────────────────
  // Data types
  // ─────────────────────────────────────────────────────────────────────────────

  /** Clausification input: imported hypotheses and an optional conjecture.
    *
    * Only the hypotheses become kernel-proof imports — the conjecture is consumed by [[certifyNegated]] (which adds `¬φ`
    * as an extra hypothesis and recurses with `conjecture = None`). All pipeline
    * stages below [[certifyNegated]] therefore see `conjecture = None`. */
  case class Problem(hypotheses: Seq[Sequent], conjecture: Option[Sequent], frozen: Set[Variable] = Set.empty) {
    /** User-facing imports: just the hypotheses. Library imports are threaded
      * separately via [[Clausification.libImports]] and appear at the end of the
      * produced kernel proof's imports. */
    def imports: IndexedSeq[Sequent] = hypotheses.toIndexedSeq

    def hypIndex(i: Int): Int = -(i + 1)
  }
  // `frozen`: free variables introduced upstream (notably Skolem-function symbols from [[SkolemPhase]]) that must be
  // treated as **uninterpreted constants**, NOT universally quantified — downstream phases must never `∀`-close or
  // parameterize a definition over them (their meaning is pinned by a defining-equality assumption instead). Threaded
  // forward through every phase's transformed problem.

  /** Total node count of a kernel expression (variables/constants/applications/lambdas). */
  def formulaSize(e: Expression): Int = e match
    case Application(f, a) => 1 + formulaSize(f) + formulaSize(a)
    case Lambda(_, body)   => 1 + formulaSize(body)
    case _                 => 1

  /** Sum of formula sizes across all sequents in a problem (LHS + RHS, hypotheses + conjecture). */
  def problemSize(p: Problem): Int =
    def seqSize(s: Sequent): Int = s.left.toSeq.map(formulaSize).sum + s.right.toSeq.map(formulaSize).sum
    p.hypotheses.map(seqSize).sum + p.conjecture.fold(0)(seqSize)

  private[clausification] def singleRightFormula(sequent: Sequent, what: String): Expression = {
    require(sequent.left.isEmpty, s"$what must have empty left-hand side, got ${sequent.repr}")
    require(sequent.right.size == 1, s"$what must have a single formula on the right-hand side, got ${sequent.repr}")
    sequent.right.head
  }

  private[clausification] def onSingleRight(sequent: Sequent, what: String)(f: Expression => Expression): Sequent =
    () |- f(singleRightFormula(sequent, what))

  private[clausification] def sameImportList(left: Seq[Sequent], right: Seq[Sequent]): Boolean =
    left.size == right.size && left.zip(right).forall((l, r) => l == r || isSameSequent(l, r))

  /** Negative kernel reference (`-(idx+1)` form) for a library import at `libIdx`
    * within an outer imports list whose first `nonLibSize` entries are non-library
    * imports and last [[libImports.size]] entries are the library imports. */
  private[clausification] def libRef(nonLibSize: Int, libIdx: Int): Int = -(nonLibSize + libIdx + 1)

  /** Negative kernel reference for the [[existsEpsilonIffStatement]] library import. */
  private[clausification] def libIffRef(nonLibSize: Int): Int = libRef(nonLibSize, libExistsEpsilonIffIdx)

  /** References into outer imports for the library imports, in their fixed order. */
  private[clausification] def libRefs(nonLibSize: Int): IndexedSeq[Int] = libImports.indices.map(libRef(nonLibSize, _)).toIndexedSeq

  private[clausification] type ClausificationProver = Problem => ClausificationProof

  /** Apply a [[Variable]]-substitution pointwise to both sides of a sequent. */
  private[clausification] def substSequent(seq: Sequent, subst: Map[Variable, Expression]): Sequent =
    Sequent(seq.left.map(substituteVariables(_, subst)), seq.right.map(substituteVariables(_, subst)))

  /**
   * Re-expand η-reduced quantifier bodies: rewrite `∀(f)` / `∃(f)` (where `f` is **not** a `Lambda`) to
   * `∀(λz. f(z))` / `∃(λz. f(z))`. The kernel's `betaNormalForm` η-reduces `λy. p(x, y)` to `p(x)`, so a
   * `∀y. p(x, y)` can come back as `∀(p(x))` — which the [[Forall]]/[[Exists]] extractors (they require an
   * explicit `Lambda`) no longer recognise, leaving the quantifier stranded as an opaque atom in the clause.
   * Applying this after every `betaNormalForm` restores the `Lambda` form so the phases can strip/skolemize it.
   *
   * '''ε-terms are left untouched''' (not expanded, not descended into): they are Skolem *terms*, abstracted
   * wholesale by the downstream prover and never quantifier-stripped, so expanding their interior would only
   * desync them from the β-normalised (η-reduced) form the prover reconstructs — breaking import matching.
   */
  private[clausification] def etaExpandQuantifiers(e: Expression): Expression =
    def freshEtaVar(free: Set[Variable]): Variable =
      var n = 0
      var z = Variable(Identifier("etaZ", n), Ind)
      while free.contains(z) do { n += 1; z = Variable(Identifier("etaZ", n), Ind) }
      z
    def wrapBinder(binder: Expression, body: Expression): Expression = body match
      case Lambda(v, inner) => binder(Lambda(v, etaExpandQuantifiers(inner)))
      case f =>
        val ef = etaExpandQuantifiers(f)
        val z  = freshEtaVar(ef.freeVariables)
        binder(Lambda(z, ef(z)))
    e match
      case Application(`forall`, body)  => wrapBinder(forall, body)
      case Application(`exists`, body)  => wrapBinder(exists, body)
      case Application(`epsilon`, _)    => e // leave Skolem ε-terms exactly as β-normalisation produced them
      case Application(f, a)            => Application(etaExpandQuantifiers(f), etaExpandQuantifiers(a))
      case Lambda(v, b)                 => Lambda(v, etaExpandQuantifiers(b))
      case _                            => e

  /** Negative kernel references for `n` consecutive imports starting at zero-based `start`. */
  private[clausification] def negRange(start: Int, n: Int): IndexedSeq[Int] =
    (start until start + n).map(i => -(i + 1)).toIndexedSeq

  /** Layout of the recursion-context premises for the certify_* functions.
    *
    * All three (skolem/prenex/tseitin) share the same outer-imports shape after
    * popping one axiom from `notdone`:
    *
    *   outerImports = ax :: rest ++ done ++ libImports
    *
    * The recursive call produces an inner proof whose imports are
    * `rest ++ done ++ libImports`, possibly with a few additional
    * "produced" axioms prepended (e.g. the rewritten one). This captures the
    * common index arithmetic. */
  private[clausification] case class RecCtx(restSize: Int, doneSize: Int) {
    /** Number of non-library outer imports (ax + rest + done). */
    def nonLibSize: Int = 1 + restSize + doneSize
  }

  /** Per-axiom transformation step used by [[certifyAxiomwise]]:
    * given the head axiom and current [[RecCtx]], either return `None` to
    * passthrough or `Some((newAx, prelude, producedIdx))` to inject a new axiom
    * derived by `prelude` (with `producedIdx` selecting the step concluding `newAx`). */
  private[clausification] type AxiomTransform =
    (Sequent, Counter, RecCtx) => Option[(Sequent, IndexedSeq[ClausificationProofStep], Int)]

  /** Generic "pop one axiom, optionally transform, recurse" certifier.
    *
    * Shared scaffold for [[certifySkolem]] and [[certifyPrenex]]. */
  /** Cooperative cancellation hook: throw `InterruptedException` if the
    * current thread has been interrupted, OR if the JVM is dangerously close
    * to OOM (used heap > 90% of max).  The latter is a safety valve so a
    * runaway problem (e.g. an exponential blow-up that allocates faster than
    * `Thread.interrupted()` can be polled) cannot crash the whole bench. */
  private[clausification] inline def checkInterrupted(): Unit = {
    if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled")
    val rt = Runtime.getRuntime
    val used = rt.totalMemory() - rt.freeMemory()
    if (used > (rt.maxMemory() / 10) * 9)
      throw new InterruptedException(s"Memory pressure: heap ${used / (1024*1024)}MB / max ${rt.maxMemory() / (1024*1024)}MB")
  }

  private[clausification] def certifyAxiomwise(
      problem: Problem,
      prover: ClausificationProver,
      transform: AxiomTransform
  ): ClausificationProof = {
    require(problem.conjecture.isEmpty, "certifyAxiomwise expects a conjecture-free problem (consumed by certifyNegated)")
    val counter = Counter()
    val hypotheses = problem.hypotheses.toIndexedSeq
    val n = hypotheses.size
    val outerImports = hypotheses ++ libImports

    // Flat layout: outerImports = [hyp_0, ..., hyp_{n-1}] ++ libImports.
    // For each hypothesis `i`, repeatedly apply `transform` until it returns None;
    // each prelude is inlined into `flatSteps` with reference rewriting:
    //   - `-1` (the transform's view of "current axiom") is rewritten to point either
    //     to the original import `-(i+1)` (first transform) or to the previous
    //     prelude's `producedIdx` step (subsequent transforms).
    //   - `libRef(...)` references are already correct because we use a constant
    //     `nonLibSize = n` matching the flat outer-imports layout.
    //   - Local positive references inside the prelude are offset by the current
    //     `flatSteps.size` at the point of inlining.
    // Finally one [[ClausificationSubproof]] wraps the downstream prover call,
    // mapping each transformed axiom slot to its final step index (or original
    // import ref for passthroughs). This collapses the n nested subproofs of the
    // previous design into a single flat ClausificationProof, eliminating the
    // O(n²) cost of recomputing per-level outer imports and external-import maps.
    val flatSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val finalAxioms = scala.collection.mutable.ArrayBuffer.empty[Sequent]
    val finalAxiomRefs = scala.collection.mutable.ArrayBuffer.empty[Int]
    val flatCtx = RecCtx(restSize = 0, doneSize = n - 1) // only nonLibSize=n is used

    for (i <- 0 until n) {
      checkInterrupted()
      var currentAx: Sequent = hypotheses(i)
      var currentAxRef: Int  = -(i + 1)
      var continue = true
      while (continue) {
        checkInterrupted()
        transform(currentAx, counter, flatCtx) match
          case None =>
            continue = false
          case Some((newAx, prelude, producedIdx)) =>
            val inlineOffset = flatSteps.size
            val axRefForRebase = currentAxRef
            def rebase(ref: Int): Int =
              if (ref >= 0) inlineOffset + ref
              else if (ref == -1) axRefForRebase
              else ref // libRef already correct (nonLibSize == n in both layouts)
            prelude.foreach {
              case KernelStep(step) => flatSteps += KernelStep(mapStepPremises(step, rebase))
              case csub: ClausificationSubproof =>
                flatSteps += csub.copy(premises = csub.premises.map(rebase))
            }
            currentAx = newAx
            currentAxRef = inlineOffset + producedIdx
      }
      finalAxioms += currentAx
      finalAxiomRefs += currentAxRef
    }

    val newProblem = Problem(finalAxioms.toList, None, problem.frozen)
    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    val csubPremises = finalAxiomRefs.toIndexedSeq ++ libRefs(n)
    flatSteps += ClausificationSubproof(downstream, csubPremises)
    ClausificationProof(flatSteps.toIndexedSeq, outerImports)
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Top-level pipeline
  // ─────────────────────────────────────────────────────────────────────────────

  /** Run the full certified clausification pipeline and then call the clausal prover.
    *
    * The returned [[SCProof]] takes, in addition to the user's hypothesis/conjecture
    * imports, the schematic statements of two library theorems
    * ([[lisa.maths.Quantifiers.existsEpsilonIff]] and
    * [[lisa.maths.Quantifiers.forallInstantiation]]) as imports, in fixed order at
    * the end of the imports list. A future tactic wrapping this pipeline can
    * discharge them by cutting against the corresponding library theorems.
    *
    * ==Clausal-prover contract (`prover`)==
    * Established empirically against the composition below (see the superposition prover's
    * `Phase3.md` §9 and `ClausalTest` "probe"). `prover` is called on a conjecture-free clausal
    * [[Problem]] and MUST return an [[SCProof]] such that:
    *  - '''imports''' `== problem.imports` (the clause-sequents), pointwise and in order — the
    *    wrapper appends [[libImports]] and the pipeline asserts `sameImportList` on the result.
    *    (Declare every clause even if the refutation does not use it.)
    *  - '''conclusion''' `== ⊢` (the EMPTY sequent). NOT `{all clause literals} ⊢`: the
    *    [[ClausificationSubproof]] embeds this proof with no assumptions, and [[certifyNegated]]'s
    *    final `Cut` lifts only the negated conjecture `¬φ` to the LHS, so it needs `¬φ ⊢`
    *    (empty RHS) — i.e. the prover proper must derive `⊢`. The `Sorry`-based stub concluding
    *    `{all literals} ⊢` typechecks only because a `Sorry` is not kernel-checked.
    * ==Clause format the prover receives==
    * Every clause is a [[Sequent]] in uniform literal-set form: `Sequent(∅, {literals})` with the
    * literals on the RHS and negatives written `¬A` (no bare disjunctions, no quantifiers — universals
    * are already free variables by the Tseitin stage, and `certifyTseitin` restates each residual
    * axiom/rewrite into set form at the point it is declared clausal). A first-order prover that expects
    * a negative literal's atom on the LHS need only move each `¬A` from the RHS to the LHS as `A`, and
    * bridge each original clause to that working form with a single per-clause `Restate` (which also
    * handles the equivalent left/right placement). No `∀`-strip or `∨`-split is required. */
  def certifyClausal(problem: Problem, prover: Problem => SCProof): SCProof = {
    val wrappedProver: ClausificationProver = p =>
      // The downstream clausal prover only knows about user imports; pad its proof
      // with the library imports at the end so the rest of the pipeline can rely on
      // them being present at stable indices.
      val downstream = ClausificationProof.fromSCProof(prover(p))
      ClausificationProof(downstream.steps, downstream.imports ++ libImports)
    val tseitinProver: ClausificationProver = TseitinPhase.certifyTseitin(_, wrappedProver)
    val prenexProver: ClausificationProver = PrenexPhase.certifyPrenex(_, tseitinProver)
    val skolemProver: ClausificationProver = SkolemPhase.certifySkolem(_, prenexProver)
    val nnfProver: ClausificationProver = NnfPhase.certifyNnf(_, skolemProver)
    val fullProver: ClausificationProver = NegatedPhase.certifyNegated(_, nnfProver)
    lowerClausificationProof(fullProver(problem))
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Pure (uncertified) formula transformations  (helpers for the pipeline)
  // ─────────────────────────────────────────────────────────────────────────────

  /** Like [[lisa.kernel.fol.Syntax.substituteVariables]] but avoids redundant work and
    * heap allocation when parts of the expression tree are unaffected by the substitution:
    *  - `m.isEmpty` guard: if the substitution is empty, returns `e` unchanged (same reference).
    *  - Lambda stripping: when a Lambda binder removes the last key from `m`, the body subtree
    *    is returned as-is without recursion.
    *  - Smart constructors: the result of an Application or Lambda is the original expression `e`
    *    (same reference) when both sub-results are reference-equal to the originals. This avoids
    *    allocating new nodes for unchanged subtrees and lets parent calls short-circuit too.
    *
    * The function is observationally identical to the kernel version on well-sorted inputs.
    */
  private[clausification] def substituteVariablesOpti(e: Expression, m: Map[Variable, Expression]): Expression =
    if (m.isEmpty) e
    else
      // Pre-compute the free variables of all substitution values once at the top level.
      // This set is passed down so that Lambda cases don't recompute it from scratch for
      // every nested binder (which would be O(depth × |m| × value_size) total).
      val fvOfValues: Set[Variable] = m.values.flatMap(_.freeVariables).toSet
      substituteVariablesOptiRec(e, m, fvOfValues)

  private[clausification] def substituteVariablesOptiRec(e: Expression, m: Map[Variable, Expression], fvOfValues: Set[Variable]): Expression =
    e match
      case v: Variable => m.getOrElse(v, v)
      case _: Constant => e
      case Application(f, arg) =>
        val newF   = substituteVariablesOptiRec(f, m, fvOfValues)
        val newArg = substituteVariablesOptiRec(arg, m, fvOfValues)
        if (newF eq f) && (newArg eq arg) then e else Application(newF, newArg)
      case Lambda(v, t) =>
        val newM = m - v
        if (newM.isEmpty) e
        else
          // Remove v from fvOfValues only if v was a key (its value may have had v free).
          // In practice fvOfValues is a conservative over-approximation: we recompute it
          // precisely only when we need to check for capture.
          if fvOfValues.contains(v) then
            // Potential capture: recompute precisely for this binder.
            val newFv = newM.values.flatMap(_.freeVariables).toSet
            if newFv.contains(v) then
              val newV = Variable(freshId(newFv.view.map(_.id) ++ newM.keys.view.map(_.id), v.id), v.sort)
              Lambda(newV, substituteVariablesOptiRec(t, newM + (v -> newV), newFv + newV))
            else
              val newT = substituteVariablesOptiRec(t, newM, newFv)
              if (newT eq t) e else Lambda(v, newT)
          else
            val newT = substituteVariablesOptiRec(t, newM, fvOfValues)
            if (newT eq t) e else Lambda(v, newT)

  // ─────────────────────────────────────────────────────────────────────────────
  // Counter helper
  // ─────────────────────────────────────────────────────────────────────────────

  class Counter(var value: Int = 0) {
    def next(): Int = { val v = value; value += 1; v }
  }
}
