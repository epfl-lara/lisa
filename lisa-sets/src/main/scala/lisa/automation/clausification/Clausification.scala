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
  private val schemaP: Variable = Variable(Identifier("P", 0), Ind >>: Prop)
  private val schemaQ: Variable = Variable(Identifier("Q", 0), Ind >>: Prop)
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
  private val libExistsEpsilonIffIdx: Int = 0
  private val libForallAndLeftIdx: Int    = 1
  private val libForallAndRightIdx: Int   = 2
  private val libForallOrLeftIdx: Int     = 3
  private val libForallOrRightIdx: Int    = 4

  // ─────────────────────────────────────────────────────────────────────────────
  // Data types
  // ─────────────────────────────────────────────────────────────────────────────

  /** Clausification input: imported hypotheses and an optional conjecture.
    *
    * Only the hypotheses become kernel-proof imports — the conjecture is consumed by [[certifyNegated]] (which adds `¬φ`
    * as an extra hypothesis and recurses with `conjecture = None`). All pipeline
    * stages below [[certifyNegated]] therefore see `conjecture = None`. */
  case class Problem(hypotheses: Seq[Sequent], conjecture: Option[Sequent]) {
    /** User-facing imports: just the hypotheses. Library imports are threaded
      * separately via [[Clausification.libImports]] and appear at the end of the
      * produced kernel proof's imports. */
    def imports: IndexedSeq[Sequent] = hypotheses.toIndexedSeq

    def hypIndex(i: Int): Int = -(i + 1)
  }

  private def singleRightFormula(sequent: Sequent, what: String): Expression = {
    require(sequent.left.isEmpty, s"$what must have empty left-hand side, got ${sequent.repr}")
    require(sequent.right.size == 1, s"$what must have a single formula on the right-hand side, got ${sequent.repr}")
    sequent.right.head
  }

  private def onSingleRight(sequent: Sequent, what: String)(f: Expression => Expression): Sequent =
    () |- f(singleRightFormula(sequent, what))

  private def sameImportList(left: Seq[Sequent], right: Seq[Sequent]): Boolean =
    left.size == right.size && left.zip(right).forall((l, r) => l == r || isSameSequent(l, r))

  /** Negative kernel reference (`-(idx+1)` form) for a library import at `libIdx`
    * within an outer imports list whose first `nonLibSize` entries are non-library
    * imports and last [[libImports.size]] entries are the library imports. */
  private def libRef(nonLibSize: Int, libIdx: Int): Int = -(nonLibSize + libIdx + 1)

  /** Negative kernel reference for the [[existsEpsilonIffStatement]] library import. */
  private def libIffRef(nonLibSize: Int): Int = libRef(nonLibSize, libExistsEpsilonIffIdx)

  /** References into outer imports for the library imports, in their fixed order. */
  private def libRefs(nonLibSize: Int): IndexedSeq[Int] = libImports.indices.map(libRef(nonLibSize, _)).toIndexedSeq

  private type ClausificationProver = Problem => ClausificationProof

  /** `∀v_0...∀v_{n-1}. body` (innermost-first foldRight). */
  private def quantifyAll(body: Expression, vars: Seq[Variable]): Expression =
    vars.foldRight(body)((v, acc) => forall(Lambda(v, acc)))

  /** `λv_0...λv_{n-1}. body` (innermost-first foldRight). */
  private def lambdifyAll(body: Expression, vars: Seq[Variable]): Expression =
    vars.foldRight(body)((v, acc) => Lambda(v, acc))

  /** Apply a [[Variable]]-substitution pointwise to both sides of a sequent. */
  private def substSequent(seq: Sequent, subst: Map[Variable, Expression]): Sequent =
    Sequent(seq.left.map(substituteVariables(_, subst)), seq.right.map(substituteVariables(_, subst)))

  /** Negative kernel references for `n` consecutive imports starting at zero-based `start`. */
  private def negRange(start: Int, n: Int): IndexedSeq[Int] =
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
  private case class RecCtx(restSize: Int, doneSize: Int) {
    /** Number of non-library outer imports (ax + rest + done). */
    def nonLibSize: Int = 1 + restSize + doneSize
  }

  /** Build a [[ClausificationProof]] for a passthrough recursive step:
    *
    *   outerImports = ax :: rest ++ done ++ libImports
    *   rec.imports  = rest ++ done ++ Seq(ax) ++ libImports
    *
    * The single subproof maps outer imports into rec's import order. */
  private def passthroughProof(rec: ClausificationProof, ctx: RecCtx, outerImports: IndexedSeq[Sequent]): ClausificationProof = {
    val premises =
      negRange(1, ctx.restSize) ++
        negRange(1 + ctx.restSize, ctx.doneSize) ++
        IndexedSeq(-1) ++
        libRefs(ctx.nonLibSize)
    val csub = ClausificationSubproof(rec, premises)
    ClausificationProof(IndexedSeq(csub), outerImports)
  }

  /** Build a [[ClausificationProof]] for a "produce one new axiom in place of `ax`" step:
    *
    *   outerImports = ax :: rest ++ done ++ libImports
    *   rec.imports  = newAx :: rest ++ done ++ libImports
    *
    * `prelude` are the local steps that derive `newAx`; `producedIdx` is the index
    * of the prelude step concluding `() ⊢ newAx`. */
  private def produceAxiomProof(
      prelude: IndexedSeq[ClausificationProofStep],
      producedIdx: Int,
      rec: ClausificationProof,
      ctx: RecCtx,
      outerImports: IndexedSeq[Sequent]
  ): ClausificationProof = {
    val tailRefs = negRange(1, ctx.restSize + ctx.doneSize)
    val premises = IndexedSeq(producedIdx) ++ tailRefs ++ libRefs(ctx.nonLibSize)
    val csub = ClausificationSubproof(rec, premises)
    ClausificationProof(prelude :+ csub, outerImports)
  }

  /** Per-axiom transformation step used by [[certifyAxiomwise]]:
    * given the head axiom and current [[RecCtx]], either return `None` to
    * passthrough or `Some((newAx, prelude, producedIdx))` to inject a new axiom
    * derived by `prelude` (with `producedIdx` selecting the step concluding `newAx`). */
  private type AxiomTransform =
    (Sequent, Counter, RecCtx) => Option[(Sequent, IndexedSeq[ClausificationProofStep], Int)]

  /** Generic "pop one axiom, optionally transform, recurse" certifier.
    *
    * Shared scaffold for [[certifySkolem]] and [[certifyPrenex]]. */
  /** Cooperative cancellation hook: throw `InterruptedException` if the
    * current thread has been interrupted, OR if the JVM is dangerously close
    * to OOM (used heap > 90% of max).  The latter is a safety valve so a
    * runaway problem (e.g. an exponential blow-up that allocates faster than
    * `Thread.interrupted()` can be polled) cannot crash the whole bench. */
  private inline def checkInterrupted(): Unit = {
    if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled")
    val rt = Runtime.getRuntime
    val used = rt.totalMemory() - rt.freeMemory()
    if (used > (rt.maxMemory() / 10) * 9)
      throw new InterruptedException(s"Memory pressure: heap ${used / (1024*1024)}MB / max ${rt.maxMemory() / (1024*1024)}MB")
  }

  private def certifyAxiomwise(
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

    val newProblem = Problem(finalAxioms.toList, None)
    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    val csubPremises = finalAxiomRefs.toIndexedSeq ++ libRefs(n)
    flatSteps += ClausificationSubproof(downstream, csubPremises)
    ClausificationProof(flatSteps.toIndexedSeq, outerImports)
  }

  /**
    * Build a subproof of `() ⊢ matrix` from the imported `() ⊢ phi`, where `phi`
    * may contain `∀`-quantifiers *anywhere* in the tree (not necessarily at the root).
    * `matrix` is `phi` with every `∀x._` stripped and `x` replaced by the
    * corresponding witness `V_i` (pre-order, as computed by [[extractUniversalMatrix]]).
    *
    * Two strategies, dispatched by [[preferRewriteStrategy]]:
    *   - [[provePrenexDeconstruct]]: walk `phi`'s tree, apply `LeftForall` at each
    *     `∀` node in-place. O(|phi|).
    *   - [[provePrenexRewrite]]: lift each `∀` to the root one connective at a time
    *     via prenex-equivalence rewrites, then strip with `LeftForall`. O(nq × depth). */
  private def provePrenex(
      imported: Sequent,
      premise: Int,
      conclusion: Sequent,
      witnesses: Seq[Variable],
      libPrenexRefs: (Int, Int, Int, Int),
      forceDeconstruct: Boolean = false,
      forceRewrite: Boolean = false
  ): SCSubproof = {
    val phi = singleRightFormula(imported, "imported (prenex source)")
    if (!forceDeconstruct && (forceRewrite || preferRewriteStrategy(phi)))
      provePrenexRewrite(imported, premise, conclusion, witnesses, libPrenexRefs)
    else provePrenexDeconstruct(imported, premise, conclusion, witnesses)
  }

  private def hasForall(f: Expression): Boolean = f match
    case Forall(_, _) => true
    case And(g, h)    => hasForall(g) || hasForall(h)
    case Or(g, h)     => hasForall(g) || hasForall(h)
    case Neg(g)       => hasForall(g)
    case _            => false

  /** Per-formula heuristic deciding between the rewrite and deconstruction prenex
    * strategies.  Returns `true` if [[provePrenexRewrite]] is expected to produce
    * a smaller proof than [[provePrenexDeconstruct]].
    *
    * Currently a coarse global heuristic: pick rewriting when the formula has
    * many leaves but few quantifiers, deconstruction otherwise. */
  private def preferRewriteStrategy(phi: Expression): Boolean = {
    def counts(e: Expression): (Int, Int) = e match // (size, numForall)
      case Forall(_, body) =>
        val (s, q) = counts(body); (s + 1, q + 1)
      case And(g, h) =>
        val (sg, qg) = counts(g); val (sh, qh) = counts(h)
        (sg + sh + 1, qg + qh)
      case Or(g, h) =>
        val (sg, qg) = counts(g); val (sh, qh) = counts(h)
        (sg + sh + 1, qg + qh)
      case Neg(body) =>
        val (s, q) = counts(body); (s + 1, q)
      case _ => (1, 0)
    val (size, nq) = counts(phi)
    // Rewriting is asymptotically O(nq * depth); deconstruction is O(size).
    // Pick rewrite when there are few quantifiers relative to formula size.
    nq > 0 && size > 4 * nq * nq
  }

  /** Deconstruction strategy: build a kernel proof of `phi ⊢ matrix` by walking
    * `phi`'s tree, mirroring its connectives, and using `LeftForall` directly to
    * instantiate each universal at its corresponding witness from `witnesses`
    * (pre-order). Then `Cut` against `imported` to obtain `() ⊢ matrix`.
    *
    * Proof size is linear in `|phi|`. */
  private def provePrenexDeconstruct(
      imported: Sequent,
      premise: Int,
      conclusion: Sequent,
      witnesses: Seq[Variable]
  ): SCSubproof = {
    val phi    = singleRightFormula(imported, "imported (prenex source)")
    val matrix = singleRightFormula(conclusion, "conclusion (prenex matrix)")

    val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
    def emit(s: SCProofStep): Int = { steps += s; steps.size - 1 }

    val witsIter = witnesses.iterator

    // Builds steps with conclusion `orig ⊢ matrixOf(orig)` and returns the step index.
    // Fast path: if `orig` contains no ∀, its matrix is itself — no tree walk needed.
    def go(orig: Expression): Int =
      if !hasForall(orig) then emit(Hypothesis(orig |- orig, orig))
      else orig match
      case Forall(x, body) =>
        require(witsIter.hasNext, "Witness list exhausted while walking universals")
        val v = witsIter.next()
        val bodySub  = substituteVariablesOpti(body, Map(x -> v))
        val innerIdx = go(bodySub)
        val innerM   = steps(innerIdx).bot.right.head
        // LeftForall(b, t1, phi, x, t): from `Γ, body[x:=v] ⊢ Δ` derive `Γ, ∀x.body ⊢ Δ`.
        emit(LeftForall(orig |- innerM, innerIdx, body, x, v))

      case And(g, h) =>
        val gIdx = go(g)
        val hIdx = go(h)
        val mg = steps(gIdx).bot.right.head
        val mh = steps(hIdx).bot.right.head
        val mAnd = and(mg)(mh)
        val gWithAnd = emit(LeftAnd(orig |- mg, gIdx, g, h))
        val hWithAnd = emit(LeftAnd(orig |- mh, hIdx, g, h))
        emit(RightAnd(orig |- mAnd, Seq(gWithAnd, hWithAnd), Seq(mg, mh)))

      case Or(g, h) =>
        val gIdx = go(g)
        val hIdx = go(h)
        val mg = steps(gIdx).bot.right.head
        val mh = steps(hIdx).bot.right.head
        val mOr = or(mg)(mh)
        // RightOr lifts each branch to the disjunctive matrix; LeftOr combines them.
        val gWithOr = emit(RightOr(g |- mOr, gIdx, mg, mh))
        val hWithOr = emit(RightOr(h |- mOr, hIdx, mg, mh))
        emit(LeftOr(orig |- mOr, Seq(gWithOr, hWithOr), Seq(g, h)))

      case _ =>
        // NNF leaves: atoms and negated atoms — Hypothesis suffices.
        emit(Hypothesis(orig |- orig, orig))

    val phiToMatrixIdx = go(phi)
    require(steps(phiToMatrixIdx).bot.right.head == matrix,
      s"Deconstruction produced unexpected matrix: got ${steps(phiToMatrixIdx).bot.right.head}, expected $matrix")
    require(!witsIter.hasNext, "Unused witnesses after walking universals")
    // Cut: from `() ⊢ phi` (import 0) and `phi ⊢ matrix` derive `() ⊢ matrix`.
    emit(Cut(() |- matrix, -1, phiToMatrixIdx, phi))

    SCSubproof(SCProof(steps.toIndexedSeq, IndexedSeq(imported)), IndexedSeq(premise))
  }

  /** Rewriting strategy: for each universal quantifier in `phi` (in pre-order),
    * lift it to the top of the formula via `RightSubstIff` with the appropriate
    * prenex equivalence (proven inline), then strip it with `LeftForall` at the
    * matching witness from `witnesses`. After all quantifiers are stripped, we
    * have `() ⊢ matrix`. The remaining body's structure is never destructured.
    *
    * Cost per quantifier: `O(nb_q*depth)` rewrites (one per enclosing connective on
    * the path from root to the quantifier). */
  /** Description of a single one-layer step lifting `∀x.body` across the
    * surrounding connective when it sits inside `(…) ⊕ Q` or `Q ⊕ (…)`. */
  private sealed trait LiftLayer
  private case class LayerAndL(rhs: Expression) extends LiftLayer  // (∀x.body) ∧ rhs  →  ∀x.(body ∧ rhs)
  private case class LayerAndR(lhs: Expression) extends LiftLayer  // lhs ∧ (∀x.body)  →  ∀x.(lhs ∧ body)
  private case class LayerOrL (rhs: Expression) extends LiftLayer  // (∀x.body) ∨ rhs  →  ∀x.(body ∨ rhs)
  private case class LayerOrR (lhs: Expression) extends LiftLayer  // lhs ∨ (∀x.body)  →  ∀x.(lhs ∨ body)

  private def provePrenexRewrite(
      imported: Sequent,
      premise: Int,
      conclusion: Sequent,
      witnesses: Seq[Variable],
      libPrenexRefs: (Int, Int, Int, Int)
  ): SCSubproof = {
    val phi    = singleRightFormula(imported, "imported (prenex source)")
    val matrix = singleRightFormula(conclusion, "conclusion (prenex matrix)")
    val (outerLibAndL, outerLibAndR, outerLibOrL, outerLibOrR) = libPrenexRefs
    // Inside the inner SCProof, the prenex-lifting library theorems appear as
    // imports 1..4 (0-based), referenced as -2 through -5.
    val innerLibAndL = -2; val innerLibAndR = -3
    val innerLibOrL  = -4; val innerLibOrR  = -5

    val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
    def emit(s: SCProofStep): Int = { steps += s; steps.size - 1 }
    val freshCounter = Counter()

    // Locate the leftmost ∀ in pre-order.  Returns the path (root→quantifier) of
    // one-layer descents, plus the bound variable and body of the ∀ found.
    def locateForall(f: Expression): Option[(List[LiftLayer], Variable, Expression)] = f match
      case Forall(x, body) => Some((Nil, x, body))
      case And(g, h) =>
        locateForall(g).map { case (p, x, b) => (LayerAndL(h) :: p, x, b) }
          .orElse(locateForall(h).map { case (p, x, b) => (LayerAndR(g) :: p, x, b) })
      case Or(g, h) =>
        locateForall(g).map { case (p, x, b) => (LayerOrL(h) :: p, x, b) }
          .orElse(locateForall(h).map { case (p, x, b) => (LayerOrR(g) :: p, x, b) })
      case _ => None

    /** Replace the sub-expression at `path` (relative to root of `f`) using `f0 => f1`. */
    def rewriteAt(f: Expression, path: List[LiftLayer], at: Expression => Expression): Expression =
      path match
        case Nil => at(f)
        case LayerAndL(_) :: rest => f match { case And(g, h) => and(rewriteAt(g, rest, at))(h); case _ => sys.error("path mismatch (∧L)") }
        case LayerAndR(_) :: rest => f match { case And(g, h) => and(g)(rewriteAt(h, rest, at)); case _ => sys.error("path mismatch (∧R)") }
        case LayerOrL(_)  :: rest => f match { case Or(g, h)  => or(rewriteAt(g, rest, at))(h);  case _ => sys.error("path mismatch (∨L)") }
        case LayerOrR(_)  :: rest => f match { case Or(g, h)  => or(g)(rewriteAt(h, rest, at));  case _ => sys.error("path mismatch (∨R)") }

    /** Sub-expression at `path` in `f`. */
    def subAt(f: Expression, path: List[LiftLayer]): Expression =
      path match
        case Nil => f
        case LayerAndL(_) :: rest => f match { case And(g, _) => subAt(g, rest); case _ => sys.error("path mismatch (∧L)") }
        case LayerAndR(_) :: rest => f match { case And(_, h) => subAt(h, rest); case _ => sys.error("path mismatch (∧R)") }
        case LayerOrL(_)  :: rest => f match { case Or(g, _)  => subAt(g, rest); case _ => sys.error("path mismatch (∨L)") }
        case LayerOrR(_)  :: rest => f match { case Or(_, h)  => subAt(h, rest); case _ => sys.error("path mismatch (∨R)") }

    /** Apply one prenex equivalence at `pathToInner` (whose tail describes the
      * single connective layer to cross) inside `srcFormula`, producing a step
      * whose conclusion is `() ⊢ liftedFormula`. */
    def liftOneLayer(
        srcIdx: Int,
        srcFormula: Expression,
        pathToOuter: List[LiftLayer],   // path from root to the ⊕-node containing ∀x.body
        layer: LiftLayer,               // describes which side of ⊕ holds the ∀
        x: Variable,
        body: Expression
    ): (Int, Expression) = {
      val innerForall = forall(Lambda(x, body))
      val (lhsIff, rhsIff): (Expression, Expression) = layer match
        case LayerAndL(rhs) => (and(innerForall)(rhs), forall(Lambda(x, and(body)(rhs))))
        case LayerAndR(lhs) => (and(lhs)(innerForall), forall(Lambda(x, and(lhs)(body))))
        case LayerOrL(rhs)  => (or(innerForall)(rhs),  forall(Lambda(x, or(body)(rhs))))
        case LayerOrR(lhs)  => (or(lhs)(innerForall),  forall(Lambda(x, or(lhs)(body))))

      val iffFormula = lhsIff <=> rhsIff
      // Instantiate the appropriate prenex library theorem to get `() ⊢ iffFormula`.
      val (libRef, schemaSubst): (Int, Map[Variable, Expression]) = layer match
        case LayerAndL(rhs) => (innerLibAndL, Map(schemaP -> Lambda(x, body), schemaQ -> Lambda(x, rhs)))
        case LayerAndR(lhs) => (innerLibAndR, Map(schemaP -> Lambda(x, lhs),  schemaQ -> Lambda(x, body)))
        case LayerOrL(rhs)  => (innerLibOrL,  Map(schemaP -> Lambda(x, body), schemaQ -> Lambda(x, rhs)))
        case LayerOrR(lhs)  => (innerLibOrR,  Map(schemaP -> Lambda(x, lhs),  schemaQ -> Lambda(x, body)))
      val iffStep = emit(InstSchema(() |- iffFormula, libRef, schemaSubst))

      // Lifted formula: replace `lhsIff` at `pathToOuter` with `rhsIff`.
      val liftedFormula = rewriteAt(srcFormula, pathToOuter, _ => rhsIff)

      // Build the context lambda for RightSubstIff: λp. srcFormula[pathToOuter := p].
      val pVar = Variable(Identifier("_p", freshCounter.next()), Prop)
      val ctxBody = rewriteAt(srcFormula, pathToOuter, _ => pVar)

      val substStep = emit(RightSubstIff(
        Sequent(Set(iffFormula), Set(liftedFormula)),
        srcIdx,
        Seq((lhsIff, rhsIff)),
        (Seq(pVar), ctxBody)
      ))
      val cutStep = emit(Cut(() |- liftedFormula, iffStep, substStep, iffFormula))
      (cutStep, liftedFormula)
    }

    // Start by Restating `imported` to obtain `() ⊢ phi` at a known index.
    var currentRefIdx = emit(Restate(() |- phi, -1))
    var currentFormula: Expression = phi
    val witsIter = witnesses.iterator

    // Outer loop: lift one ∀ to the root, then strip it; repeat until no ∀ remains.
    while locateForall(currentFormula).isDefined do
      // Inner loop: while the located ∀ is below the root, lift it one layer.
      var loc = locateForall(currentFormula).get
      while loc._1.nonEmpty do
        val (path, x, body) = loc
        // The ∀-containing ⊕-node is at `path.init`; the final step describes
        // which side the ∀ sits on (and what the sibling is).
        val pathToOuter = path.init
        val finalLayer  = path.last
        val (newIdx, newFormula) = liftOneLayer(currentRefIdx, currentFormula, pathToOuter, finalLayer, x, body)
        currentRefIdx = newIdx
        currentFormula = newFormula
        loc = locateForall(currentFormula).get
      // ∀ is now at the root: strip it.
      require(witsIter.hasNext, "Encountered top-level ∀ but no witness to instantiate")
      val v = witsIter.next()
      val (_, x, body) = loc
      val instantiated = substituteVariables(body, Map(x -> v))
      val hypIdx = emit(Hypothesis(instantiated |- instantiated, instantiated))
      val lfIdx  = emit(LeftForall(currentFormula |- instantiated, hypIdx, body, x, v))
      val cutIdx = emit(Cut(() |- instantiated, currentRefIdx, lfIdx, currentFormula))
      currentRefIdx = cutIdx
      currentFormula = instantiated

    require(!witsIter.hasNext, "Witnesses left over with no ∀ to instantiate")
    require(currentFormula == matrix,
      s"Rewrite produced unexpected matrix: got $currentFormula, expected $matrix")

    // Inner SCProof imports: 0 = `imported` (the source axiom), 1..4 = prenex lib theorems.
    val innerImports = IndexedSeq(imported, forallAndLeftStatement, forallAndRightStatement, forallOrLeftStatement, forallOrRightStatement)
    SCSubproof(
      SCProof(steps.toIndexedSeq, innerImports),
      IndexedSeq(premise, outerLibAndL, outerLibAndR, outerLibOrL, outerLibOrR)
    )
  }

  /**
    * SC-TPTP-style certified Tseitin step helpers.
    *
    * The Tseitin transformation introduces a *fresh* Tseitin atom `tsi(fv)`,
    * abstracting a connector subformula `subst = g op h`. The defining iff
    * `equiv = tsi(fv) ⇔ subst` is NOT a logical theorem (it's a definition).
    * Following the SC-TPTP playbook, we thread the *quantified* iff
    * `quantified = ∀fv. equiv` as a *local assumption* on the LHS of the inner
    * proof (using [[ClausificationSubproof.assumptions]]), and discharge it at
    * the call site via [[InstSchema]] + a closed proof of the trivial
    * reflexive iff `∀fv. (subst ⇔ subst)`.
    */

  /** Lift `n` quantifiers onto the LHS of a sequent via [[LeftForall]] (innermost first).
    *
    * Given a step at `srcRef` with bot `equiv |- rhsFormula`, append `n = freeVars.size`
    * `LeftForall` steps to `builder`, producing successively
    * `∀v_{n-1}. equiv |- rhsFormula`, ..., `quantified |- rhsFormula`. Returns the
    * index of the final lifted step in `builder`. */
  private def liftLeftForall(
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
  private def proveTsRewriteFromQuantified(
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
  private def proveNewClauseFromQuantified(
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
  private def proveQuantifiedReflIff(subst: Expression, freeVars: Seq[Variable]): SCProof = {
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
    * discharge them by cutting against the corresponding library theorems. */
  def certifyClausal(problem: Problem, prover: Problem => SCProof): SCProof = {
    val wrappedProver: ClausificationProver = p =>
      // The downstream clausal prover only knows about user imports; pad its proof
      // with the library imports at the end so the rest of the pipeline can rely on
      // them being present at stable indices.
      val downstream = ClausificationProof.fromSCProof(prover(p))
      ClausificationProof(downstream.steps, downstream.imports ++ libImports)
    val tseitinProver: ClausificationProver = certifyTseitin(_, wrappedProver)
    val prenexProver: ClausificationProver = certifyPrenex(_, tseitinProver)
    val skolemProver: ClausificationProver = certifySkolem(_, prenexProver)
    val nnfProver: ClausificationProver = certifyNnf(_, skolemProver)
    val fullProver: ClausificationProver = certifyNegated(_, nnfProver)
    lowerClausificationProof(fullProver(problem))
  }

  /** Like [[certifyClausal]] but streams each proof step to `pw` as it is
    * produced rather than accumulating the full [[SCProof]] in memory.  This
    * eliminates the peak memory cost of holding all steps simultaneously.
    *
    * File format (one line per record):
    * {{{
    *   # imports: <n>  problem: <name>
    *   import|-1|<sequent.repr>
    *   ...
    *   <global-idx>|<ClassName>|<comma-premises>|<sequent.repr>
    *   ...
    *   # end  steps: <total>
    * }}}
    * Top-level imports are referenced by negative indices in premise lists.
    * Every [[ClausificationSubproof]] is inlined (no SCSubproof wrappers in the
    * file); all step indices are globally monotone.
    *
    * @return total number of flat steps written.
    */
  def certifyClausalFlat(problem: Problem, prover: Problem => SCProof, pw: java.io.PrintWriter): Int = {
    val wrappedProver: ClausificationProver = p =>
      val downstream = ClausificationProof.fromSCProof(prover(p))
      ClausificationProof(downstream.steps, downstream.imports ++ libImports)
    val tseitinProver: ClausificationProver = certifyTseitin(_, wrappedProver)
    val prenexProver: ClausificationProver  = certifyPrenex(_, tseitinProver)
    val skolemProver: ClausificationProver  = certifySkolem(_, prenexProver)
    val nnfProver: ClausificationProver     = certifyNnf(_, skolemProver)
    val fullProver: ClausificationProver    = certifyNegated(_, nnfProver)
    val fullProof = fullProver(problem)
    pw.println(s"# imports: ${fullProof.imports.size}")
    fullProof.imports.zipWithIndex.foreach { case (imp, i) =>
      pw.println(s"import|-${i + 1}|${imp.repr}")
    }
    val sink = new StreamSink(pw)
    val topImportGlobalRefs = IndexedSeq.tabulate(fullProof.imports.size)(i => -(i + 1))
    lowerClausificationProofFlat(fullProof, IndexedSeq.empty, IndexedSeq.empty, topImportGlobalRefs, sink)
    sink.count
  }

  /** Wrap a flat prover so that the pipeline can see the library axiom imports. */
  private def wrapProver(prover: Problem => SCProof): ClausificationProver = p =>
    val downstream = ClausificationProof.fromSCProof(prover(p))
    ClausificationProof(downstream.steps, downstream.imports ++ libImports)

  /** Run only the Tseitin phase (input must be quantifier-free). */
  def certifyTseitinPhase(problem: Problem, prover: Problem => SCProof): SCProof =
    lowerClausificationProof(certifyTseitin(problem, wrapProver(prover)))

  /** Run only the prenex phase on a fully Skolemized problem (no existential quantifiers). */
  def certifyPrenexPhase(problem: Problem, prover: Problem => SCProof): SCProof =
    lowerClausificationProof(certifyPrenex(problem, wrapProver(prover)))

  /** Like [[certifyPrenexPhase]] but forces the deconstruction strategy, bypassing the heuristic. */
  def certifyPrenexDeconstructPhase(problem: Problem, prover: Problem => SCProof): SCProof =
    lowerClausificationProof(certifyPrenex(problem, wrapProver(prover), forceDeconstruct = true))

  /** Like [[certifyPrenexPhase]] but forces the rewrite strategy, bypassing the heuristic. */
  def certifyPrenexRewritePhase(problem: Problem, prover: Problem => SCProof): SCProof =
    lowerClausificationProof(certifyPrenex(problem, wrapProver(prover), forceRewrite = true))

  /** Run only the Skolem phase on a problem in NNF (no implications or double negations). */
  def certifySkolemPhase(problem: Problem, prover: Problem => SCProof): SCProof =
    lowerClausificationProof(certifySkolem(problem, wrapProver(prover)))

  private def certifyNegated(problem: Problem, prover: ClausificationProver): ClausificationProof =
    problem.conjecture match
      case None => prover(problem)
      case Some(conjecture) =>
        val phi = singleRightFormula(conjecture, "conjecture")
        val negPhi = neg(phi)
        val transformed = Problem(problem.hypotheses :+ (() |- negPhi), None)
        val downstream = prover(transformed)
        require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

        // Bridge: Hypothesis(φ ⊢ φ) and RightNot(() ⊢ φ, ¬φ), then cut against the
        // downstream subproof of `() ⊢ ¬φ`.
        val hypStep      = KernelStep(Hypothesis(phi |- phi, phi))
        val rightNotStep = KernelStep(RightNot(() |- (phi, negPhi), 0, phi))
        val csub = ClausificationSubproof(
          downstream,
          problem.hypotheses.indices.map(problem.hypIndex).toIndexedSeq ++ libRefs(problem.imports.size),
          IndexedSeq(Assumption(negPhi, problem.hypotheses.size))
        )
        val cutStep = KernelStep(Cut(() |- phi, 1, 2, negPhi))
        ClausificationProof(IndexedSeq(hypStep, rightNotStep, csub, cutStep), problem.imports ++ libImports)

  private def certifyNnf(problem: Problem, prover: ClausificationProver): ClausificationProof = {
    val transformedHyps = problem.hypotheses.map { h =>
      checkInterrupted()
      onSingleRight(h, "hypothesis")(toNNF(_, negated = false))
    }
    val transformed = Problem(transformedHyps, None)
    val downstream = prover(transformed)
    require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

    val restateSteps: IndexedSeq[ClausificationProofStep] =
      transformedHyps.zipWithIndex.map { case (nnfHyp, i) =>
        KernelStep(Restate(nnfHyp, problem.hypIndex(i)))
      }.toIndexedSeq
    val subproof = ClausificationSubproof(
      downstream,
      restateSteps.indices.toIndexedSeq ++ libRefs(problem.imports.size)
    )
    ClausificationProof(restateSteps :+ subproof, problem.imports ++ libImports)
  }

  private def certifySkolem(problem: Problem, prover: ClausificationProver): ClausificationProof =
    certifyAxiomwise(problem, prover, (ax, counter, ctx) => {
      val phi = singleRightFormula(ax, "axiom")
      skolemizeOne(phi, counter).map { case SkolemStep(skoFormula, bridge) =>
        // Outer steps:
        //   step 0: bridge proof, concluding `phi ⊢ skoFormula`. The bridge takes
        //           [[existsEpsilonIffStatement]] as a single import, supplied here
        //           via [[libIffRef]] into the outer library imports.
        //   step 1: Cut against ax, concluding `() ⊢ skoFormula`.
        val skoaxF     = () |- skoFormula
        val bridgeStep = KernelStep(SCSubproof(bridge, IndexedSeq(libIffRef(ctx.nonLibSize))))
        val cutStep    = KernelStep(Cut(skoaxF, -1, 0, phi))
        (skoaxF, IndexedSeq(bridgeStep, cutStep), 1)
      }
    })

  /** For each axiom containing a `∀` anywhere in its tree, strip all universals and
    * replace each bound variable with a fresh witness `V_i` (pre-order). Certifies
    * the derivation of the quantifier-free matrix via [[provePrenex]]. */
  private def certifyPrenex(problem: Problem, prover: ClausificationProver,
      forceDeconstruct: Boolean = false, forceRewrite: Boolean = false): ClausificationProof = {
    certifyAxiomwise(problem, prover, (ax, counter, ctx) => {
      val phi = singleRightFormula(ax, "axiom")
      if !hasForall(phi) then None
      else
        // Outer step 0 derives matrixAx from ax via universal-quantifier stripping,
        // using `witnesses` (the fresh `V_i` introduced by [[extractUniversalMatrix]]
        // in pre-order) as instantiation terms.
        val (matrix, witnesses) = extractUniversalMatrix(phi, counter)
        val matrixAx   = () |- matrix
        // Lib refs in the outer ClausificationProof (ax :: rest ++ done ++ libImports).
        val prenexLibRefs = (
          libRef(ctx.nonLibSize, libForallAndLeftIdx),
          libRef(ctx.nonLibSize, libForallAndRightIdx),
          libRef(ctx.nonLibSize, libForallOrLeftIdx),
          libRef(ctx.nonLibSize, libForallOrRightIdx)
        )
        val prenexStep = KernelStep(provePrenex(ax, -1, matrixAx, witnesses, prenexLibRefs, forceDeconstruct, forceRewrite))
        Some((matrixAx, IndexedSeq(prenexStep), 0))
    })
  }

  private def certifyTseitin(problem: Problem, prover: ClausificationProver): ClausificationProof =
    certifyTseitinFlat(problem, prover)

  /** Recursive (legacy) Tseitin certifier: one nested [[ClausificationSubproof]] per
    * axiom.  Each level introduces K_i local assumptions for that axiom's Tseitin
    * IFFs. Lowering each csub adds one [[Weakening]] per external import, giving
    * a per-level cost of O(#axioms) and a total cost of O(#axioms²) in proof size.
    *
    * Superseded by [[certifyTseitinFlat]] which gathers ALL Tseitin assumptions
    * across ALL axioms into a single outermost csub, reducing cross-axiom proof
    * size to linear. Kept for reference and ease of reverting. */
  @scala.annotation.unused
  private def certifyTseitinRecursive(problem: Problem, prover: ClausificationProver): ClausificationProof = {
    require(problem.conjecture.isEmpty, "certifyTseitin expects a conjecture-free problem (consumed by certifyNegated)")
    val counter = Counter()

    def innerCertifyTseitin(notdone: List[Sequent], clausal: List[Sequent]): ClausificationProof = {
      val outerImports = (notdone ++ clausal).toIndexedSeq ++ libImports
      notdone match
        case Nil =>
          val newProblem = Problem(clausal, None)
          val downstream = prover(newProblem)
          require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
          downstream
        case ax :: next =>
          val phi = singleRightFormula(ax, "axiom")
          tseitinStep(phi, counter) match
            case None =>
              // Already a clause: move to `clausal`.
              val rec = innerCertifyTseitin(next, clausal :+ ax)
              val ctx = RecCtx(next.size, clausal.size)
              passthroughProof(rec, ctx, outerImports)
            case Some(firstTseitin) =>
              // ── Collect ALL Tseitin sub-steps for this axiom ──────────────────────
              // Iterate `tseitinStep` until the rewritten axiom is clausal; gather every
              // intermediate `TseitinStep`. The chain `tseitins(i).tsRewrite` is the
              // cumulative rewrite of `phi` after applying tseitins(0..i).
              val tseitinsBuf = scala.collection.mutable.ArrayBuffer[TseitinStep](firstTseitin)
              var current: Expression = firstTseitin.tsRewrite
              var continue            = true
              while (continue) {
                tseitinStep(current, counter) match
                  case None    => continue = false
                  case Some(t) => tseitinsBuf += t; current = t.tsRewrite
              }
              val tseitins         = tseitinsBuf.toIndexedSeq
              val K                = tseitins.size
              val ctx              = RecCtx(next.size, clausal.size)
              val nextSize         = ctx.restSize
              val clausalSize      = ctx.doneSize
              val libCount         = libImports.size

              // Final clausal form of phi after all K Tseitin rewrites.
              val tsRewriteFinalSeq: Sequent = () |- tseitins.last.tsRewrite
              // All new definitional clauses produced across the K steps, in order.
              val allNewClauseSeqs: IndexedSeq[Sequent] =
                tseitins.flatMap(_.newClauses).map(lits => Sequent(Set.empty, lits.toSet)).toIndexedSeq
              val totalClauseCount = allNewClauseSeqs.size

              // Quantified-iff assumptions: one per Tseitin step.
              //   quantifieds(i) = ∀fv_i. (tsApp_i ⇔ subst_i)
              val quantifieds: IndexedSeq[Expression] =
                tseitins.map(t => quantifyAll(t.tsApp <=> t.subst, t.freeVars))

              // ── Inner ClausificationProof (under K local assumptions) ────────────
              // Inner imports layout (indices in `innerImports`):
              //   [0..R-1]               next axioms              (R = nextSize)
              //   [R..R+D-1]             clausal_old              (D = clausalSize)
              //   [R+D]                  original ax              (= () |- phi)
              //   [R+D+1..R+D+L]         libImports               (L = libCount)
              //   [R+D+L+1..R+D+L+K]     quantifieds (assumption imports)
              val innerImports: IndexedSeq[Sequent] =
                (next ++ clausal).toIndexedSeq ++
                  IndexedSeq(ax) ++
                  libImports ++
                  quantifieds.map(q => () |- q)
              val innerAxIdx        = nextSize + clausalSize
              val innerLibStart     = innerAxIdx + 1
              val innerQuantStart   = innerLibStart + libCount
              val innerAxRef        = -(innerAxIdx + 1)
              def innerQuantRef(i: Int): Int = -(innerQuantStart + i + 1)

              val innerSteps    = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
              val clauseIndices = scala.collection.mutable.ArrayBuffer.empty[Int]

              // (1) New-clause sub-proofs: for each Tseitin step i, derive each of its
              // newClauses using ONLY the corresponding `quantifieds(i)` assumption.
              for (i <- 0 until K) {
                val ts = tseitins(i)
                val sideExprs: IndexedSeq[Expression] =
                  if ts.isAndCase then IndexedSeq(ts.leftSide, ts.rightSide)
                  else IndexedSeq(ts.subst)
                ts.newClauses.zip(sideExprs).foreach { case (lits, sideExpr) =>
                  val sp = proveNewClauseFromQuantified(lits, ts, sideExpr)
                  clauseIndices += innerSteps.size
                  innerSteps += KernelStep(SCSubproof(sp, IndexedSeq(innerQuantRef(i))))
                }
              }

              // (2) Chain of K rewrite sub-proofs producing the cumulative rewritten
              // axiom. Each step takes the previous result as its `ax` import.
              //   prove_0: () ⊢ phi               + () ⊢ quantified_0  →  () ⊢ tsRewrite_0
              //   prove_1: () ⊢ tsRewrite_0       + () ⊢ quantified_1  →  () ⊢ tsRewrite_1
              //   ...
              //   prove_{K-1}: () ⊢ tsRewrite_{K-2} + () ⊢ quantified_{K-1} →  () ⊢ tsRewriteFinal
              val rewriteIndices = new Array[Int](K)
              var prevAxRef: Int = innerAxRef
              var prevAxBot: Sequent = ax
              for (i <- 0 until K) {
                val ts = tseitins(i)
                val sp = proveTsRewriteFromQuantified(prevAxBot, ts)
                rewriteIndices(i) = innerSteps.size
                innerSteps += KernelStep(SCSubproof(sp, IndexedSeq(prevAxRef, innerQuantRef(i))))
                prevAxRef = rewriteIndices(i)
                prevAxBot = () |- ts.tsRewrite
              }

              // (3) Cross-axiom recursion: process the remaining axioms with the new
              // clauses + final rewritten axiom appended to `clausal` (all clausal).
              val rec = innerCertifyTseitin(next, clausal ++ allNewClauseSeqs.toList ++ List(tsRewriteFinalSeq))
              // rec.imports layout:
              //   [0..R-1]                           next                ← inner [0..R-1]
              //   [R..R+D-1]                         clausal_old         ← inner [R..R+D-1]
              //   [R+D..R+D+C-1]                     allNewClauseSeqs    ← clauseIndices
              //   [R+D+C]                            tsRewriteFinalSeq   ← rewriteIndices(K-1)
              //   [R+D+C+1..R+D+C+L]                 libImports          ← inner [R+D+1..R+D+L]
              val recPremises =
                negRange(0, nextSize) ++
                  negRange(nextSize, clausalSize) ++
                  clauseIndices.toIndexedSeq ++
                  IndexedSeq(rewriteIndices(K - 1)) ++
                  negRange(innerLibStart, libCount)
              innerSteps += ClausificationSubproof(rec, recPremises)
              val innerProof = ClausificationProof(innerSteps.toIndexedSeq, innerImports)

              // ── Outer ClausificationProof: one csub holding all K assumptions, then
              //    K InstSchema/refl/Cut packages discharging them latest-first. ─────
              // csub.bot = innerProof.conclusion +<< quantified_0 +<< ... +<< quantified_{K-1}
              //          = {quantified_0, ..., quantified_{K-1}} ⊢ rec.conclusion.right
              val csubPremises =
                negRange(1, nextSize) ++ negRange(1 + nextSize, clausalSize) ++
                  IndexedSeq(-1) ++
                  libRefs(ctx.nonLibSize)
              val assumptions = (0 until K).toIndexedSeq.map { i =>
                Assumption(quantifieds(i), innerQuantStart + i)
              }
              val csub = ClausificationSubproof(innerProof, csubPremises, assumptions)

              val outerSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
              outerSteps += csub
              val rhs: Set[Expression] = csub.bot.right
              val mutableLhs = scala.collection.mutable.HashSet.from(csub.bot.left)
              var prevBotRef: Int = 0
              // Discharge K assumptions, latest-introduced first. At iteration i we
              // substitute tsi_i (which only appears in quantifieds(i), since
              // quantifieds(j<i) was defined before tsi_i existed and quantifieds(j>i)
              // has already been discharged).
              for (i <- (K - 1) to 0 by -1) {
                checkInterrupted()
                val ts            = tseitins(i)
                val schemaSubst   = Map(ts.tsi -> lambdifyAll(ts.subst, ts.freeVars))
                // `ts.tsi` is unique to step i so only `quantifieds(i)` is affected.
                val quantReflFormula = substituteVariablesOpti(quantifieds(i), schemaSubst)
                mutableLhs -= quantifieds(i)
                mutableLhs += quantReflFormula
                val instLhs       = mutableLhs.toSet
                val instBot       = Sequent(instLhs, rhs)
                outerSteps       += KernelStep(InstSchema(instBot, prevBotRef, schemaSubst))
                val instRef       = outerSteps.size - 1
                outerSteps       += KernelStep(SCSubproof(proveQuantifiedReflIff(ts.subst, ts.freeVars), IndexedSeq.empty))
                val reflRef       = outerSteps.size - 1
                mutableLhs -= quantReflFormula
                val cutLhs        = mutableLhs.toSet
                val cutBot        = Sequent(cutLhs, rhs)
                outerSteps       += KernelStep(Cut(cutBot, reflRef, instRef, quantReflFormula))
                prevBotRef        = outerSteps.size - 1
              }

              ClausificationProof(outerSteps.toIndexedSeq, outerImports)
    }

    innerCertifyTseitin(problem.hypotheses.toList, Nil)
  }

  /** Flat cross-axiom Tseitin certifier: pre-processes every axiom (running
    * `tseitinStep` until clausal), gathers ALL `Q = ∑ K_i` quantified-iff
    * assumptions into ONE outer [[ClausificationSubproof]], then discharges them
    * in a single block of `Q` InstSchema/refl/Cut triples.
    *
    * This eliminates the n-fold per-import [[Weakening]] paid by the legacy
    * recursive design at every nested csub level: instead of `O(n) imports ×
    * O(n) levels = O(n²)` weakenings, the flat design pays `O(n) imports × 1
    * level`, giving linear total proof size in the number of independent axioms.
    *
    * Each axiom's K_i Tseitin IFFs are still discharged latest-first, but across
    * axioms the order is irrelevant because Tseitin variables introduced by one
    * axiom never appear in another axiom's `subst` (each axiom is processed
    * independently with a private starting position in [[tseitinStep]]). */
  private def certifyTseitinFlat(problem: Problem, prover: ClausificationProver): ClausificationProof = {
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
        finalSeq: Sequent                     // `ax` if K=0 else `() |- last.tsRewrite`
    )

    val allAxData: IndexedSeq[AxData] = problem.hypotheses.zipWithIndex.map { case (ax, i) =>
      checkInterrupted()
      val phi = singleRightFormula(ax, "axiom")
      val buf = scala.collection.mutable.ArrayBuffer.empty[TseitinStep]
      var current: Expression = phi
      var continue = true
      while (continue) {
        checkInterrupted()
        tseitinStep(current, counter) match
          case None    => continue = false
          case Some(t) => buf += t; current = t.tsRewrite
      }
      val tseitins = buf.toIndexedSeq
      val newClauseSeqs = tseitins.flatMap(_.newClauses).map(lits => Sequent(Set.empty, lits.toSet)).toIndexedSeq
      val finalSeq = if (tseitins.isEmpty) ax else () |- tseitins.last.tsRewrite
      AxData(i, ax, tseitins, newClauseSeqs, finalSeq)
    }.toIndexedSeq

    val flatTseitins: IndexedSeq[TseitinStep] = allAxData.flatMap(_.tseitins)
    val Q = flatTseitins.size

    // Final clausal problem for the downstream prover, in interleaved axiom order:
    // for each axiom either the original axiom (if already clausal) or its newClauses
    // followed by its final rewritten form.
    val finalAxioms: IndexedSeq[Sequent] = allAxData.flatMap { ad =>
      if (ad.tseitins.isEmpty) IndexedSeq(ad.ax)
      else ad.newClauseSeqs ++ IndexedSeq(ad.finalSeq)
    }
    val newProblem = Problem(finalAxioms.toList, None)

    // Fast path: no Tseitin work at all (every axiom already clausal).
    if (Q == 0) {
      val downstream = prover(newProblem)
      require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
      // newProblem.imports == problem.imports here, so downstream.imports already match outerImports.
      return downstream
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
        finalAxRefs += innerAxRef(ad.axIdx)
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
        finalAxRefs += lastRewriteRef
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

  // ─────────────────────────────────────────────────────────────────────────────
  // Pure (uncertified) formula transformations  (helpers for the pipeline)
  // ─────────────────────────────────────────────────────────────────────────────

  /** Convert a formula to negation normal form. */
  def toNNF(f: Expression, negated: Boolean): Expression = f match
    case `top`          => if negated then bot else top
    case `bot`          => if negated then top else bot
    case Neg(g)         => toNNF(g, !negated)
    case And(g, h)      =>
      if negated then or(toNNF(g, true))(toNNF(h, true))
      else and(toNNF(g, false))(toNNF(h, false))
    case Or(g, h)       =>
      if negated then and(toNNF(g, true))(toNNF(h, true))
      else or(toNNF(g, false))(toNNF(h, false))
    case Implies(g, h)  => toNNF(or(neg(g))(h), negated)
    case Iff(g, h)      =>
      // Expand directly without going through Implies, to avoid rebuilding
      // intermediate implication nodes.  The result is:
      //   (g ⟺ h)  =  (¬g_nnf ∨ h_nnf) ∧ (g_nnf ∨ ¬h_nnf)
      //  ¬(g ⟺ h)  =  (g_nnf ∧ ¬h_nnf) ∨ (¬g_nnf ∧ h_nnf)
      val gPos = toNNF(g, negated = false); val gNeg = toNNF(g, negated = true)
      val hPos = toNNF(h, negated = false); val hNeg = toNNF(h, negated = true)
      if negated then or(and(gPos)(hNeg))(and(gNeg)(hPos))
      else and(or(gNeg)(hPos))(or(gPos)(hNeg))
    case Forall(x, inner) =>
      if negated then exists(x, toNNF(inner, true))
      else forall(x, toNNF(inner, false))
    case Exists(x, inner) =>
      if negated then forall(x, toNNF(inner, true))
      else exists(x, toNNF(inner, false))
    case atom => if negated then neg(atom) else atom

  /**
    * Result of one Skolemization step on a formula.
    *
    *   - `skoFormula`     : the original formula with the leftmost outermost existential
    *                        `∃x. φ(x)` (possibly nested under `∀`/`∧`/`∨`) replaced by
    *                        `φ[ε(λx.φ)/x]` — i.e. the bound variable substituted by the
    *                        Hilbert-epsilon witness directly. This is the formula the
    *                        parent recursion threads as the new axiom; no further
    *                        substitution across the recursive proof is needed.
    *   - `bridge`         : a closed (no-imports modulo [[existsEpsilonIffStatement]])
    *                        SC proof concluding `f ⊢ skoFormula`. This is what the
    *                        parent uses to derive `() ⊢ skoFormula` from `() ⊢ f` via
    *                        a single Cut.
    */
  case class SkolemStep(
      skoFormula: Expression,
      bridge: SCProof
  )

  /**
    * Single-step Skolemization with bridge proof.
    *
    * Pops the leftmost outermost existential `∃x. φ` reachable through `∀`/`∧`/`∨`
    * and replaces it directly by `φ[ε(λx. φ)/x]` (the Hilbert-epsilon witness form).
    * Synthesises a closed SC proof bridging the original formula `f` to its
    * post-substitution form in a constant number of steps, by:
    *
    *   1. Instantiating [[Quantifiers.existsEpsilonIff]] (the schematic equivalence
    *      `(∃x. P(x)) ⇔ P(εx. P(x))`) at `P := λx. φ` to obtain the local equivalence
    *      `(∃x. φ) ⇔ φ[ε(λx.φ)/x]`.
    *   2. Using one [[RightSubstIff]] application to lift that local equivalence into
    *      the position chosen inside `f` (via a context `λp. phi_body`, where
    *      `phi_body` is `f` with the chosen `∃x.φ` replaced by a fresh propositional
    *      variable `p`).
    *
    * Returns `None` if `f` contains no existential under the supported connectives.
    */
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
  private def substituteVariablesOpti(e: Expression, m: Map[Variable, Expression]): Expression =
    if (m.isEmpty) e
    else
      // Pre-compute the free variables of all substitution values once at the top level.
      // This set is passed down so that Lambda cases don't recompute it from scratch for
      // every nested binder (which would be O(depth × |m| × value_size) total).
      val fvOfValues: Set[Variable] = m.values.flatMap(_.freeVariables).toSet
      substituteVariablesOptiRec(e, m, fvOfValues)

  private def substituteVariablesOptiRec(e: Expression, m: Map[Variable, Expression], fvOfValues: Set[Variable]): Expression =
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

  def skolemizeOne(f: Expression, counter: Counter): Option[SkolemStep] = {
    checkInterrupted()
    // Single descent that builds:
    //   - phi_body  : f with the leftmost ∃x.φ replaced by `p(b_1)…(b_k)`, where
    //                 `b_1…b_k` are the enclosing universally-bound variables on
    //                 the path to the ∃ and `p` is a fresh higher-sort marker
    //                 (sort `s_1 → … → s_k → Prop`). Used as the body of the
    //                 RightSubstIff context. Parameterising the marker by the
    //                 enclosing binders is essential: without it, capture-avoiding
    //                 substitution α-renames the surrounding ∀-binders and strands
    //                 their occurrences inside the substituted ε-form (see the
    //                 Skolem bridge below).
    //   - x, inner  : the bound variable and body of the chosen ∃, used to
    //                 instantiate the schematic [[existsEpsilonIffStatement]] at
    //                 `P := λx.inner[b_i := u_i]` for fresh witnesses `u_i`.
    //   - p         : the fresh marker variable used as the substitution point.
    //   - enclosing : enclosing universal binders, outermost first.
    case class Hit(
        phi_body: Expression,
        x: Variable,
        inner: Expression,
        p: Variable,
        enclosing: Seq[Variable]
    )

    def descend(e: Expression, enclosing: Seq[Variable]): Option[Hit] =
      def bin(g: Expression, h0: Expression, op: (Expression, Expression) => Expression): Option[Hit] =
        descend(g, enclosing).map(h => h.copy(phi_body = op(h.phi_body, h0)))
          .orElse(descend(h0, enclosing).map(h => h.copy(phi_body = op(g, h.phi_body))))
      e match
        case Exists(x, inner) =>
          val pSort = enclosing.foldRight(Prop: Sort)((b, acc) => b.sort >>: acc)
          val p     = Variable(Identifier(s"_p${counter.next()}", 0), pSort)
          val pApp  = enclosing.foldLeft(p: Expression)(_(_))
          Some(Hit(pApp, x, inner, p, enclosing))

        case Forall(y, body) =>
          descend(body, enclosing :+ y).map(h => h.copy(phi_body = forall(Lambda(y, h.phi_body))))

        case And(g, h0) => bin(g, h0, and(_)(_))
        case Or(g, h0)  => bin(g, h0, or(_)(_))

        // In NNF, `Neg` only wraps atoms, so no existential reaches this case.
        case _ => None

    descend(f, Seq.empty).map { h =>
      val k = h.enclosing.size

      // Pick fresh witnesses u_i (one per enclosing binder), all kept distinct from
      // every name occurring in `f`. They will play the role of the universally-
      // quantified arguments of the iff that bridges the substitution.
      val taken = scala.collection.mutable.Set.empty[Identifier] ++ f.freeVariables.map(_.id)
      val us = h.enclosing.map { b =>
        val id = freshId(taken, Identifier("u", 0))
        taken += id
        Variable(id, b.sort)
      }
      val renaming: Map[Variable, Expression] = h.enclosing.zip(us).toMap

      // Local quantities, all in terms of the fresh u_i:
      //   innerU    = inner[b_i := u_i]
      //   lambdaInnerU = λx. innerU
      //   targetU   = ∃x. innerU
      //   epsFormU  = innerU[x := ε(λx.innerU)]
      //   localIff  = targetU ⇔ epsFormU         (the existsEpsilonIff instance)
      val innerU       = substituteVariablesOpti(h.inner, renaming)
      val lambdaInnerU = Lambda(h.x, innerU)
      val targetU      = exists(lambdaInnerU)
      val epsFormU     = substituteVariablesOpti(innerU, Map(h.x -> epsilon(lambdaInnerU)))
      val localIff     = targetU <=> epsFormU

      // The higher-sort substitution lambdas. After β, `targetLambda(u_1)…(u_k)`
      // is `targetU`, and similarly for `epsLambda`. The kernel checker for
      // [[RightSubstIff]] (= [[RightSubstEq]]) synthesises the universally-
      // quantified iff `∀x_no…x_{no+k-1}. targetLambda(...) ⇔ epsLambda(...)`,
      // which is α-equivalent (after β) to `outerIff` below.
      val targetLambda = us.foldRight(targetU: Expression)((u, e) => Lambda(u, e))
      val epsLambda    = us.foldRight(epsFormU: Expression)((u, e) => Lambda(u, e))
      val outerIff     = us.foldRight(localIff: Expression)((u, e) => forall(Lambda(u, e)))

      // Skolem result: substitute `p` with `epsLambda` in `phi_body`, then β-
      // normalise. β-normalisation is essential so that subsequent
      // [[skolemizeOne]] passes can syntactically descend through the result:
      // without it, the freshly-introduced `(λu_i.body)(b_i)` redexes hide
      // inner `Forall/Exists/And/Or` nodes from the descent matcher.
      val skoFormula =
        substituteVariablesOpti(h.phi_body, Map(h.p -> epsLambda)).betaNormalForm

      // Bridge proof: takes [[existsEpsilonIffStatement]] as a single import,
      // conclusion `f ⊢ skoFormula`. Reuses [[Quantifiers.existsEpsilonIff]] to
      // avoid rebuilding the local iff proof at every Skolem site: instantiate
      // the schematic theorem to obtain `() ⊢ localIff`, wrap with `RightForall`
      // × k to lift it to `outerIff`, then lift it into context via RightSubstIff.
      val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
      // 0: () ⊢ localIff   (single InstSchema of existsEpsilonIff)
      steps += InstSchema(() |- localIff, -1, Map(schemaP -> lambdaInnerU))
      // 1..k: RightForall × k (innermost first)
      var current: Expression = localIff
      var ref = 0
      for (i <- us.indices.reverse) {
        val u = us(i)
        val wrapped = forall(Lambda(u, current))
        steps += RightForall(() |- wrapped, ref, current, u)
        ref = steps.size - 1
        current = wrapped
      }
      val outerIffRef = ref
      // k+1: f ⊢ f
      steps += Hypothesis(f |- f, f)
      val hypRef = steps.size - 1
      // k+2: lift the local iff into context, replacing `p` with the substitution.
      steps += RightSubstIff(
        Sequent(Set(f, outerIff), Set(skoFormula)),
        hypRef,
        Seq((targetLambda, epsLambda)),
        (Seq(h.p), h.phi_body)
      )
      val substRef = steps.size - 1
      // k+3: discharge `outerIff` via Cut.
      steps += Cut(f |- skoFormula, outerIffRef, substRef, outerIff)

      // The recursion now sees the ε-form directly: no cross-proof substitution.
      SkolemStep(skoFormula, SCProof(steps.toIndexedSeq, IndexedSeq(existsEpsilonIffStatement)))
    }
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
  def tseitinStep(f: Expression, counter: Counter): Option[TseitinStep] = {
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
      val (tsi, freeVars, tsApp) = freshTseitinAtom(sub, counter)
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

  /** Collect ALL Tseitin steps for a formula in a single bottom-up pass (O(K) instead
    * of O(K²) from iterating [[tseitinStep]]).
    *
    * The bottom-up traversal rewrites each non-clause AND/OR node exactly once:
    *   - When both children are clauses, emit a [[TseitinStep]] and return the fresh
    *     Tseitin atom (a clause) as the rewritten node.
    *   - Recurse into children first so the deepest eligible node is processed before
    *     its parent (same selection order as the iterative [[tseitinStep]] loop).
    *
    * Returns the accumulated list of steps in emission order (same as the iterative
    * loop in [[certifyTseitinFlat]]). If `f` is already a clause, returns Nil. */
  private def tseitinAllSteps(f: Expression, counter: Counter): List[TseitinStep] = {
    val buf = scala.collection.mutable.ListBuffer.empty[TseitinStep]

    // Returns the rewritten form of `g` (a clause or Tseitin atom) after emitting all
    // necessary steps into `buf`. Pre-condition: `g` is in NNF (no Iff/Implies).
    def rewrite(g: Expression): Expression = g match
      case _ if isClause(g) => g
      case And(g1, g2) =>
        val r1 = rewrite(g1)
        val r2 = rewrite(g2)
        if (isClause(r1) && isClause(r2)) {
          // Both sides are now clauses: emit a Tseitin step.
          val sub = and(r1)(r2)
          val (tsi, freeVars, tsApp) = freshTseitinAtom(sub, counter)
          val hole = Variable(Identifier(s"_th${counter.next()}", 0), Prop)
          val contextBody = hole  // context: λhole. hole (the whole formula is the subst target)
          val tsRewrite = tsApp
          val newClauses: Seq[Seq[Expression]] =
            Seq(neg(tsApp) +: clauseLiterals(r1), neg(tsApp) +: clauseLiterals(r2))
          buf += TseitinStep(tsRewrite, newClauses, tsi, freeVars, tsApp, sub, hole, contextBody, isAndCase = true, r1, r2)
          tsApp
        } else and(r1)(r2)
      case Or(g1, g2) =>
        val r1 = rewrite(g1)
        val r2 = rewrite(g2)
        if (isClause(r1) && isClause(r2)) {
          val sub = or(r1)(r2)
          val (tsi, freeVars, tsApp) = freshTseitinAtom(sub, counter)
          val hole = Variable(Identifier(s"_th${counter.next()}", 0), Prop)
          val contextBody = hole
          val tsRewrite = tsApp
          val newClauses: Seq[Seq[Expression]] =
            Seq(neg(tsApp) +: (clauseLiterals(r1) ++ clauseLiterals(r2)))
          buf += TseitinStep(tsRewrite, newClauses, tsi, freeVars, tsApp, sub, hole, contextBody, isAndCase = false, r1, r2)
          tsApp
        } else or(r1)(r2)
      case _ => g  // literal or atom — already a clause

    if (!isClause(f)) rewrite(f)
    buf.toList
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

  def conjuncts(f: Expression): Seq[Expression] = f match
    case And(g, h) => conjuncts(g) ++ conjuncts(h)
    case other     => Seq(other)

  def disjoinAll(formulas: Seq[Expression]): Expression =
    if formulas.size == 1 then formulas.head else multior(formulas)

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
  private def freshTseitinAtom(f: Expression, counter: Counter): (Variable, Seq[Variable], Expression) = {
    // Only the Ind-sorted free variables are abstracted into `tsi` — higher-sorted
    // free variables (e.g. predicate or function variables like `P : Ind → Prop`)
    // cannot be `forall`-quantified by the kernel, so they remain free in the
    // iff/quantified definitional context (acting as opaque parameters). They are
    // still substituted correctly by [[InstSchema]] since `tsi` is fresh and
    // substituting it cannot capture any other free variable.
    val freeVars = f.freeVariables.toSeq.filter(_.sort == Ind).sortBy(_.id.toString)
    val tsId = Identifier(s"Ts${counter.next()}", 0)
    val tsSort = freeVars.foldRight(Prop: Sort)((v, acc) => v.sort -> acc)
    val tsi = Variable(tsId, tsSort)
    val tsApp = freeVars.foldLeft(tsi: Expression)((acc, v) => acc(v))
    (tsi, freeVars, tsApp)
  }

  def extractUniversalMatrix(f: Expression, counter: Counter): (Expression, Seq[Variable]) = {
    def go(f: Expression, subst: Map[Variable, Expression]): (Expression, Seq[Variable]) =
      f match
        case Forall(x, inner) =>
          val fresh = Variable(Identifier(s"V${counter.next()}", 0), Ind)
          val (matrix, vars) = go(inner, subst + (x -> fresh))
          (matrix, fresh +: vars)
        case And(left, right) =>
          val (leftMatrix, leftVars) = go(left, subst)
          val (rightMatrix, rightVars) = go(right, subst)
          (and(leftMatrix)(rightMatrix), leftVars ++ rightVars)
        case Or(left, right) =>
          val (leftMatrix, leftVars) = go(left, subst)
          val (rightMatrix, rightVars) = go(right, subst)
          (or(leftMatrix)(rightMatrix), leftVars ++ rightVars)
        case Neg(inner) =>
          val (innerMatrix, innerVars) = go(inner, subst)
          (neg(innerMatrix), innerVars)
        case other =>
          (substituteVariablesOpti(other, subst), Seq.empty)
    go(f, Map.empty)
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Counter helper
  // ─────────────────────────────────────────────────────────────────────────────

  class Counter(var value: Int = 0) {
    def next(): Int = { val v = value; value += 1; v }
  }
}
