package lisa.automation.clausification
import lisa.utils.K
import lisa.utils.K.{_, given}

/** Certified clausification for Lisa, following the SC-TPTP pipeline structure.
  *
  * The reusable proof IR (`ClausificationProof`, `ClausificationSubproof`,
  * lowering, etc.) lives in [[ProofIR]] (same package). This module hosts the
  * clausification-specific certification pipeline. */
object Clausification {

  /**
   * Authoritative, '''single-point-of-change''' configuration of every fresh name the clausifier and proof
   * reconstruction generate. Each site builds its identifiers from these vals (`Identifier(prefix, counter)`),
   * so a prefix is changed in exactly one place.
   *
   * '''Naming standard.''' Every prefix is a short (≤5 char, usually ~3), purely alphabetic string — no digits,
   * no `_`. The incrementing counter ALWAYS lives in the identifier's `no` field, so `Identifier("esk", n)`
   * renders `esk`, `esk_1`, `esk_2`, … (the lone `_` is the kernel's `String ↔ Identifier` round-trip
   * separator). This is what the whole pipeline relies on: [[lisa.automation.superposition.Bridge]] interns
   * bank symbols by `id.toString` (name+counter, so counter-distinct symbols never collapse) and
   * `Reconstruction.identOf` recovers `Identifier(name, no)` from `name_no`. Because the prefixes are lowercase
   * alphabetic, generated symbols also print as bare TPTP lower-words.
   *
   * '''Reserved namespace.''' Together with the fixed schema placeholders of the library statements
   * ([[schemaP]] `P`, [[schemaR]] `R`, `x` — instantiated by the Skolem/prenex bridges), these prefixes form the
   * namespace the pipeline instantiates from the inside. No input variable may live in it: an inner `InstSchema`
   * on a variable that is also free in an enclosing [[ClausificationSubproof]] assumption is rejected by the
   * kernel (see the soundness restriction on [[ClausificationSubproof]]). [[ScreenPhase]] enforces this once, at
   * the top of the pipeline, by renaming *every* free input variable into [[inputVar]] / [[inputPred]] /
   * [[inputFun]], the prefixes reserved for screened input. Those are disjoint from every prefix below, and
   * disjoint from `P`/`R`/`x` because a screened name always carries a counter of at least 1: `P_1` is a
   * screened predicate, whereas the bare `P` is [[schemaP]] and is never produced by screening.
   */
  private[automation] object GeneratedNames:
    // Certified clausification pipeline (kernel schema vars, naming atoms, substitution-context holes):
    val skolemFun      = "esk"  // SkolemPhase             — Skolem ε-function schema var (discharged via InstSchema)
    val namingAtom     = "nm"   // UncertifiedClausifier + certified — the definitional-naming atom (both paths, via NamingSupport.freshNamingAtom)
    val clauseVar      = "w"    // UncertifiedClausifier, PrenexPhase (+ test stripForall) — the fresh variable each stripped ∀
                                //   is instantiated at (via LeftForall), becoming a clause variable; SAME name in both paths
    val epsAbs         = "epsi" // Clausal                 — ε-abstraction function schema var lifting ε-terms
    val hole           = "HOLE" // for specifying rewrite positions in proofs.

    val etaVar         = "etaZ" // Clausification          — fresh var for η-expansion (avoids capture) e.g. `∀ P` becoming `∀(λz. P(z))`
    val skolemBound    = "u"    // SkolemPhase             — fresh bound-var base (freshId) inside a Skolem-term λ
    // Uncertified path (symbols interned into the term bank by `id.toString`):
    val uncertifiedSkolem     = "sk"   // UncertifiedClausifier            — Skolem function Constant (≠ the certified ε-schema `esk`)
    // Input screening ([[ScreenPhase]]) — the three namespaces every free input variable is renamed into,
    // by the sort a symbol ultimately returns. Screening counters start at 1, so a screened name is never the
    // bare prefix and can therefore never be `P` ([[schemaP]]), `R` ([[schemaR]]) or `x`.
    val inputVar       = "v"    // Ind                    — the clause variables of the input
    val inputPred      = "P"    // Ind → … → Ind → Prop   — the input's uninterpreted predicate symbols
    val inputFun       = "F"    // Ind → … → Ind → Ind    — the input's uninterpreted function symbols
    // Proof reconstruction (superposition DAG → kernel, [[lisa.automation.superposition.Reconstruction]]):
    val reconClauseVar = "cv"   // per-clause canonical clause variable (reused across clauses; instantiated independently)

  // ─────────────────────────────────────────────────────────────────────────────
  // Library theorem statements used by the certified bridges.
  //
  // The clausification proof uses these as *imports*, to be discharged later by
  // the corresponding library theorem when the pipeline is wrapped as a tactic.
  // They are kept in fixed positions at the *end* of the proof's imports list,
  // so that bridge subproofs can reference them by stable negative indices.
  // ─────────────────────────────────────────────────────────────────────────────

  // ── Clause-count estimation (shared by the uncertified [[UncertifiedClausifier]] and its certified twin
  //    [[CertifiedClausifier]], whose naming decisions must agree bit-for-bit) ──────────────────
  //
  /** Positive/negative CNF clause-count estimate of a subformula, each saturated at [[clauseCountCap]] — we
   *  only ever compare it against a naming `threshold`, so the exact count past the cap is irrelevant. */
  private[clausification] final case class Est(pos: Long, neg: Long)
  private[clausification] val atomEst: Est = Est(1, 1)
  private[clausification] val clauseCountCap: Long = 1L << 20
  private[clausification] inline def capMul(a: Long, b: Long): Long = math.min(clauseCountCap, a * b)
  private[clausification] inline def capAdd(a: Long, b: Long): Long = math.min(clauseCountCap, a + b)

  /** Schema variables appearing in the library statements: predicate `P` (`Ind → Prop`) for the
    * quantified side of the prenex laws, and nullary `R` (`Prop`) for the closed (`x`-free) side. */
  private[clausification] val schemaP: Variable = Variable(Identifier("P", 0), Ind >>: Prop)
  private[clausification] val schemaR: Variable = Variable(Identifier("R", 0), Prop)
  private val schemaX: Variable = Variable(Identifier("x", 0), Ind)

  /** Statement of `lisa.maths.Quantifiers.existsEpsilonIff`: `() ⊢ ∃(λx.P(x)) ⇔ P(ε(λx.P(x)))`. */
  val existsEpsilonIffStatement: Sequent = {
    val lambdaPx = Lambda(schemaX, schemaP(schemaX))
    () |- (exists(lambdaPx) <=> schemaP(epsilon(lambdaPx)))
  }

  // Prenex-lifting equivalences (∀ commutes with ∧/∨ over a *closed* side). The closed side is the
  // nullary `R` (a `Prop`, hence `x`-free), so each statement is a genuine theorem — unlike a `Q(x)`
  // form, which would bind the closed side's `x` under the ∀ on the right and be a non-theorem.
  // `P` is always the quantified side; each statement matches one of the four [[LiftLayer]] cases.
  val forallAndLeftStatement: Sequent  = () |- (and(forall(Lambda(schemaX, schemaP(schemaX))))(schemaR) <=> forall(Lambda(schemaX, and(schemaP(schemaX))(schemaR))))
  val forallAndRightStatement: Sequent = () |- (and(schemaR)(forall(Lambda(schemaX, schemaP(schemaX)))) <=> forall(Lambda(schemaX, and(schemaR)(schemaP(schemaX)))))
  val forallOrLeftStatement: Sequent   = () |- (or(forall(Lambda(schemaX, schemaP(schemaX))))(schemaR) <=> forall(Lambda(schemaX, or(schemaP(schemaX))(schemaR))))
  val forallOrRightStatement: Sequent  = () |- (or(schemaR)(forall(Lambda(schemaX, schemaP(schemaX)))) <=> forall(Lambda(schemaX, or(schemaR)(schemaP(schemaX)))))

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

  /**
    * The sequent shape a clause takes on the way out of either conversion: the clause
    * `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ` becomes `a₁, …, aₘ ⊢ b₁, …, bₙ`, so a negative literal is carried as its
    * atom on the **left** and a positive literal on the right. The empty sequent is the empty clause.
    *
    * This is the form [[lisa.automation.superposition.Bridge]] reads clauses in, and hence the form the
    * imports of a reconstructed refutation take. Emitting it directly keeps the clause set, the prover's
    * working form and the proof's imports in one representation. [[DistributePhase]] builds the same shape
    * structurally, since it has to name the two sides while the derivation is still being assembled.
    */
  private[automation] def clauseSequent(literals: Iterable[Expression]): Sequent =
    val negative = Set.newBuilder[Expression]
    val positive = Set.newBuilder[Expression]
    literals.foreach {
      case Neg(atom) => negative += atom
      case literal   => positive += literal
    }
    Sequent(negative.result(), positive.result())

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

  /** References into outer imports for the library imports, in their fixed order. */
  private[clausification] def libRefs(nonLibSize: Int): IndexedSeq[Int] = libImports.indices.map(libRef(nonLibSize, _)).toIndexedSeq

  private[clausification] type ClausificationProver = Problem => ClausificationProof

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
   *
   * '''Where it is called, and the invariant it maintains.''' Everything downstream of an entry point holds
   * "every `∀`/`∃` is an explicit `Application(binder, Lambda(x, b))`". Each of the three ways a formula can enter
   * the prover establishes it once, at its own boundary:
   *
   *   - [[ScreenPhase]] — the certified pipeline, on hypotheses and conjecture alike;
   *   - [[UncertifiedClausifier.clausalFormWithOrigins]] — the uncertified path (CASC, the benchmarks), after the optional
   *     orthologic step, which can itself reintroduce the shape;
   *   - [[lisa.automation.superposition.Bridge.formulaToSequent]] — already-clausal TPTP input, whose `∀`-strip
   *     needs the explicit binder.
   *
   * Downstream, [[SkolemPhase.skolemizeOne]] is the one step that demonstrably *reintroduces* the shape (it
   * `betaNormalForm`s, which is where η-reduction lives) and re-applies this immediately. The orthologic
   * `reducedNNFForm` is ordered before the expansion in [[UncertifiedClausifier]] for the same reason, defensively: it
   * rebuilds the formula through the kernel's locally-nameless normal form, so anything normalised beforehand can
   * come back reshaped. The rule for new code is therefore: **re-apply this after any `betaNormalForm` or kernel
   * normal-form round-trip.** [[DistributePhase.isLeaf]] rejects a surviving η-reduced quantifier as the certified
   * pipeline's end-of-pipeline check that the invariant actually held.
   *
   * `private[automation]` rather than `private[clausification]` because [[lisa.automation.superposition.Bridge]]
   * is one of the three entry points.
   */
  private[automation] def etaExpandQuantifiers(e: Expression): Expression =
    def freshEtaVar(free: Set[Variable]): Variable =
      var n = 0
      var z = Variable(Identifier(GeneratedNames.etaVar, n), Ind)
      while free.contains(z) do { n += 1; z = Variable(Identifier(GeneratedNames.etaVar, n), Ind) }
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

  /**
   * The outer **discharge** loop shared by [[SkolemPhase.certifySkolem]] and
   * [[CertifiedClausifier.certifyNaming]]. `csub` carries `count` fresh-symbol definitions as
   * assumptions on its antecedent; this discharges them **latest-first** — for each `j = count-1 … 0`,
   * `InstSchema` the fresh symbol to its value (which turns assumption `j` into a reflexive formula), prove that
   * reflexive formula, and `Cut` it away. `perStep(j)` supplies the three things that differ between the two
   * callers: the schema substitution `F := value`, the assumption formula being discharged (`oldLhs`, present on
   * `csub`'s antecedent), and the closed proof of its reflexive instance `substituteVariablesOpti(oldLhs, subst)`.
   *
   * Latest-first is required: a later definition's value may mention an earlier fresh symbol, so discharging the
   * latest first keeps every symbol confined to its own (still-present) assumption when instantiated. Returns the
   * finished proof over `outerImports`.
   *
   * '''Precondition:''' every `perStep` substitution must leave `csub.bot.right` pointwise unchanged, since that
   * succedent is carried across the whole `InstSchema`/`Cut` chain as written — vacuous for both callers, whose
   * subproof concludes `⊢`.
   */
  private[clausification] def dischargeAssumptionsLatestFirst(
      csub: ClausificationSubproof,
      count: Int,
      outerImports: IndexedSeq[Sequent],
      perStep: Int => (Map[Variable, Expression], Expression, SCProof)): ClausificationProof =
    val outerSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    outerSteps += csub
    val rhs = csub.bot.right
    val mutableLhs = scala.collection.mutable.HashSet.from(csub.bot.left)
    var prevBotRef = 0
    for j <- (count - 1) to 0 by -1 do
      val (schemaSubst, oldLhs, reflProof) = perStep(j)
      val reflexive = substituteVariablesOpti(oldLhs, schemaSubst) // instantiating the fresh symbol makes it reflexive
      mutableLhs -= oldLhs; mutableLhs += reflexive
      outerSteps += KernelStep(InstSchema(Sequent(mutableLhs.toSet, rhs), prevBotRef, schemaSubst))
      val instRef = outerSteps.size - 1
      outerSteps += KernelStep(SCSubproof(reflProof, IndexedSeq.empty))
      val reflRef = outerSteps.size - 1
      mutableLhs -= reflexive
      outerSteps += KernelStep(Cut(Sequent(mutableLhs.toSet, rhs), reflRef, instRef, reflexive))
      prevBotRef = outerSteps.size - 1
    ClausificationProof(outerSteps.toIndexedSeq, outerImports)

  /** Layout of the recursion-context premises for [[certifyAxiomwise]].
    *
    * It uses the same outer-imports shape after popping one axiom from the todo list:
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

  /** Heap ceiling for the safety valve below: 90% of max. `maxMemory` is fixed for the life of the JVM, so
    * it is read once rather than on every poll. */
  private val heapCeiling: Long = (Runtime.getRuntime.maxMemory / 10) * 9

  /** Counts calls to [[checkInterrupted]] so the heap is polled only every [[heapPollInterval]]th one. Not
    * synchronised: it is a heuristic trigger, and a lost increment under concurrent use only shifts *when*
    * the poll happens, never whether the valve is correct. */
  private var interruptPolls: Int = 0
  private inline val heapPollInterval = 256

  /** Cooperative cancellation hook: throw `InterruptedException` if the
    * current thread has been interrupted, OR if the JVM is dangerously close
    * to OOM (used heap > 90% of max).  The latter is a safety valve so a
    * runaway problem (e.g. an exponential blow-up that allocates faster than
    * `Thread.interrupted()` can be polled) cannot crash the whole bench.
    *
    * The interrupt flag is checked every call — it is a plain field read. The heap is not: `totalMemory` and
    * `freeMemory` are native calls, and this runs per axiom, per naming step and per distribute step, of
    * which there are thousands. Polling every 256th call keeps the valve responsive (a step allocates a
    * bounded amount, so the heap cannot run far between polls) at 1/256th of the cost. */
  private[clausification] inline def checkInterrupted(): Unit = {
    if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled")
    interruptPolls += 1
    if ((interruptPolls & (heapPollInterval - 1)) == 0) checkHeadroom()
  }

  /** The out-of-line half of [[checkInterrupted]]: the part worth paying for only occasionally. */
  private def checkHeadroom(): Unit = {
    val rt = Runtime.getRuntime
    val used = rt.totalMemory() - rt.freeMemory()
    if (used > heapCeiling)
      throw new InterruptedException(s"Memory pressure: heap ${used / (1024*1024)}MB / max ${rt.maxMemory() / (1024*1024)}MB")
  }

  /** Generic "pop one axiom, optionally transform, recurse" certifier — the scaffold behind
    * [[PrenexPhase.certifyPrenex]] ([[SkolemPhase.certifySkolem]] has its own loop). */
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
    // Finally one [[ClausificationSubproof]] wraps the downstream prover call, mapping each transformed axiom
    // slot to its final step index (or import ref for passthroughs).
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

  // The top-level certified clausification pipeline lives in [[CertifiedClausifier.certifyClausal]] (it adds a
  // threshold-gated naming pass before NNF to cap CNF blow-up). The per-phase certifiers and the shared helpers
  // (libImports, lowerClausificationProof, ClausificationProof) below are what it composes.

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
