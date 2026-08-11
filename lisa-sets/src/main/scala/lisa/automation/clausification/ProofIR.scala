package lisa.automation.clausification

import lisa.utils.K
import lisa.utils.K.{_, given}

// ─────────────────────────────────────────────────────────────────────────────
// Proof IR for the certified clausification pipeline.
//
// A [[ClausificationProof]] is a thin layer over [[SCProof]] that adds one
// extra constructor — [[ClausificationSubproof]] — letting an inner subproof
// declare a subset of its imports as *local LHS assumptions* (rather than
// premises supplied by the parent). [[lowerClausificationProof]] converts a
// [[ClausificationProof]] into a kernel [[SCProof]] by:
//   - threading each [[Assumption]] formula onto the LHS of the step bots of
//     the inner proof that need it — those whose premise cone reaches an
//     import, which is the only way an assumption can enter a step — and
//   - introducing a `Hypothesis(φ ⊢ φ)` step at the start of the lowered
//     subproof to discharge the assumption import locally.
//
// This module is package-private to [[lisa.automation.clausification]].
// ─────────────────────────────────────────────────────────────────────────────

private[clausification] sealed trait ClausificationProofStep {
  def bot: Sequent
}

private[clausification] final case class KernelStep(step: SCProofStep) extends ClausificationProofStep {
  def bot: Sequent = step.bot
}

/** A non-trivial LHS assumption pushed down into a [[ClausificationSubproof]].
  *
  * @param formula      the assumed formula `φ` (added on the LHS of every step bot of
  *                     the inner proof during lowering)
  * @param importIndex  the position of `() ⊢ φ` in [[ClausificationSubproof.proof.imports]];
  *                     this import is *not* discharged by a parent premise but instead by
  *                     a `Hypothesis(φ ⊢ φ)` step inserted at the start of the lowered subproof. */
private[clausification] final case class Assumption(formula: Expression, importIndex: Int)

/** A subproof that is itself a [[ClausificationProof]] (rather than a kernel [[SCProofStep]]),
  * lowered to an [[SCSubproof]] by [[lowerClausificationProof]].
  *
  * The inner proof's imports are partitioned into:
  *   - **assumption imports** — those at positions [[assumptions]]`.map(_.importIndex)`.
  *     Each such `() ⊢ φ` is materialised inside the lowered subproof by a fresh
  *     `Hypothesis(φ ⊢ φ)` step, and `φ` is added to the LHS of the conclusions that
  *     depend on it (steps whose premise cone reaches an import — see
  *     [[lowerClausificationProof]]; the conclusion always does). From the *outside*,
  *     this subproof's bot therefore is `proof.conclusion +<< φ1 +<< φ2 +<< ...` (see [[bot]]).
  *   - **external imports** — all other positions, in their original order. They are
  *     discharged by [[premises]]`(j)`, a kernel reference into the *parent* proof for
  *     the `j`-th external position. The same indexing convention as kernel
  *     [[SCSubproof]] applies (non-negative for parent steps, negative for parent imports).
  *
  * '''Restriction on positive premises: cite only assumption-bearing steps.''' When this subproof is lowered
  * inside a region that carries assumptions — its own, or any inherited from an enclosing
  * [[ClausificationSubproof]] — every external import of the lowered child is given those assumptions on its
  * left, while the kernel matches a subproof's imports against its premises *exactly*. So a premise that is a
  * **step index** must name a step that carries the assumptions too, i.e. one whose own premise cone reaches an
  * import (the `needs` relation computed in [[lowerClausificationProof]]).
  *
  * Citing a locally-derived *closed* lemma — one proved outright, with no import anywhere in its cone — hands
  * the kernel `Γ ⊢ Δ` where it expects `φ1, …, φk, Γ ⊢ Δ`, and the step is rejected. That is a live temptation
  * rather than a hypothetical: [[DistributePhase]] derives every clause of a matrix from closed steps
  * (`Hypothesis`/`LeftAnd`/`LeftOr` over `φ`'s subformulas, citing only each other) and keeps to the rule by
  * citing only the `Cut` against the axiom import, never the closed derivation behind it. Negative premises are
  * always safe: the lowering routes them through the external-import view or a `Weakening`, both of which carry
  * the assumptions. Asserted during lowering, where the `needs` relation is available.
  *
  * '''Soundness restriction on the inner proof.''' During lowering, an assumption-dependent
  * step bot of the inner proof is rewritten to `step.bot +<< φ1 +<< ... +<< φk` (the assumption
  * formulas added on the LHS), but the existing premise/conclusion shapes — including
  * those of any [[InstSchema]] step inside the inner proof — are kept as written.
  * If the inner proof contains an `InstSchema` (or any other step) that instantiates
  * a schema variable that occurs *free* in some assumption formula `φi`, the lowered
  * step's bot ends up with the *original* `φi` on the LHS (mechanically prepended by
  * the lowering pass) but its RHS reflects the *substituted* form derived from the
  * already-substituted premise sequent — so the kernel will reject the step on a
  * left/right mismatch.
  *
  * So: never [[InstSchema]] a schema var free in an assumption formula from inside the inner proof; do it in
  * the parent after discharge (as `certifyNaming`/`certifySkolem` do). The pipeline keeps to this on both
  * sides: it only ever instantiates its *own* schemas (the library placeholders `P`/`R`, the fresh `esk`/`nm`),
  * and [[ScreenPhase]] guarantees no *input* variable is named like one of them.
  *
  * Invariants (checked at construction):
  *   - `assumptions.size + premises.size == proof.imports.size` (every inner import is
  *     accounted for).
  *   - All `assumptions(_).importIndex` values are distinct and in range. */
private[clausification] final case class ClausificationSubproof(
    proof: ClausificationProof,
    premises: IndexedSeq[Int],
    assumptions: IndexedSeq[Assumption] = IndexedSeq.empty
) extends ClausificationProofStep {
  require(assumptions.size + premises.size == proof.imports.size, "Subproof assumptions and premises must account for all imports")
  require(assumptions.forall(a => a.importIndex >= 0 && a.importIndex < proof.imports.size), "Assumption import indices out of range")
  require(assumptions.map(_.importIndex).distinct.size == assumptions.size, "Assumption import indices must be distinct")

  // Memoized: `bot` may be called repeatedly during lowering (once per outer step in
  // the discharge loop, O(Q) times for the csub produced by certifyNaming/certifySkolem).
  // Using `lazy val` avoids the repeated `foldLeft` allocation.
  lazy val bot: Sequent = assumptions.foldLeft(proof.conclusion)((acc, a) => acc +<< a.formula)
}

private[clausification] final case class ClausificationProof(steps: IndexedSeq[ClausificationProofStep], imports: IndexedSeq[Sequent]) {
  require(steps.nonEmpty, "A clausification proof must contain at least one step")

  def conclusion: Sequent = steps.last.bot
}

private[clausification] object ClausificationProof {
  def fromSCProof(proof: SCProof): ClausificationProof =
    ClausificationProof(proof.steps.map(KernelStep(_)), proof.imports)
}

/** Append every assumption in `assumptionSet` to the LHS of `sequent` (idempotent on existing entries).
  * Takes a precomputed set so callers can amortize the `Seq -> Set` build across many sequents that share
  * the same assumption list. */
private[clausification] def addAssumptionsLeftSet(sequent: Sequent, assumptionSet: Set[Expression]): Sequent =
  if (assumptionSet.isEmpty) sequent
  else sequent.copy(left = sequent.left ++ assumptionSet)

/** Rebuild a kernel [[SCProofStep]] keeping all its data but swapping its bot. */
private[clausification] def rewriteStepBot(step: SCProofStep, newBot: Sequent): SCProofStep = step match
  case Cut(_, t1, t2, phi) => Cut(newBot, t1, t2, phi)
  case Hypothesis(_, phi) => Hypothesis(newBot, phi)
  case InstSchema(_, t1, subst) => InstSchema(newBot, t1, subst)
  case LeftAnd(_, t1, phi, psi) => LeftAnd(newBot, t1, phi, psi)
  case LeftExists(_, t1, phi, x) => LeftExists(newBot, t1, phi, x)
  case LeftForall(_, t1, phi, x, t) => LeftForall(newBot, t1, phi, x, t)
  case LeftIff(_, t1, phi, psi) => LeftIff(newBot, t1, phi, psi)
  case LeftImplies(_, t1, t2, phi, psi) => LeftImplies(newBot, t1, t2, phi, psi)
  case LeftNot(_, t1, phi) => LeftNot(newBot, t1, phi)
  case LeftOr(_, t, disjuncts) => LeftOr(newBot, t, disjuncts)
  case LeftRefl(_, t1, fa) => LeftRefl(newBot, t1, fa)
  case LeftSubstEq(_, t1, equals, lambdaPhi) => LeftSubstEq(newBot, t1, equals, lambdaPhi)
  case Restate(_, t1) => Restate(newBot, t1)
  case RestateTrue(_) => RestateTrue(newBot)
  case RightAnd(_, t, conjuncts) => RightAnd(newBot, t, conjuncts)
  case RightEpsilon(_, t1, phi, x, t) => RightEpsilon(newBot, t1, phi, x, t)
  case RightExists(_, t1, phi, x, t) => RightExists(newBot, t1, phi, x, t)
  case RightForall(_, t1, phi, x) => RightForall(newBot, t1, phi, x)
  case RightIff(_, t1, t2, phi, psi) => RightIff(newBot, t1, t2, phi, psi)
  case RightImplies(_, t1, phi, psi) => RightImplies(newBot, t1, phi, psi)
  case RightNot(_, t1, phi) => RightNot(newBot, t1, phi)
  case RightOr(_, t1, phi, psi) => RightOr(newBot, t1, phi, psi)
  case RightRefl(_, fa) => RightRefl(newBot, fa)
  case RightSubstEq(_, t1, equals, lambdaPhi) => RightSubstEq(newBot, t1, equals, lambdaPhi)
  case SCSubproof(sp, premises) =>
    val rewritten =
      if (sp.conclusion.left.size == newBot.left.size && sp.conclusion.right.size == newBot.right.size && isSameSequent(sp.conclusion, newBot))
        sp
      else
        sp.withNewSteps(IndexedSeq(Weakening(newBot, sp.steps.size - 1)))
    SCSubproof(rewritten, premises)
  case step: Sorry => step.copy(bot = newBot)
  case Weakening(_, t1) => Weakening(newBot, t1)

/** Push `assumptions` onto the LHS of every step bot and import of a kernel proof.
  *
  * For `SCSubproof` steps, uses a shallow strategy: instead of recursing into the
  * inner proof (which would be O(Q × inner_steps) per sub-proof), it appends a single
  * `Weakening` step to the inner proof to produce the correct conclusion with the
  * extra assumptions.  This makes the cost O(1) per `SCSubproof` rather than O(inner_steps × Q).
  *
  * '''Restriction: a nested `SCSubproof`'s inner proof must be closed''' (no imports) — required below.
  * The shallow rewrite touches only the nested proof's *conclusion*; its **imports** keep their original
  * left-hand sides. Its inner *steps* not carrying the assumptions is harmless — that is exactly what the
  * appended `Weakening` legitimises — but an inner *import* is matched by the kernel against the parent
  * premise discharging it (`isSameSequent(ref(premise), sp.imports(i))`, in `SCProofChecker`'s `SCSubproof`
  * case), and that premise *has* just been given the assumptions. `φ, Γ ⊢ Δ` would then be matched against
  * `Γ ⊢ Δ` and the step rejected. With no imports there is nothing to mismatch.
  *
  * The restriction holds throughout the pipeline, and the `require` below enforces it rather than trusting
  * it. The import-bearing subproofs — the ε-bridge in [[SkolemPhase]], the naming bridge in
  * [[CertifiedClausifier.certifyNaming]], [[PrenexPhase]]'s lifting subproof, the prover's own
  * reconstruction — are all *top-level* steps of the proof handed to this function, whose imports it rewrites
  * itself (`loweredImports`); they are never nested one level deeper.
  */
private[clausification] def lowerKernelProofWithAssumptions(proof: SCProof, assumptions: Seq[Expression]): SCProof = {
  // Fast path: with no assumptions, lowering is the identity. Avoids walking every
  // step and reallocating identical bot sequents (a major win for skolem/prenex which
  // rely on this helper but never have assumptions in scope).
  if (assumptions.isEmpty) proof
  else {
    if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled (lowering)")
    val assumptionSet = assumptions.toSet
    val loweredImports = proof.imports.map(addAssumptionsLeftSet(_, assumptionSet))
    val loweredSteps = proof.steps.map {
      case SCSubproof(sp, premises) =>
        // Shallow: add a Weakening step to produce the correct conclusion without
        // recursively adding assumptions to every inner step. Sound only for a closed inner proof —
        // its imports would otherwise keep their un-weakened LHS while the premises discharging them
        // gain the assumptions, and the kernel's premise/import match fails (see the method doc).
        require(sp.imports.isEmpty,
          s"lowerKernelProofWithAssumptions: a nested SCSubproof must be closed, but this one has " +
            s"${sp.imports.size} import(s); the shallow rewrite would leave them un-weakened and the kernel " +
            "would reject the step. Lower it as a ClausificationSubproof, or hoist it to a top-level step.")
        val targetBot = addAssumptionsLeftSet(sp.conclusion, assumptionSet)
        val shallowSp =
          if (targetBot.left.size == sp.conclusion.left.size && isSameSequent(targetBot, sp.conclusion)) sp
          else sp.withNewSteps(IndexedSeq(Weakening(targetBot, sp.steps.size - 1)))
        SCSubproof(shallowSp, premises)
      case step =>
        rewriteStepBot(step, addAssumptionsLeftSet(step.bot, assumptionSet))
    }
    SCProof(loweredSteps, loweredImports)
  }
}

/** Lower a [[ClausificationProof]] (no inherited assumptions) to a kernel [[SCProof]]. */
private[clausification] def lowerClausificationProof(proof: ClausificationProof): SCProof =
  lowerClausificationProof(proof, IndexedSeq.empty, IndexedSeq.empty)

private[clausification] def lowerClausificationProof(
    proof: ClausificationProof,
    localAssumptions: IndexedSeq[Assumption],
    inheritedAssumptions: IndexedSeq[Expression]
): SCProof = {
  val assumptions = inheritedAssumptions ++ localAssumptions.map(_.formula)
  val assumptionSet: Set[Expression] = if (assumptions.isEmpty) Set.empty else assumptions.toSet
  val assumptionIndexSet = localAssumptions.map(_.importIndex).toSet
  val externalImportIndices = proof.imports.indices.filterNot(assumptionIndexSet).toIndexedSeq
  val externalCount = externalImportIndices.size
  require(externalCount + localAssumptions.size == proof.imports.size, "Imports must split into external + local-assumption imports")
  // External imports carry only the inherited assumptions: that is what the parent's
  // premise step bots look like. Local assumptions are weakened into the proof at the
  // beginning of `loweredSteps` below.
  val inheritedSet: Set[Expression] = if (inheritedAssumptions.isEmpty) Set.empty else inheritedAssumptions.toSet
  val externalImports = externalImportIndices.map { i =>
    addAssumptionsLeftSet(proof.imports(i), inheritedSet)
  }

  val loweredSteps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
  // Map each external import to a kernel reference inside the lowered subproof.
  // - When the import does NOT need rewriting (target == externalView), keep the
  //   negative import reference `-(newIndex+1)` directly: no extra step is needed
  //   since the inner steps can reference the SCSubproof's imports themselves.
  // - When the import needs rewriting (a strict superset of left assumptions), insert
  //   a single Weakening step and store its (positive) step index.
  // This is critical: emitting an unconditional Restate per import at every level
  // makes the lowered proof O(n^2) in the depth of nested ClausificationSubproofs.
  // Array indexed by import index for O(1) lookup (no HashMap).
  val externalImportMapArr: Array[Int] = Array.fill(proof.imports.size)(Int.MinValue)
  externalImportIndices.zipWithIndex.foreach { case (oldIndex, newIndex) =>
    val externalView = externalImports(newIndex)
    val newRef: Int =
      if (localAssumptions.isEmpty) {
        // assumptions == inheritedAssumptions, so target == externalView; no rewrite.
        -(newIndex + 1)
      } else {
        val target = addAssumptionsLeftSet(proof.imports(oldIndex), assumptionSet)
        if (target.left.size == externalView.left.size && target.right.size == externalView.right.size && isSameSequent(target, externalView))
          -(newIndex + 1)
        else {
          val ref = loweredSteps.size
          loweredSteps += Weakening(target, -(newIndex + 1))
          ref
        }
      }
    externalImportMapArr(oldIndex) = newRef
  }
  val localAssumptionSteps = localAssumptions.map { case Assumption(phi, _) =>
      val hypRef = loweredSteps.size
      loweredSteps += Hypothesis(phi |- phi, phi)
      val weakenedBot = addAssumptionsLeftSet(() |- phi, assumptionSet)
      if (weakenedBot.left.size == loweredSteps(hypRef).bot.left.size && weakenedBot.right.size == loweredSteps(hypRef).bot.right.size && isSameSequent(weakenedBot, loweredSteps(hypRef).bot)) hypRef
      else {
        val weakenedRef = loweredSteps.size
        loweredSteps += Weakening(weakenedBot, hypRef)
        weakenedRef
      }
  }
  val localAssumptionMap = localAssumptions.map(_.importIndex).zip(localAssumptionSteps).toMap
  val localPrefixSize = loweredSteps.size

  def mapReference(ref: Int): Int =
    if (ref >= 0) localPrefixSize + ref
    else {
      val oldImportIndex = -ref - 1
      // externalImportMapArr entries: non-MinValue means external import, MinValue means local assumption.
      val ext = externalImportMapArr(oldImportIndex)
      if (ext != Int.MinValue) ext
      else localAssumptionMap(oldImportIndex)
    }

  // Which steps actually need the assumptions pasted onto their LHS.
  //
  // An assumption can only enter a step through an *import*: the external imports were given the inherited
  // assumptions above, and each local assumption is materialised as a `Hypothesis(φ ⊢ φ)` prefix step
  // discharging its import. So a step whose premise cone never reaches an import proves its bot outright,
  // and adding the assumptions to it is pure cost — a fresh `Sequent` per step, and per enclosing level.
  //
  // This is what makes a flat derivation as cheap to lower as a nested one. [[DistributePhase]] emits its
  // whole clause derivation flat (`Hypothesis`/`LeftAnd`/`LeftOr` over `φ`'s subformulas, citing only each
  // other) precisely so each step is checked once; none of it touches an import, so none of it is rewritten
  // here. The assumptions enter exactly where they should — at the `Cut` against the hypothesis import,
  // which turns an assumption-free `φ ⊢ Cᵢ` into `Ψ ⊢ Cᵢ`.
  //
  // Soundness: a *needing* step may have a *non-needing* premise, so the two must compose. They do, because
  // `needs` is inherited from the premises: a step is needing iff some premise is, so a single-premise step
  // always agrees with its premise, and a step can only be needing while one premise is not if another
  // premise reaches an import — a multi-premise rule, and those relate their premises' left sides by union or
  // by a `subset`/`allContainedExcept` test, both of which tolerate the extra formulas on one side. `Cut`
  // against a hypothesis import is exactly that case.
  val needsAssumptions: Array[Boolean] =
    if (assumptionSet.isEmpty) null // nothing to add anywhere; the per-step checks below short-circuit
    else {
      val needs = new Array[Boolean](proof.steps.size)
      var i = 0
      while (i < proof.steps.size) {
        // Steps are in topological order (a premise index is always < i), so this single pass is a fixpoint.
        needs(i) = proof.steps(i) match
          case KernelStep(step) => step.premises.exists(r => r < 0 || needs(r))
          // A ClausificationSubproof is lowered with the assumptions threaded through it, so it carries them.
          case _: ClausificationSubproof => true
        i += 1
      }
      needs
    }

  inline def assumptionsFor(idx: Int): Set[Expression] =
    if (needsAssumptions == null || !needsAssumptions(idx)) Set.empty else assumptionSet

  proof.steps.zipWithIndex.foreach { (s, idx) =>
    s match {
      case KernelStep(step) =>
        if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled (lowering)")
        val stepAssumptions = assumptionsFor(idx)
        val rewritten = step match
          case SCSubproof(sp, premises) =>
            val loweredSubproof = lowerKernelProofWithAssumptions(sp, if (stepAssumptions.isEmpty) Seq.empty else assumptions)
            SCSubproof(loweredSubproof, premises.map(mapReference))
          case _ =>
            val rebased = mapStepPremises(step, mapReference)
            // Skip the bot-rewrite allocation when this step needs no assumptions added.
            if (stepAssumptions.isEmpty) rebased
            else rewriteStepBot(rebased, addAssumptionsLeftSet(rebased.bot, stepAssumptions))
        loweredSteps += rewritten

      case ClausificationSubproof(subproof, premises, subAssumptions) =>
        if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled (lowering)")
        // The child's external imports are about to be given `assumptionSet` on the left, and the kernel matches
        // them against these premises exactly — so a premise naming a *step* must be one the pass below also
        // gives the assumptions to. See the restriction on [[ClausificationSubproof.premises]]. Nothing to check
        // when there are no assumptions in scope (`needsAssumptions == null`): then nothing is rewritten at all.
        if (needsAssumptions != null)
          premises.foreach { r =>
            require(r < 0 || needsAssumptions(r),
              s"ClausificationSubproof premise $r names a step whose premise cone never reaches an import, so " +
                s"lowering leaves its bot without the ${assumptionSet.size} assumption(s) that the child's " +
                "imports carry, and the kernel would reject the subproof on an import/premise mismatch. Cite a " +
                "step derived from an import (e.g. the Cut against the axiom), not a locally-derived closed lemma.")
          }
        val loweredSubproof = lowerClausificationProof(
          subproof,
          subAssumptions,
          assumptions
        )
        loweredSteps += SCSubproof(loweredSubproof, premises.map(mapReference))
    }
  }

  // The lowered conclusion is what the parent matches against [[ClausificationSubproof.bot]], which is
  // `proof.conclusion` plus the assumptions — so the last step must carry them however its cone looks. It
  // normally does, descending from the imports; this covers the degenerate proof that concludes without them.
  if (needsAssumptions != null && !needsAssumptions(proof.steps.size - 1)) {
    val last = loweredSteps.size - 1
    loweredSteps += Weakening(addAssumptionsLeftSet(loweredSteps(last).bot, assumptionSet), last)
  }

  SCProof(loweredSteps.toIndexedSeq, externalImports.toIndexedSeq)
}
