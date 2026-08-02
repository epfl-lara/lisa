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
//   - threading each [[Assumption]] formula onto the LHS of every step bot of
//     the inner proof, and
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
  *     `Hypothesis(φ ⊢ φ)` step and the formula `φ` is added to the LHS of every
  *     other step's conclusion. From the *outside*, this subproof's bot therefore is
  *     `proof.conclusion +<< φ1 +<< φ2 +<< ...` (see [[bot]]).
  *   - **external imports** — all other positions, in their original order. They are
  *     discharged by [[premises]]`(j)`, a kernel reference into the *parent* proof for
  *     the `j`-th external position. The same indexing convention as kernel
  *     [[SCSubproof]] applies (non-negative for parent steps, negative for parent imports).
  *
  * '''Soundness restriction on the inner proof.''' During lowering, every step bot of
  * the inner proof is rewritten to `step.bot +<< φ1 +<< ... +<< φk` (the assumption
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
  * the parent after discharge (as `certifyFastNaming`/`certifySkolem` do).
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
  // the discharge loop, O(Q) times for the csub produced by certifyFastNaming/certifySkolem).
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
  * Note: The resulting proof is NOT kernel-valid (the SCSubproof's inner steps won't
  * have the assumptions on their bots).  This is intentional: the clausification
  * pipeline only uses kernel proofs for proof-size accounting, not for verification.
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
        // recursively adding assumptions to every inner step.
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

  proof.steps.foreach {
    case KernelStep(step) =>
      if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled (lowering)")
      val rewritten = step match
        case SCSubproof(sp, premises) =>
          val loweredSubproof = lowerKernelProofWithAssumptions(sp, assumptions)
          SCSubproof(loweredSubproof, premises.map(mapReference))
        case _ =>
          val rebased = mapStepPremises(step, mapReference)
          // Skip the bot-rewrite allocation when there are no assumptions to add.
          if (assumptionSet.isEmpty) rebased
          else rewriteStepBot(rebased, addAssumptionsLeftSet(rebased.bot, assumptionSet))
      loweredSteps += rewritten

    case ClausificationSubproof(subproof, premises, subAssumptions) =>
      if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled (lowering)")
      val loweredSubproof = lowerClausificationProof(
        subproof,
        subAssumptions,
        assumptions
      )
      loweredSteps += SCSubproof(loweredSubproof, premises.map(mapReference))
  }

  SCProof(loweredSteps.toIndexedSeq, externalImports.toIndexedSeq)
}
