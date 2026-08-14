package lisa.automation.clausification

import lisa.utils.K
import lisa.utils.K.{_, given}

// ─────────────────────────────────────────────────────────────────────────────
// Proof IR for the certified clausification pipeline.
//
// A [[ClausificationProof]] is a thin layer over [[SCProof]] whose steps may be
// a [[ClausificationSubproof]], a nested proof declaring a subset of its own
// imports as *local assumptions* rather than as premises supplied by the
// parent. Such a subproof may use the sequent `⊢ φ` for each of them.
// [[clausificationProofToSCProof]] converts a [[ClausificationProof]] into a kernel [[SCProof]] by:
//   - threading each assumed formula onto the LHS of the step bots of
//     the inner proof that need it, namely those whose premise cone reaches an
//     import, and
//   - introducing a `RestateTrue(… ⊢ φ)` step at the start of the converted
//     subproof to represent the corresponding assumption.
// A kernel `SCSubproof` step follows the same path, as the case where the list
// of local assumptions is empty.
// ─────────────────────────────────────────────────────────────────────────────

/** A step of a [[ClausificationProof]]: an ordinary kernel step, or a [[ClausificationSubproof]]. Both are
  * converted by the same code; they differ only in whether the inner proof declares assumptions of its own. */
private[clausification] type ClausificationProofStep = SCProofStep | ClausificationSubproof

/** The conclusion of a step. Selection on a union type needs this; on either arm alone the member is used. */
extension (step: ClausificationProofStep)
  private[clausification] def bot: Sequent = step match
    case s: SCProofStep => s.bot
    case c: ClausificationSubproof => c.bot

/** Whether `sequent` has the shape an assumption import must take, `() ⊢ φ`. */
private[clausification] def isAssumptionImport(sequent: Sequent): Boolean =
  sequent.left.isEmpty && sequent.right.size == 1

/** The assumed formula `φ` of an assumption import `() ⊢ φ`, which [[ClausificationSubproof]] checks the shape of. */
private[clausification] def assumedFormula(sequent: Sequent): Expression = sequent.right.head

/** A subproof that is itself a [[ClausificationProof]], converted to an [[SCSubproof]] by
  * [[clausificationProofToSCProof]]. Its inner imports split in two: the positions named by [[assumptions]], each
  * materialised inside the converted subproof by a `RestateTrue(… ⊢ φ)` and added to the left of every conclusion
  * depending on it, and all other positions, discharged ba reference as usual in the kernel's SCProof.
  * From outside, this step's bot is the inner conclusion plus the assumed formulas
  * (see [[bot]]). Construction checks that each assumption names an import of the form `() ⊢ φ`.
  *
  * A kernel `SCSubproof` inside a [[ClausificationProof]] is converted by the same code, as the case where
  * [[assumptions]] is empty, so everything below applies to it as well.
  *
  * Two restrictions on the inner proof follow, both asserted during the conversion.
  *
  * To avoid unnecessary weeakening and allocation of new sequents, when converting to a kernel proof, assumptions are only added
  * to steps that need at least one assumption, but they are also recursively added to every imports of subproofs, so the import should be justified
  * by a step that has dependencies in imports and hence has the assumptions (otherwise there would be a missmatch between the import and the justification
  * of the import). All our phases respect that; if one day it's inconvenient, solutions can be to add a weakening step, or to exactly track assumptions
  * dependencies, including through imports, rather than simply "needs 0 assumption"/"needs at least one".
  *
  * '''No [[InstSchema]] inside the subproof on a schema variable free in an assumption.''' The conversion prepends the
  * assumption formulas to the left of a step. Instantiateion would also instantiate the assumption, but then the assumption is not the same throughout the proof.
  * The pipeline instantiates only its own schemas, and [[ScreenPhase]] keeps input variables out of their
  * namespace. */
private[clausification] final case class ClausificationSubproof(
    proof: ClausificationProof,
    premises: IndexedSeq[Int],
    assumptions: IndexedSeq[Int] = IndexedSeq.empty
) {
  // assumptions are the subproof's imports pointed by `assumptions`. Everything else is a regular import, 
  // and there must be as many of them as of premises.
  require(assumptions.size + premises.size == proof.imports.size, "Subproof assumptions and premises must account for all imports")
  require(assumptions.forall(i => i >= 0 && i < proof.imports.size), "Assumption import indices out of range")
  require(assumptions.distinct.size == assumptions.size, "Assumption import indices must be distinct")
  require(assumptions.forall(i => isAssumptionImport(proof.imports(i))), "An assumption import must have the form `() ⊢ φ`")

  // Memoized: `bot` may be called repeatedly during the conversion (once per outer step in
  // the discharge loop, O(Q) times for the csub produced by certifyNaming/certifySkolem).
  // Using `lazy val` avoids the repeated `foldLeft` allocation.
  lazy val bot: Sequent = assumptions.foldLeft(proof.conclusion)((acc, i) => acc +<< assumedFormula(proof.imports(i)))
}

private[clausification] final case class ClausificationProof(steps: IndexedSeq[ClausificationProofStep], imports: IndexedSeq[Sequent]) {
  require(steps.nonEmpty, "A clausification proof must contain at least one step")

  def conclusion: Sequent = steps.last.bot
}

private[clausification] object ClausificationProof {
  def fromSCProof(proof: SCProof): ClausificationProof =
    ClausificationProof(proof.steps, proof.imports)
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

/** Convert a [[ClausificationProof]] to a kernel [[SCProof]] (no assumptions). */
private[clausification] def clausificationProofToSCProof(proof: ClausificationProof): SCProof =
  clausificationProofToSCProof(proof, IndexedSeq.empty, IndexedSeq.empty)

private[clausification] def clausificationProofToSCProof(
    proof: ClausificationProof,
    localAssumptions: IndexedSeq[Int],
    inheritedAssumptions: IndexedSeq[Expression]
): SCProof = {
  val assumptions = inheritedAssumptions ++ localAssumptions.map(i => assumedFormula(proof.imports(i)))
  val assumptionSet: Set[Expression] = if (assumptions.isEmpty) Set.empty else assumptions.toSet
  val assumptionIndexSet = localAssumptions.toSet
  val externalImportIndices = proof.imports.indices.filterNot(assumptionIndexSet).toIndexedSeq
  require(externalImportIndices.size + localAssumptions.size == proof.imports.size, "Imports must split into external + local-assumption imports")
  // External imports carry only the inherited assumptions: that is what the parent's
  // premise step bots look like. Local assumptions are weakened into the proof at the
  // beginning of `scSteps` below.
  val inheritedSet: Set[Expression] = if (inheritedAssumptions.isEmpty) Set.empty else inheritedAssumptions.toSet
  val externalImports = externalImportIndices.map { i =>
    addAssumptionsLeftSet(proof.imports(i), inheritedSet)
  }

  val scSteps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
  // Each external import has two forms. The import list of the converted proof shows the raw import plus the
  // INHERITED assumptions, since that is what the parent's premise steps prove. A step inside this proof that
  // cites the import expects the raw import plus ALL the assumptions in scope, inherited and local. The two
  // agree when there is no local assumption, and then a step cites the import directly as `-(newIndex+1)`.
  // Otherwise one Weakening bridges them and the steps cite that step's index instead. Emitting the Weakening
  // unconditionally would cost one step per import per level, and the nesting is one level per definition in
  // certifyNaming and certifySkolem.
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
          val ref = scSteps.size
          scSteps += Weakening(target, -(newIndex + 1))
          ref
        }
      }
    externalImportMapArr(oldIndex) = newRef
  }
  
  // Materialise each local assumption as the tautology `ψ₁, …, ψₖ, φ ⊢ φ`, carrying the other assumptions too,
  // and keep the step that the citations of its import must be redirected to.
  val localAssumptionSteps = localAssumptions.map { i =>
    val phi = assumedFormula(proof.imports(i))
    scSteps += RestateTrue(addAssumptionsLeftSet(() |- phi, assumptionSet))
    scSteps.size - 1
  }
  val localAssumptionMap = localAssumptions.zip(localAssumptionSteps).toMap
  val localPrefixSize = scSteps.size

  // With no local assumption there is no prefix step and no import renumbering, so `mapReference` below is the
  // identity: no step needs rebuilding. This is the common case, every kernel subproof included.
  val identityMapping = localAssumptions.isEmpty

  /** Translate a premise number into the number of the step that means the same in the converted proof.
  * A step index moves up by the number of prefix steps inserted at the begining of the proof; an import reference becomes its new
  * import reference, or the prefix step standing for it. */
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
  // A step whose premise cone never reaches an import proves its bot directly,
  // and adding the assumptions to it is pure cost, so we skip it and leave it without the assumption.
  val needsAssumptions: Array[Boolean] =
    if (assumptionSet.isEmpty) null // nothing to add anywhere; the per-step checks below short-circuit
    else {
      val needs = new Array[Boolean](proof.steps.size)
      var i = 0
      while (i < proof.steps.size) {
        val premises = proof.steps(i) match
          case step: SCProofStep => step.premises
          case csub: ClausificationSubproof => csub.premises
        needs(i) = premises.exists(r => r < 0 || needs(r))
        i += 1
      }
      needs
    }

  inline def assumptionsFor(idx: Int): Set[Expression] =
    if (needsAssumptions == null || !needsAssumptions(idx)) Set.empty else assumptionSet

  // The imports of a converted subproof receive the assumptions handed down to it, and the kernel matches those
  // imports against the bots of the premises discharging them, so a premise naming a step must name one that the
  // loop below also gives the assumptions to. See the restriction documented on [[ClausificationSubproof]].
  def checkSubproofPremises(premises: Seq[Int]): Unit =
    if (needsAssumptions != null)
      premises.foreach { r =>
        require(r < 0 || needsAssumptions(r),
          s"Subproof premise $r names a step whose premise cone never reaches an import, so the conversion " +
            s"leaves its bot without the ${assumptionSet.size} assumption(s) that the subproof's imports carry, " +
            "and the kernel would reject the step on an import/premise mismatch. Cite a step derived from an " +
            "import (e.g. the Cut against the axiom), not a locally-derived closed lemma.")
      }

  def mapPremises(premises: Seq[Int]): Seq[Int] = if (identityMapping) premises else premises.map(mapReference)

  /** Convert and append a subproof step, kernel or clausification: they differ only in whether the inner proof
    * declares assumptions of its own. Like any other step it is handed the assumptions in scope only if it
    * reaches an import. */
  def emitSubproof(inner: ClausificationProof, innerAssumptions: IndexedSeq[Int], premises: Seq[Int], idx: Int): Unit =
    val inherited = if (assumptionsFor(idx).isEmpty) IndexedSeq.empty else assumptions
    if (inherited.nonEmpty) checkSubproofPremises(premises)
    scSteps += SCSubproof(clausificationProofToSCProof(inner, innerAssumptions, inherited), mapPremises(premises))

  proof.steps.zipWithIndex.foreach { (s, idx) =>
    if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled (proof conversion)")
    s match {
      case SCSubproof(sp, premises) =>
        emitSubproof(ClausificationProof.fromSCProof(sp), IndexedSeq.empty, premises, idx)

      case step: SCProofStep =>
        val stepAssumptions = assumptionsFor(idx)
        val rebased = if (identityMapping) step else mapStepPremises(step, mapReference)
        // Skip the bot-rewrite allocation when this step needs no assumptions added.
        scSteps +=
          (if (stepAssumptions.isEmpty) rebased
           else rewriteStepBot(rebased, addAssumptionsLeftSet(rebased.bot, stepAssumptions)))

      case ClausificationSubproof(subproof, premises, subAssumptions) =>
        emitSubproof(subproof, subAssumptions, premises, idx)
    }
  }

  // This conclusion becomes the bot of the subproof step in the parent, and the parent gave that step the
  // assumptions, so the last step must carry them however its cone looks. It normally does, descending from the
  // imports; this covers the proof that concludes without reaching one, a closed kernel subproof for instance.
  if (needsAssumptions != null && !needsAssumptions(proof.steps.size - 1)) {
    val last = scSteps.size - 1
    scSteps += Weakening(addAssumptionsLeftSet(scSteps(last).bot, assumptionSet), last)
  }

  SCProof(scSteps.toIndexedSeq, externalImports.toIndexedSeq)
}
