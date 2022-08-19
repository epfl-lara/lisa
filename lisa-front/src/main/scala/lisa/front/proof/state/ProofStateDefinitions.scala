package lisa.front.proof.state

import lisa.kernel.proof.SCProof
import lisa.front.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.{Rewrite, SCProofStep, SCSubproof}
import lisa.utils.{ProofsShrink}
import lisa.front.proof.sequent.{SequentDefinitions, SequentOps}

trait ProofStateDefinitions extends SequentDefinitions with SequentOps {

  /**
   * A proof in the front.
   * It corresponds to an initial state represented a sequence of goals, and a sequence of tactics to be applied.
   * Note that the tactics do not necessarily eliminate all goals.
   * @param initialState the initial state
   * @param steps the tactics
   */
  case class Proof(initialState: ProofState, steps: Seq[Tactic])
  object Proof {
    def apply(goals: Sequent*)(steps: Tactic*): Proof = Proof(ProofState(goals.toIndexedSeq), steps)
  }

  /**
   * The proof state is a sequence of proof goals, which are themselves sequents.
   * @param goals the goals in this state
   */
  final case class ProofState(goals: IndexedSeq[Sequent]) {
    override def toString: String =
      ((if (goals.nonEmpty) s"${goals.size} goal${if (goals.sizeIs > 1) "s" else ""}" else "[zero goals]") +:
        goals.map(_.toString).map(s => s"- $s")
        ).mkString("\n")
  }
  object ProofState {
    def apply(goals: Sequent*): ProofState = ProofState(goals.toIndexedSeq)
  }

  type MutatorResult = Option[ProofModeState]
  private[ProofStateDefinitions] type TacticResult = Option[Seq[(AppliedTactic, ProofStateSnapshot)]]

  /**
   * A general class that describes a mutation on the proof mode state.
   */
  sealed abstract class ProofModeStateMutator {
    def applyMutator(proofModeState: ProofModeState): MutatorResult
  }
  case object CancelPreviousTactic extends ProofModeStateMutator {
    override def applyMutator(proofModeState: ProofModeState): MutatorResult =
      proofModeState.steps match {
        case _ +: previousSteps =>
          Some(proofModeState.copy(steps = previousSteps))
        case _ => None
      }
  }
  case object ResetProofMode extends ProofModeStateMutator {
    override def applyMutator(proofModeState: ProofModeState): MutatorResult =
      Some(proofModeState.copy(steps = Seq.empty))
  }

  /**
   * A tactic is a function that can transform a proof state into a new proof state.
   * When applied it returns an [[AppliedTactic]] object along with the new state.
   */
  sealed abstract class Tactic extends ProofModeStateMutator {
    override final def applyMutator(proofModeState: ProofModeState): MutatorResult =
      applySnapshot(proofModeState.lastSnapshot, proofModeState.environment).map(steps => proofModeState.withNewSteps(steps))
    private[ProofStateDefinitions] def applySnapshot(snapshot: ProofStateSnapshot, env: ProofEnvironment): TacticResult
  }
  case class TacticFocusGoal(goal: Int) extends Tactic {
    override private[ProofStateDefinitions] def applySnapshot(snapshot: ProofStateSnapshot, env: ProofEnvironment): TacticResult = {
      if(snapshot.proofState.goals.indices.contains(goal)) {
        // This function moves the element of index `goal` to the front
        def bringToFront[T](goals: IndexedSeq[T]): IndexedSeq[T] =
          goals(goal) +: (goals.take(goal) ++ goals.drop(goal + 1))
        val newProofState = ProofState(bringToFront(snapshot.proofState.goals))
        val newShadowProofState = bringToFront(snapshot.shadowProofState)
        Some(Seq((
          AppliedTactic(-1, this, () => IndexedSeq.empty, false, Map.empty), ProofStateSnapshot(newProofState, newShadowProofState, snapshot.nextId)
        )))
      } else {
        None
      }
    }
  }
  case class TacticRepeat(tactic: Tactic) extends Tactic {
    override private[ProofStateDefinitions] def applySnapshot(snapshot: ProofStateSnapshot, env: ProofEnvironment): TacticResult = {
      def repeat(currentSnapshot: ProofStateSnapshot, acc: Seq[(AppliedTactic, ProofStateSnapshot)], executed: Boolean): TacticResult = {
        tactic.applySnapshot(currentSnapshot, env) match {
          case Some(seq) if seq.nonEmpty =>
            val reversed = seq.reverse
            repeat(reversed.head._2, reversed ++ acc, true)
          case _ => if(executed) Some(acc.reverse) else None
        }
      }
      repeat(snapshot, Seq.empty, true)
    }
  }
  case class TacticFallback(tactics: Seq[Tactic]) extends Tactic {
    override private[ProofStateDefinitions] def applySnapshot(snapshot: ProofStateSnapshot, env: ProofEnvironment): TacticResult = {
      def iteratedTry(remaining: Seq[Tactic]): TacticResult = remaining match {
        case tactic +: tail =>
          tactic.applySnapshot(snapshot, env) match {
            case Some(result) => Some(result)
            case None => iteratedTry(tail)
          }
        case _ => None
      }
      iteratedTry(tactics)
    }
  }
  case class TacticCombine(tactics: Seq[Tactic]) extends Tactic {
    override private[ProofStateDefinitions] def applySnapshot(snapshot: ProofStateSnapshot, env: ProofEnvironment): TacticResult = {
      def iterated(remaining: Seq[Tactic], currentSnapshot: ProofStateSnapshot, acc: Seq[(AppliedTactic, ProofStateSnapshot)]): TacticResult = remaining match {
        case tactic +: tail =>
          tactic.applySnapshot(currentSnapshot, env) match {
            case Some(result) =>
              val reversed = result.reverse
              val newSnapshot = reversed.headOption match {
                case Some((_, head)) => head
                case None => currentSnapshot
              }
              iterated(tail, newSnapshot, reversed ++ acc)
            case None => None
          }
        case _ => Some(acc.reverse)
      }
      iterated(tactics, snapshot, Seq.empty)
    }
  }

  /**
   * A particular case of tactic that works on a single goal.
   */
  sealed abstract class TacticGoal extends Tactic {
    override private[ProofStateDefinitions] def applySnapshot(snapshot: ProofStateSnapshot, env: ProofEnvironment): TacticResult = {
      (snapshot.proofState.goals, snapshot.shadowProofState) match {
        case (proofGoal +: tailGoals, id +: tailShadowProofState) =>
          applyGoal(proofGoal, env) match {
            case Some(opt) =>
              val (newGoalsOrJustifications, reconstruct) = opt.getOrElse((IndexedSeq.empty, () => IndexedSeq.empty))
              val newGoals = newGoalsOrJustifications.map {
                case Left(sequent) => sequent
                case Right(justified) => justified.sequent
              }
              val newGoalsShown = newGoalsOrJustifications.collect {
                case Left(sequent) => sequent
              }
              // We prepend the newly created goals
              val newProofState = ProofState(newGoalsShown ++ tailGoals)
              // Number of goals that have been created (or updated), possibly zero
              // This corresponds to the number of premises in that rule
              val nReplacedGoals = newGoals.size
              val newShadowGoals = snapshot.nextId until (snapshot.nextId + nReplacedGoals)
              val newShadowGoalsShown = newShadowGoals.zip(newGoalsOrJustifications).collect { case (i, Left(_)) => i }
              // Updated shadow proof state (= ids for the new proof state)
              val newShadowProofState = newShadowGoalsShown ++ tailShadowProofState
              // Since we created n new goals, we must increment the counter by n
              val newNextId = snapshot.nextId + nReplacedGoals

              val justifications = newShadowGoals.zip(newGoalsOrJustifications).collect { case (i, Right(justified)) => (i, justified) }.toMap

              Some(Seq((AppliedTactic(id, this, reconstruct, opt.isEmpty, justifications), ProofStateSnapshot(newProofState, newShadowProofState, newNextId))))
            case None => None
          }
        case _ => None
      }
    }
    def applyGoal(proofGoal: Sequent, env: ProofEnvironment): Option[Option[(IndexedSeq[Either[Sequent, Justified]], ReconstructSteps)]]
  }
  case class TacticApplyJustification(justified: Justified) extends TacticGoal {
    override def applyGoal(proofGoal: Sequent, env: ProofEnvironment): Option[Option[(IndexedSeq[Either[Sequent, Justified]], ReconstructSteps)]] = {
      if(justified.environment == env && justified.sequent == proofGoal && env.contains(proofGoal)) {
        Some(None)
      } else {
        None
      }
    }
  }

  type ReconstructSteps = () => IndexedSeq[SCProofStep]

  // The premises indexing is implicit:
  // * 0, 1, 2 will reference respectively the first, second and third steps in that array

  abstract class TacticGoalFunctionalPruning extends TacticGoal {
    override def applyGoal(proofGoal: Sequent, env: ProofEnvironment): Option[Option[(IndexedSeq[Either[Sequent, Justified]], ReconstructSteps)]] =
      apply(proofGoal).map(result => Some(result))
    def apply(proofGoal: Sequent): Option[(IndexedSeq[Either[Sequent, Justified]], ReconstructSteps)]
  }

  abstract class TacticGoalFunctional extends TacticGoal {
    override def applyGoal(proofGoal: Sequent, env: ProofEnvironment): Option[Option[(IndexedSeq[Either[Sequent, Justified]], ReconstructSteps)]] =
      apply(proofGoal).map { case (sequent, reconstruct) => Some((sequent.map(Left.apply), reconstruct)) }
    def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)]
  }


  trait ReadableProofEnvironment {
    def contains(sequent: Sequent): Boolean
    def belongsToTheory(sequent: SequentBase): Boolean
  }

  type ProofEnvironment <: ReadableProofEnvironment

  trait ReadableJustified {
    private[proof] def environment: ProofEnvironment
    def sequent: Sequent
  }
  type Justified <: ReadableJustified

  private[ProofStateDefinitions] case class ProofStateSnapshot(
    proofState: ProofState,
    shadowProofState: IndexedSeq[Int],
    nextId: Int,
  )

  private[ProofStateDefinitions] case class AppliedTactic(id: Int, tactic: Tactic, reconstruct: ReconstructSteps, isTheorem: Boolean, toClose: Map[Int, Justified])

  /**
   * The proof mode state represents a backward proof builder.
   * It is initialized by specifying a sequent (the starting goal).
   * Applied tactics may be appended using the method [[withNewSteps]].
   * See [[reconstructSCProof]] for the conversion of this object into a kernel proof.
   * @param initialSnapshot
   * @param steps
   * @param environment
   */
  case class ProofModeState private[ProofStateDefinitions](
    private[ProofStateDefinitions] val initialSnapshot: ProofStateSnapshot,
    private[ProofStateDefinitions] val steps: Seq[Seq[(AppliedTactic, ProofStateSnapshot)]], // Steps are in reverse direction (the first element is the latest)
    environment: ProofEnvironment,
  ) {
    private[ProofStateDefinitions] def lastSnapshot: ProofStateSnapshot =
      steps.view.flatMap(_.lastOption).headOption.map { case (_, snapshot) => snapshot }.getOrElse(initialSnapshot)
    private[ProofStateDefinitions] def zippedSteps: Seq[(ProofStateSnapshot, AppliedTactic, ProofStateSnapshot)] = {
      val flatSteps = steps.flatMap(_.reverse)
      val snapshots = flatSteps.map { case (_, snapshot) => snapshot } :+ initialSnapshot
      snapshots.zip(snapshots.tail).zip(flatSteps.map { case (applied, _) => applied }).map {
        case ((snapshotAfter, snapshotBefore), applied) =>
          (snapshotBefore, applied, snapshotAfter)
      }
    }
    private[ProofStateDefinitions] def withNewSteps(step: Seq[(AppliedTactic, ProofStateSnapshot)]): ProofModeState =
      copy(steps = step +: steps)

    def state: ProofState = lastSnapshot.proofState
    def proving: ProofState = initialSnapshot.proofState
    def tactics: Seq[Tactic] = steps.reverse.flatten.map { case (AppliedTactic(_, tactic, _, _, _), _) => tactic }
  }

  /**
   * Evaluates a proof by converting tactics to applied tactics.
   * @param proof the proof to evaluate
   * @param environment the environment
   * @return an optional final proof mode state after applying all the tactics
   */
  def evaluateProof(proof: Proof)(environment: ProofEnvironment): Option[ProofModeState] = {
    def applyTactics(tactics: Seq[Tactic], proofModeState: ProofModeState): Option[ProofModeState] = tactics match {
      case tactic +: rest =>
        tactic.applyMutator(proofModeState) match {
          case Some(newProofModeState) => applyTactics(rest, newProofModeState)
          case None => None
        }
      case _ => Some(proofModeState)
    }
    applyTactics(proof.steps, initialProofModeState(proof.initialState.goals*)(environment))
  }

  /**
   * Reconstructs a kernel proof from an instance of a [[ProofModeState]].
   * The passed mode can still contain goals, in that case they be included as imports.
   * @param proofModeState the proof mode to use
   * @return the final proof, and a mapping from imports to the theorems used
   */
  def reconstructSCProof(proofModeState: ProofModeState): (SCProof, Map[Int, Sequent]) = {
    val proofEnvironment = proofModeState.environment
    // Each proof goal that is created (or updated) will be given a unique id
    // Then we use these ids to refer to them as a proof step in the SC proof

    // For a complete proof the proof state should be empty
    // However for testing purposes we may still allow incomplete proofs to exist,
    // and for that we should convert unclosed branches into imports
    val imports = proofModeState.lastSnapshot.proofState.goals.map(sequentToKernel)
    val initialTranslation = proofModeState.lastSnapshot.shadowProofState.zipWithIndex.map { case (v, i) => v -> -(i + 1) }.toMap

    val (finalProof, _, finalTheorems) = proofModeState.zippedSteps.foldLeft((SCProof(IndexedSeq.empty, imports), initialTranslation, Map.empty[Int, Sequent])) {
      case ((proof, translation, theorems), (snapshotBefore, applied, snapshotAfter)) =>
        val reconstructedSteps = applied.reconstruct()
        val isTheorem = applied.isTheorem
        val nReplacedGoals = snapshotAfter.nextId - snapshotBefore.nextId // TODO do not rely on the ids for that
        val id = applied.id // TODO
        val updatedGoal = snapshotBefore.proofState.goals.head

        val sortedClosed = applied.toClose.toSeq.sortBy(_._1)
        val newTheorems = theorems ++ sortedClosed.zipWithIndex.map { case ((_, justified), i) =>
          (proof.imports.size + i) -> justified.sequent
        }.toMap
        val newTranslation = translation ++ sortedClosed.zipWithIndex.map { case ((id, _), j) =>
          id -> -(proof.imports.size + j + 1)
        }
        val newImports = proof.imports ++ sortedClosed.map(_._2.sequent).map(sequentToKernel)
        val newProof0 = proof.copy(imports = newImports)

        val premises = (snapshotBefore.nextId until snapshotAfter.nextId).map(newTranslation)
        val reconstructedAndRemappedStep =
          if(reconstructedSteps.nonEmpty)
            Some(SCSubproof(
              SCProof(reconstructedSteps, premises.map(newProof0.getSequent)),
              premises,
            ))
          else
            None
        val newProof = newProof0.withNewSteps(reconstructedAndRemappedStep.toIndexedSeq)

        // We return the expanded proof, along with the information to recover the last (= current) step as a premise
        if(isTheorem) {
          val importId = newProof.imports.size
          val translatedId = -(importId + 1)
          (
            newProof.copy(imports = newProof.imports :+ sequentToKernel(updatedGoal)),
            newTranslation + (id -> translatedId),
            newTheorems + (importId -> updatedGoal),
          )
        } else {
          val translatedId = newProof.steps.size - 1
          (
            newProof,
            newTranslation + (id -> translatedId),
            newTheorems,
          )
        }
    }

    (ProofsShrink.flattenProof(finalProof), finalTheorems)
  }

  // The final conclusion is given the id 0, although it will never be referenced as a premise
  def initialProofModeState(goals: Sequent*)(environment: ProofEnvironment): ProofModeState = {
    require(goals.forall(isAcceptedSequent(_)(environment)))
    ProofModeState(ProofStateSnapshot(ProofState(goals*), 0 until goals.size, goals.size), Seq.empty, environment)
  }

  def isAcceptedSequent(sequent: Sequent)(environment: ProofEnvironment): Boolean = {
    isSequentWellFormed(sequent) && schematicConnectorsOfSequent(sequent).isEmpty && environment.belongsToTheory(sequent) // TODO is printable
  }

  /**
   * A helper module that provides common symbols for usage in rules.
   */
  object Notations {
    val (a, b, c, d, e) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"), SchematicPredicateLabel[0]("d"), SchematicPredicateLabel[0]("e"))
    val (s, t, u) = (SchematicTermLabel[0]("s"), SchematicTermLabel[0]("t"), SchematicTermLabel[0]("u"))
    val f: SchematicConnectorLabel[1] = SchematicConnectorLabel[1]("f")
    val p: SchematicPredicateLabel[1] = SchematicPredicateLabel[1]("p")
    val (x, y) = (VariableLabel("x"), VariableLabel("y"))
  }

}
