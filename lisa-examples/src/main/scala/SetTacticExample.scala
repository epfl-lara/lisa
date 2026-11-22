import lisa.maths.SetTheory.Base.Intersection
import lisa.maths.SetTheory.Base.Intersection.∩
import lisa.maths.SetTheory.Base.Symbols.x
import lisa.maths.SetTheory.Base.Symbols.y
import lisa.maths.SetTheory.Base.Symbols.z
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.utils.prooflib.ProofCarrier
import lisa.utils.prooflib.ProofJudgement
import lisa.utils.prooflib.TacticHelpers.failWith
import lisa.utils.prooflib.TacticProof

object SetTacticExample extends lisa.Main:

  /**
   * Prove union and intersection membership goals from known memberships.
   */
  def setTac(goal: Sequent): ProofCarrier[Unit] = TacticProof {
    // try trivial or split
    Restate(goal) ||
    // iterate over the RHS of sequent
    goal.right
      .collectFirst {
        case element ∈ (a ∪ b) =>
          val source = have(
            // recursively solve alternatives
            setTac(goal.left |- element ∈ a) || setTac(goal.left |- element ∈ b)
          )
          val rule = have(source.right |- element ∈ (a ∪ b)) by Weakening(Union.membership of (x := a, y := b, z := element))
          have(goal) by Cut(source, rule)

        case element ∈ (a ∩ b) =>
          // recursively solve; `have` notation can be combined with `setTac`
          val left = have(goal.left |- element ∈ a) by setTac
          val right = have(goal.left |- element ∈ b) by setTac
          val source = have(goal.left |- (element ∈ a) /\ (element ∈ b)) by RightAnd(left, right)

          val rule = have(source.right |- element ∈ (a ∩ b)) by Weakening(Intersection.membership of (x := a, y := b, z := element))
          have(goal) by Cut(source, rule)

      }
      .getOrElse(failWith(s"Cannot solve goal: $goal"))
  }

  val u, A, B, C = variable[Ind]

  val unionIntroduction = Theorem(u ∈ A |- u ∈ (A ∪ B)):
    have(thesis) by setTac

  val intersectionIntroduction = Theorem((u ∈ A, u ∈ B) |- u ∈ (A ∩ B)):
    have(thesis) by setTac

  val nestedMembership = Theorem((u ∈ A, u ∈ C) |- u ∈ ((A ∪ B) ∩ (B ∪ C))):
    have(thesis) by setTac
