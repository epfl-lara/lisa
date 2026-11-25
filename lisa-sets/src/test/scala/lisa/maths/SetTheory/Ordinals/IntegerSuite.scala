package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Ordinals.Integer.emptyInOmega
import lisa.maths.SetTheory.Ordinals.Integer.integer
import lisa.maths.SetTheory.Ordinals.Integer.integerHereditary
import lisa.maths.SetTheory.Ordinals.Integer.omegaDownwardClosed
import lisa.maths.SetTheory.Ordinals.Integer.omegaInduction
import lisa.maths.SetTheory.Ordinals.Integer.omegaPredecessor
import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Integer.subsetSuccessor
import lisa.maths.SetTheory.Ordinals.Integer.succMembership
import lisa.maths.SetTheory.Ordinals.Integer.successorInjectivity
import lisa.maths.SetTheory.Ordinals.Integer.zeroIsNotSucc
import lisa.maths.SetTheory.Ordinals.Integer.ω
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes integer closure proofs and successor laws for arbitrary sets.
 */
class IntegerSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager

  private val α, β, x, y, z, n, m, k = variable[Ind]
  private val P = variable[Ind >>: Prop]

  test("successor laws need no ordinal or natural-number assumptions"):
    val membership = Theorem(z ∈ S(x) <=> (z ∈ x) \/ (z === x)) {
      have(thesis) by Restate.from(succMembership.of(k := z, n := x))
    }
    val injectivity = Theorem(S(x) === S(y) |- x === y) {
      have(thesis) by Weakening(successorInjectivity.of(n := x, m := y))
    }
    val nonempty = Theorem(!(S(x) === ∅)) {
      have(thesis) by Restate.from(zeroIsNotSucc.of(n := x))
    }
    val inclusion = Theorem(x ⊆ S(x)) {
      have(thesis) by Restate.from(subsetSuccessor.of(n := x))
    }
    assert(!membership.hasErrorsOrSorry && !injectivity.hasErrorsOrSorry && !nonempty.hasErrorsOrSorry && !inclusion.hasErrorsOrSorry)

  test("integer membership is hereditary through two levels"):
    val checked = Theorem((integer(α), x ∈ α, y ∈ x) |- integer(y)) {
      val first = have((integer(α), x ∈ α) |- integer(x)) by
        Restate.from(integerHereditary.of(β := x))
      have(thesis) by Tautology.from(first, integerHereditary.of(α := x, β := y))
    }
    assert(!checked.hasErrorsOrSorry)

  test("omega contains zero and is closed under elements and predecessor"):
    val downward = Theorem((y ∈ ω, x ∈ y) |- x ∈ ω) {
      have(thesis) by Restate.from(omegaDownwardClosed)
    }
    val predecessor = Theorem(S(x) ∈ ω |- x ∈ ω) {
      have(thesis) by Restate.from(omegaPredecessor.of(α := x))
    }
    assert(!emptyInOmega.hasErrorsOrSorry && !downward.hasErrorsOrSorry && !predecessor.hasErrorsOrSorry)

  test("both induction names expose the same proof and schema"):
    val expected = (P(∅), ∀(m, m ∈ ω ==> (P(m) ==> P(S(m))))) |- ∀(n, n ∈ ω ==> P(n))
    assert(omegaSuccessorInduction eq omegaInduction)
    assert(isSameSequent(omegaSuccessorInduction.statement, expected))
    assert(!omegaSuccessorInduction.hasErrorsOrSorry)
