import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofCarrier
import lisa.utils.prooflib.ProofJudgement
import lisa.utils.prooflib.TacticHelpers._
import lisa.utils.prooflib.TacticProof
import lisa.utils.prooflib.TacticProofM

object ProofFailureExample extends lisa.Main:
  private val p = variable[Prop]
  private val q = variable[Prop]
  private val r = variable[Prop]
  private val x = variable[Ind]

  // FAILURE: try an alternative without logging an error or capturing a stack.
  val recoveredFailure = Theorem(p ==> p):
    val attempt = maybe(thesis) by Hypothesis
    have(attempt.or(Tautology(thesis)))

  // COMMITTED FAILURE: report a user error, admit p, and continue.
  val committedFailure = Theorem(p):
    have(thesis) by Tautology

  // FRONTEND MISUSE: .of(x) requires a universally quantified conclusion.
  // The theorem boundary recovers because the exception occurs before by is called.
  val badInstantiation = Theorem(p |- p):
    val premise = have(q |- q) by Hypothesis
    have(r |- r) by Restate.from(premise.of(x))
    have(thesis) by Restate.from(lastStep)

  // SUBPROOF: recover a frontend error by admitting the enclosing goal.
  val userSubproof = Theorem(p):
    have(p) subproof {
      val premise = have(q |- q) by Hypothesis
      have(r |- r) by Restate.from(premise.of(x))
    }

  private def brokenProof(conclusion: Sequent)(using Library, sourcecode.File, sourcecode.Line): ProofJudgement =
    TacticProof {
      have(conclusion) by Hypothesis
    }

  // TACTIC BUG: an internal failed have becomes a TacticException, recovered by the user have.
  val badTactic = Theorem(p):
    have(p) by brokenProof

  // MISSING PAYLOAD: haveM cannot invent an Int; the enclosing subproof recovers.
  val missingPayload = Theorem(p |- p):
    def brokenPayload(conclusion: Sequent)(using sourcecode.File, sourcecode.Line): ProofCarrier[Int] =
      TacticProofM[Int] {
        throw new IllegalStateException("Example tactic failed before computing its payload.")
      }
    have(thesis) subproof {
      val (_, count) = haveM(thesis) by brokenPayload
    }
