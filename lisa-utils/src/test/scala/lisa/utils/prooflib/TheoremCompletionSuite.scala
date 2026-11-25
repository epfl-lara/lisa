package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.automation.Discharge
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers._
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks that named theorems cannot retain unresolved kernel proof dependencies.
 */
class TheoremCompletionSuite extends AnyFunSuite:
  private given library: Library = new Library
  private given OutputManager = new StringOutputManager
  private val p, q = variable[Prop]

  test("all theorem kinds reject open proofs before exact matching or weakening"):
    val statement = () |- p
    val open = lisa.kernel.proof.Assume(using library.theory)(statement.underlying).toOption.get
    for kind <- Seq[TheoremKind](Theorem, Lemma, Corollary); goal <- Seq(statement, q |- p) do
      val theorem = kind.generated(goal) { have(open) }
      assert(theorem.errors.size == 1)
      assert(theorem.errors.head.exception.isInstanceOf[TacticFailureException])
      assert(theorem.errors.head.message.contains("unresolved kernel assumptions"))
      assert(theorem.errors.head.message.contains(statement.toString))
      assert(theorem.thm.statement == goal && theorem.thm.usesSorry)
      assert(theorem.kernel.assumptions.isEmpty)
      assert(library.theorems.getFull(theorem.fullName.value).contains(theorem))
    assert(open.assumptions == Set(statement.underlying) && !open.usesSorry)

  test("kernel dependencies may be discharged before theorem completion"):
    val statement = p |- p
    val open = lisa.kernel.proof.Assume(using library.theory)(statement.underlying).toOption.get
    val justification = BasicStep.Hypothesis(statement).kernel
    val theorem = Theorem.generated(statement) {
      have(open)
      Thm(lisa.kernel.proof.Discharge(using library.theory)(open, justification).toOption.get)
    }
    assert(theorem.errors.isEmpty && !theorem.thm.usesSorry)
    assert(theorem.kernel.assumptions.isEmpty)
    assert(theorem.thm.statement == statement)

  test("sequent hypotheses and registered axioms are not unresolved proof dependencies"):
    val hypothesis = Theorem.generated(p |- p) { have(thesis) by BasicStep.Hypothesis }
    val axiom = Theorem.generated(p) { Thm(K.Axiom(using library.theory)((() |- p).underlying).toOption.get) }
    for theorem <- Seq(hypothesis, axiom) do
      assert(theorem.errors.isEmpty && !theorem.thm.usesSorry)
      assert(theorem.kernel.assumptions.isEmpty)
    assert(axiom.kernel.axioms.nonEmpty)
