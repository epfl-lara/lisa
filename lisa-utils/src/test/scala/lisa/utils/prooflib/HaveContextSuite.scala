package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers._
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks ambient assumptions when existing theorems are recorded with have.
 */
class HaveContextSuite extends AnyFunSuite:
  private given library: Library = new Library
  private given OutputManager = new StringOutputManager
  private val p, q = variable[Prop]

  test("front, kernel and named theorems include the current assumptions"):
    val source = BasicStep.Hypothesis(p |- p).thm
    val named = Theorem.generated(p |- p) { have(source) }
    ProofBuilder.withContext: proof ?=>
      ProofHelpers.assume(q)
      for record <- Seq[() => Thm](() => have(source), () => have(source.kernel), () => have(named)) do
        val recorded = record()
        assert(recorded.statement == ((p, q) |- p))
        assert(proof.last.contains(recorded) && !recorded.usesSorry)
      assert(source.statement == (p |- p) && named.statement == (p |- p))
      assert(proof.errors.isEmpty)
      ProofJudgement(lastStep)

  test("an empty assumption context preserves the original front theorem"):
    val source = BasicStep.Hypothesis(p |- p).thm
    ProofBuilder.withContext: proof ?=>
      val recorded = have(source)
      assert(recorded eq source)
      assert(proof.last.contains(source) && proof.errors.isEmpty)
      ProofJudgement(recorded)

  test("nested contexts include inherited assumptions without changing their parent"):
    val source = BasicStep.Hypothesis(p |- p).thm
    ProofBuilder.withContext: parent ?=>
      ProofHelpers.assume(q)
      val previous = lastStep
      val result = parent.withSubcontext(): child ?=>
        val recorded = have(source)
        assert(recorded.statement == ((p, q) |- p))
        assert(child.last.contains(recorded))
        ProofJudgement(recorded)
      assert(parent.last.contains(previous))
      result

  test("weakening preserves kernel dependencies, axioms and admissions"):
    val statement = () |- p
    val open = Thm(lisa.kernel.proof.Assume(using library.theory)(statement.underlying).toOption.get)
    val axiom = Thm(K.Axiom(using library.theory)(statement.underlying).toOption.get)
    val admitted = BasicStep.Sorry(statement).thm
    ProofBuilder.withContext: proof ?=>
      ProofHelpers.assume(q)
      for source <- Seq(open, axiom, admitted) do
        val recorded = have(source)
        assert(recorded.statement == (q |- p))
        assert(recorded.kernel.assumptions == source.kernel.assumptions)
        assert(recorded.kernel.axioms == source.kernel.axioms)
        assert(recorded.usesSorry == source.usesSorry)
      assert(proof.errors.isEmpty)
      ProofJudgement(lastStep)
