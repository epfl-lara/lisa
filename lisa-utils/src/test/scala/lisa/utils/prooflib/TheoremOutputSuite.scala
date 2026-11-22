package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers._
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks the distinction between proved, admitted and erroneous theorem output.
 */
class TheoremOutputSuite extends AnyFunSuite:
  private given Library = new Library
  private val p = variable[Prop]

  test("explicit admissions and their dependents are yellow with a textual marker"):
    given output: StringOutputManager = new StringOutputManager
    val admitted = Theorem.generated(p) { have(thesis) by BasicStep.Sorry }
    val dependent = Theorem.generated(p) { have(admitted) }
    assert(admitted.errors.isEmpty && dependent.errors.isEmpty)
    val lines = output.toString.linesIterator.toSeq
    assert(lines.size == 2)
    assert(lines.forall(_.startsWith(Console.YELLOW)))
    assert(lines.forall(_.contains("(Relies on Sorry)")))

  test("proof errors remain red while their dependents are marked as admissions"):
    given output: StringOutputManager = new StringOutputManager
    val failed = Theorem.generated(p) { ProofCarrier.Failure("failed proof") }
    val dependent = Theorem.generated(p) { have(failed) }
    assert(failed.errors.nonEmpty && dependent.errors.isEmpty)
    assert(output.toString.linesIterator.next().startsWith(Console.RED))
    val last = output.toString.linesIterator.toSeq.last
    assert(last.startsWith(Console.YELLOW) && last.contains("(Relies on Sorry)"))

  test("closed proofs without admissions are green and have no admission marker"):
    given output: StringOutputManager = new StringOutputManager
    val proved = Theorem.generated(p |- p) { have(thesis) by BasicStep.Hypothesis }
    assert(proved.errors.isEmpty && !proved.thm.usesSorry)
    assert(output.toString.startsWith(Console.GREEN))
    assert(!output.toString.contains("Relies on Sorry"))

  test("the public Corollary declaration registers, prints and reuses a theorem"):
    given output: StringOutputManager = new StringOutputManager
    val corollary = Exports.Corollary(p |- p) { have(thesis) by BasicStep.Hypothesis }
    assert(corollary.kind == Corollary)
    assert(corollary.errors.isEmpty && !corollary.thm.usesSorry)
    assert(summon[Library].theorems.getFull(corollary.fullName.value).contains(corollary))
    assert(output.toString.contains(s"Corollary ${corollary.shortName} := ${corollary.statement}"))
    val reused = Theorem.generated(p |- p) { have(corollary) }
    assert(reused.errors.isEmpty && !reused.thm.usesSorry)
