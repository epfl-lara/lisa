package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2._
import lisa.maths.SetTheory.Types.ADTv2.library.nat
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes constructor exhaustiveness for empty, payload, and recursive datatypes.
 */
class ExhaustivenessSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val subject, a, b, left, right = variable[Ind]

  test("an empty datatype has no inhabitants"):
    val declaration = adt("exhaustivenessEmpty", Seq.empty)
    val checked = Theorem(subject :: declaration |- False) {
      have(thesis) by Restate.from(declaration.elim.of(subject))
    }
    assert(!declaration.semantic.elim.withSorry && !checked.withSorry)

  test("a nullary datatype exhausts exactly its constructors"):
    val declaration = adt("exhaustivenessNullary", Seq("off" -> Seq.empty, "on" -> Seq.empty))
    val Seq(off, on) = declaration.constructors: @unchecked
    val checked = Theorem(subject :: declaration |- (subject === off) \/ (subject === on)) {
      have(thesis) by Restate.from(declaration.elim.of(subject))
    }
    assert(!checked.withSorry)

  test("mixed constructor cases retain every payload and recursive typing"):
    val declaration = adt(
      "exhaustivenessMixed",
      "A",
      Seq(
        "empty" -> Seq.empty,
        "payload" -> Seq("first" -> "A", "second" -> "A"),
        "node" -> Seq("left" -> SelfRef, "right" -> SelfRef)
      )
    )
    val Seq(empty, payload, node) = declaration.constructors: @unchecked
    val carrier = declaration(nat)
    val expected = (subject === empty(nat)) \/
      ∃(a, ∃(b, ((a :: nat) /\ (b :: nat)) /\ (subject === payload(nat) * a * b))) \/
      ∃(left, ∃(right, ((left :: carrier) /\ (right :: carrier)) /\ (subject === node(nat) * left * right)))
    val checked = Theorem(subject :: carrier |- expected) {
      have(thesis) by Restate.from(declaration.elim.of(nat, subject))
    }
    assert(!checked.withSorry)

  test("constructor witnesses do not capture the subject or another constructor's arguments"):
    val declaration = adt(
      "exhaustivenessCapture",
      "A",
      Seq(
        "one" -> Seq("x2" -> "A"),
        "two" -> Seq("x" -> "A", "y" -> "A")
      )
    )
    val Seq(one, two) = declaration.constructors: @unchecked
    val x2 = Variable[Ind]("x2")
    val expected = ∃(a, (a :: nat) /\ (x2 === one(nat) * a)) \/
      ∃(a, ∃(b, ((a :: nat) /\ (b :: nat)) /\ (x2 === two(nat) * a * b)))
    val checked = Theorem(x2 :: declaration(nat) |- expected) {
      have(thesis) by Restate.from(declaration.elim.of(nat, x2))
    }
    assert(!checked.withSorry)
