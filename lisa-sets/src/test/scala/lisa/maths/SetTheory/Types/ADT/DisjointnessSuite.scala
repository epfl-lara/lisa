package lisa.maths.SetTheory.Types.ADT

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT._
import lisa.maths.SetTheory.Types.ADT.library.bool
import lisa.maths.SetTheory.Types.ADT.library.nat
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks lazy disjointness generation, symmetry, and constructor ownership.
 */
class DisjointnessSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val x, y, z = variable[Ind]

  test("a requested pair registers no unrelated disjointness and reuses each cached theorem"):
    val declaration = adt(
      "disjointnessDemand",
      "A",
      Seq(
        ("empty", Seq.empty),
        ("one", Seq(("item", "A"))),
        ("two", Seq(("left", "A"), ("right", "A"))),
        ("unused", Seq.empty)
      )
    )
    val Seq(empty, one, two, unused) = declaration.constructors: @unchecked
    val requested = declaration.disjointness(two, one)
    for first <- declaration.constructors; second <- declaration.constructors if first != second do
      val name = s"${declaration.name}/${first.semantic.name}-${second.semantic.name}/disjointness"
      assert(lisa.SetTheoryLibrary.theory.getTheorem(name).isDefined == (first == two && second == one))

    val semantic = declaration.semantic.disjointness(two.semantic, one.semantic)
    val instance = two.semantic.disjointness(one.semantic)
    val last = lisa.SetTheoryLibrary.last
    assert(declaration.disjointness(two, one) eq requested)
    assert(declaration.semantic.disjointness(two.semantic, one.semantic) eq semantic)
    assert(two.semantic.disjointness(one.semantic) eq instance)
    assert(lisa.SetTheoryLibrary.last == last)
    assert(!requested.withSorry && !semantic.withSorry && !instance.withSorry)

    val reverse = declaration.disjointness(one, two)
    val forwardApplication = Theorem((x :: nat, y :: nat, z :: nat) |- !(two(nat) * x * y === one(nat) * z)) {
      have(thesis) by Tautology.from(requested.of(nat, x, y, z))
    }
    val reverseApplication = Theorem((x :: bool, y :: bool, z :: bool) |- !(one(bool) * x === two(bool) * y * z)) {
      have(thesis) by Tautology.from(reverse.of(bool, x, y, z))
    }
    assert(!forwardApplication.withSorry && !reverseApplication.withSorry)

    val nullary = declaration.disjointness(empty, unused)
    val nullaryReverse = declaration.disjointness(unused, empty)
    val nullaryApplications = Theorem(!(empty(nat) === unused(nat)) /\ !(unused(bool) === empty(bool))) {
      have(thesis) by Tautology.from(nullary.of(nat), nullaryReverse.of(bool))
    }
    assert(!nullaryApplications.withSorry)

  test("schema binders are fresh against declared argument and type parameter names"):
    val declaration = adt(
      "disjointnessBinders",
      "disjointArgument0",
      Seq(
        ("one", Seq(("disjointArgument1", "disjointArgument0"))),
        ("two", Seq(("disjointArgument2", "disjointArgument0"), ("disjointArgument3", "disjointArgument0")))
      )
    )
    val Seq(one, two) = declaration.constructors: @unchecked
    val reverse = declaration.disjointness(two, one)
    val forward = declaration.disjointness(one, two)
    val applications = Theorem(
      (x :: nat, y :: nat, z :: nat) |-
        (!(two(nat) * x * y === one(nat) * z) /\ !(one(nat) * x === two(nat) * y * z))
    ) {
      have(thesis) by Tautology.from(reverse.of(nat, x, y, z), forward.of(nat, x, y, z))
    }
    assert(!applications.withSorry)

  test("equal and foreign constructors are rejected before proving anything"):
    val declaration = adt("disjointnessOwner", "A", Seq(("left", Seq.empty), ("right", Seq.empty)))
    val foreign = adt("disjointnessForeign", "A", Seq(("foreign", Seq.empty))).constructors.head
    val first = declaration.constructors.head
    val last = lisa.SetTheoryLibrary.last
    val language = lisa.SetTheoryLibrary.theory.language().toSet

    intercept[IllegalArgumentException](declaration.disjointness(first, first))
    intercept[IllegalArgumentException](declaration.disjointness(first, foreign))
    intercept[IllegalArgumentException](declaration.semantic.disjointness(first.semantic, first.semantic))
    intercept[IllegalArgumentException](declaration.semantic.disjointness(first.semantic, foreign.semantic))
    intercept[IllegalArgumentException](first.semantic.disjointness(first.semantic))
    intercept[IllegalArgumentException](first.semantic.disjointness(foreign.semantic))
    assert(lisa.SetTheoryLibrary.last == last)
    assert(lisa.SetTheoryLibrary.theory.language().toSet == language)
