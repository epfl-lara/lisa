package lisa.maths.SetTheory.Types.ADT.height

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks finite-union inclusion proofs and reuse of their shared schema.
 */
class FiniteUnionSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val x, y, z = variable[Ind]

  test("component inclusion handles every position, duplicates, and the empty set"):
    val components: Seq[Expr[Ind]] = Seq(x, ∅, y, x, z)
    for elems <- Seq(components, Seq[Expr[Ind]](∅), Seq(x)); member <- elems.distinct do
      val checked = Theorem(x === y |- member ⊆ FiniteUnion.unionList(elems)) {
        lisa.SetTheoryLibrary.assume(x === y)
        val inclusion = FiniteUnion.memberSubsetOfUnionList(elems, member)
        have(thesis) by Weakening(inclusion)
      }
      assert(!checked.withSorry)

  test("missing components are rejected, including the implicit empty seed"):
    val checked = Theorem(x === x) {
      intercept[IllegalArgumentException](FiniteUnion.memberSubsetOfUnionList(Seq.empty, x))
      intercept[IllegalArgumentException](FiniteUnion.memberSubsetOfUnionList(Seq(x, y), z))
      intercept[IllegalArgumentException](FiniteUnion.memberSubsetOfUnionList(Seq(x, y), ∅))
      have(thesis) by RightRefl
    }
    assert(!checked.withSorry)

  test("component proofs reuse the subset schema across proof contexts"):
    for elems <- Seq(Seq(x, y, z), Seq(z, x, y)) do
      val checked = Theorem(elems.head ⊆ FiniteUnion.unionList(elems)) {
        val first = FiniteUnion.memberSubsetOfUnionList(elems, elems.head)
        val before = lisa.SetTheoryLibrary.last
        for member <- elems do
          val inclusion = FiniteUnion.memberSubsetOfUnionList(elems, member)
          have(inclusion.statement) by Restate.from(inclusion)
        assert(lisa.SetTheoryLibrary.last == before)
        have(thesis) by Restate.from(first)
      }
      assert(!checked.withSorry)
