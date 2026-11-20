package lisa.maths.SetTheory.Types.ADT.height

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks finite-union inclusion proofs and reuse of their shared schema.
 */
class FiniteUnionSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager

  private val x, y, z = variable[Ind]

  test("component inclusion handles every position, duplicates, and the empty set"):
    val components: Seq[Expr[Ind]] = Seq(x, ∅, y, x, z)
    for elems <- Seq(components, Seq[Expr[Ind]](∅), Seq(x)); member <- elems.distinct do
      val checked = Theorem.generated(x === y |- member ⊆ FiniteUnion.unionList(elems)) {
        lisa.utils.prooflib.ProofHelpers.assume(x === y)
        val inclusion = FiniteUnion.memberSubsetOfUnionList(elems, member)
        have(thesis) by Weakening(inclusion)
      }
      assert(!checked.hasErrorsOrSorry)

  test("missing components are rejected, including the implicit empty seed"):
    val checked = Theorem.generated(x === x) {
      intercept[IllegalArgumentException](FiniteUnion.memberSubsetOfUnionList(Seq.empty, x))
      intercept[IllegalArgumentException](FiniteUnion.memberSubsetOfUnionList(Seq(x, y), z))
      intercept[IllegalArgumentException](FiniteUnion.memberSubsetOfUnionList(Seq(x, y), ∅))
      have(thesis) by RightRefl
    }
    assert(!checked.hasErrorsOrSorry)

  test("component proofs reuse the subset schema across proof contexts"):
    for elems <- Seq(Seq(x, y, z), Seq(z, x, y)) do
      val checked = Theorem.generated(elems.head ⊆ FiniteUnion.unionList(elems)) {
        val first = FiniteUnion.memberSubsetOfUnionList(elems, elems.head)
        val before = lisa.SetTheoryLibrary.theorems.all.size
        for member <- elems do
          val inclusion = FiniteUnion.memberSubsetOfUnionList(elems, member)
          have(inclusion.statement) by Restate.from(inclusion)
        assert(lisa.SetTheoryLibrary.theorems.all.size == before)
        have(thesis) by Restate.from(first)
      }
      assert(!checked.hasErrorsOrSorry)
