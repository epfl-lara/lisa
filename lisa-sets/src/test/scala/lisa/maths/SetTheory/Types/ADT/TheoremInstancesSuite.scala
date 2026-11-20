package lisa.maths.SetTheory.Types.ADT

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.maths.SetTheory.Types.ADT.library.bool
import lisa.maths.SetTheory.Types.ADT.library.cons
import lisa.maths.SetTheory.Types.ADT.library.list
import lisa.maths.SetTheory.Types.ADT.library.nat
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiate
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.N
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.wellTypedFormula
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks that specialized facts reuse their schemas without registering theorem wrappers.
 */
class TheoremInstancesSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager

  private val x, y, z, h, g, n, m = variable[Ind]

  test("empty and identity instantiation return the original theorem"):
    val base = Theorem.generated(x === y |- x === y) {
      have(thesis) by Hypothesis
    }
    val checked = Theorem.generated(base.statement) {
      val before = lisa.SetTheoryLibrary.theorems.all.size
      val empty = instantiate(base, Seq.empty)
      val identity = instantiate(base, Seq(x := x, y := y))
      assert(empty.asInstanceOf[AnyRef] eq base.thm)
      assert(identity.asInstanceOf[AnyRef] eq base.thm)
      assert(lisa.SetTheoryLibrary.theorems.all.size == before)
      have(thesis) by Restate.from(identity)
    }
    assert(!checked.hasErrorsOrSorry)

  test("one substitution list remains simultaneous while chained instances remain sequential"):
    val base = Theorem.generated(x === y |- x === y) {
      have(thesis) by Hypothesis
    }
    val checked = Theorem.generated(y === z |- y === z) {
      val before = lisa.SetTheoryLibrary.theorems.all.size
      val simultaneous = instantiate(base, Seq(x := y, y := z))
      val sequential = instantiate(base, Seq(x := y)).of(y := z)
      val lastWins = instantiate(base, Seq(x := z, x := x))
      assert(simultaneous.statement.left == Set(y === z))
      assert(sequential.statement.left == Set(z === z))
      assert(lastWins.statement.left == Set(x === y))
      assert(lisa.SetTheoryLibrary.theorems.all.size == before)
      have(z === z |- z === z) by Restate.from(sequential)
      have(base.statement) by Restate.from(lastWins)
      have(thesis) by Restate.from(simultaneous)
    }
    assert(!checked.hasErrorsOrSorry)

  test("height validity specializes in separate proofs without registering wrappers"):
    val height = list.semantic.height
    val parameter = list.typeVariablesSeq.head
    for target <- Seq(bool, nat) do
      val substitutions: Seq[TypeSubstitution] = Seq(parameter := target)
      val heightFunction = height.function.substitute(substitutions*)
      val checked = Theorem.generated(height.predicateAt(substitutions)(heightFunction)) {
        val base = height.validAt(Seq.empty)
        val identity = height.validAt(Seq(parameter := parameter))
        assert(base.asInstanceOf[AnyRef] eq identity.asInstanceOf[AnyRef])
        val before = lisa.SetTheoryLibrary.theorems.all.size
        val specialized = height.validAt(substitutions)
        val repeated = height.validAt(substitutions)
        assert(specialized.statement == repeated.statement)
        assert(lisa.SetTheoryLibrary.theorems.all.size == before)
        have(thesis) by Restate.from(repeated)
      }
      assert(!checked.hasErrorsOrSorry)

  test("constructor height schemas are shared across arguments and proof contexts"):
    val constructor = cons.semantic
    val height = list.semantic.height
    val parameter = list.typeVariablesSeq.head
    for target <- Seq(bool, nat) do
      val substitutions: Seq[TypeSubstitution] = Seq(parameter := target)
      val stageTyping = constructor.heightTypingFormula(app(h)(n)).substitute(substitutions*)
      val resultTyping = wellTypedFormula(constructor.semanticSignature2).substitute(substitutions*)
      val checked = Theorem.generated((height.predicateAt(substitutions)(h), n ∈ N, stageTyping) |- resultTyping) {
        def exercise(using proof: lisa.SetTheoryLibrary.ProofBuilder): Unit =
          val typing = constructor.semanticTypingFromHeightAt(substitutions)(h, n)
          val equality = constructor.appliedEqualityFromStructuralAt(substitutions)(h, n, x)
          val recursive = constructor.recursiveArgInHeightAt(substitutions)(h, n)
          for fact <- Seq(typing, equality, recursive) do have(fact.statement) by Restate.from(fact)

          val before = lisa.SetTheoryLibrary.theorems.all.size
          val repeated = Seq(
            constructor.semanticTypingFromHeightAt(substitutions)(g, m),
            constructor.appliedEqualityFromStructuralAt(substitutions)(g, m, y),
            constructor.recursiveArgInHeightAt(substitutions)(g, m)
          )
          assert(lisa.SetTheoryLibrary.theorems.all.size == before)
          for fact <- repeated do have(fact.statement) by Restate.from(fact)
          have(thesis) by Restate.from(typing)
        exercise
      }
      assert(!checked.hasErrorsOrSorry)

  test("specialized accessors still reject invalid type substitutions before proving anything"):
    val height = list.semantic.height
    val constructor = cons.semantic
    val parameter = list.typeVariablesSeq.head
    val foreign = Variable[Ind]("theoremInstanceForeign")
    val boolType = bool
    val natType = nat
    val checked = Theorem.generated(x === x) {
      val before = lisa.SetTheoryLibrary.theorems.all.size
      intercept[IllegalArgumentException](height.validAt(Seq(foreign := foreign)))
      intercept[IllegalArgumentException](height.zeroAt(Seq(parameter := boolType, parameter := natType)))
      intercept[IllegalArgumentException](constructor.semanticTypingFromHeightAt(Seq(foreign := foreign))(h, n))
      assert(lisa.SetTheoryLibrary.theorems.all.size == before)
      have(thesis) by RightRefl
    }
    assert(!checked.hasErrorsOrSorry)
