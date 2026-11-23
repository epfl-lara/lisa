package lisa.hol

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.∈
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.UnorderedPair
import lisa.maths.SetTheory.Base.Symbols
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.Types.TypingHelpers.TypeAssign
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib._
import lisa.utils.prooflib.Exports._
import org.scalatest.funsuite.AnyFunSuite

class CleanSuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary
  private val x = variable[Ind](K.Identifier("cleanup-x"))
  private val y = variable[Ind](K.Identifier("cleanup-y"))
  private val a = TypeVariable(K.Identifier("cleanup-A"))
  private val b = TypeVariable(K.Identifier("cleanup-B"))

  private def checked(result: ProofJudgement): Thm =
    assert(result.isValid, result.toString)
    assert(!result.thm.kernel.usesSorry)
    result.thm

  test("remove unused typings and retain required type non-emptiness"):
    val premise = checked(BasicStep.RightRefl(Sequent(Set(x ∈ a, y ∈ b), Set(a === a))))
    val result = checked(ProofBuilder.withContext(HOLSteps.Clean.allVariables(premise)))
    assert(result.statement.left.exists(isSame(_, nonEmpty(a))))
    assert(result.statement.left.exists(isSame(_, nonEmpty(b))))
    assert(!result.statement.left.contains(x ∈ a))
    assert(!result.statement.left.contains(y ∈ b))
    val cleaned = checked(ProofBuilder.withContext(HOLSteps.Clean.allTypeVars(result)))
    assert(cleaned.statement.left.exists(isSame(_, nonEmpty(a))))
    assert(!cleaned.statement.left.exists(isSame(_, nonEmpty(b))))

  test("retain variables used in the conclusion or another typing assumption"):
    val statement = Sequent(Set(x ∈ a, y ∈ x), Set(y === y))
    val premise = checked(BasicStep.RightRefl(statement))
    assert(checked(ProofBuilder.withContext(HOLSteps.Clean.allVariables(premise))).statement == statement)
    assert(!ProofBuilder.withContext(HOLSteps.Clean.variable(TypeAssign(y, x))(premise)).isValid)

  test("remove concrete witness typings after existential introduction"):
    val premise = checked(BasicStep.RightRefl(Sequent(Set(x ∈ a), Set(x === x))))
    val existential = ∃(y, y === y)
    val generalized = checked(BasicStep.RightExists.withParameters(y === y, y, x)(premise)(Sequent(premise.left, Set(existential))))
    val result = checked(ProofBuilder.withContext(HOLSteps.Clean.allVariables(generalized)))
    assert(result.statement.left.size == 1)
    assert(result.statement.left.exists(isSame(_, nonEmpty(a))))
    assert(!result.statement.hasFree(x))

  test("discharge a constant type after hiding its concrete witness"):
    val premise = checked(BasicStep.RightRefl(Sequent(Set(x ∈ HOLHelperTheorems.𝔹), Set(x === x))))
    val existential = ∃(y, y === y)
    val generalized = checked(BasicStep.RightExists.withParameters(y === y, y, x)(premise)(Sequent(premise.left, Set(existential))))
    val result = checked(ProofBuilder.withContext(HOLSteps.Clean.all(generalized)))
    assert(result.statement.left.isEmpty)
    assert(isSameSequent(result.statement, () |- existential))

  test("order polymorphic witnesses before their non-emptiness dependencies"):
    val pair = UnorderedPair.unorderedPair
    val inhabited = checked(TacticProof:
      val member = have(UnorderedPair.leftInPair.of(Symbols.x := a, Symbols.y := b))
      val existence = ∃(x, x ∈ pair(a)(b))
      val witness = have(existence) by BasicStep.RightExists.withParameters(x ∈ pair(a)(b), x, a)(member.kernel)
      have(Set(nonEmpty(a), nonEmpty(b)) |- existence) by Weakening(witness))
    val constructor = HOLPolymorphicType[Ind >>: Ind >>: Ind](pair.id, Seq(a, b), inhabited)
    val base = HOLHelperTheorems.𝔹
    val expression = constructor(base)(constructor(base)(base)) ->: (base ->: base)
    val result = checked(TacticProof:
      val witnesses = HOLSteps.Clean.collectInstantiatingConstants(expression)
      assert(witnesses.size == 5)
      val assumptions: Set[Expr[Prop]] = witnesses.map((typ, _) => ∃(x, x ∈ typ): Expr[Prop]).toSet
      val premise = have(assumptions |- base === base) by RightRefl
      have(Discharge(witnesses.map(_._2)*)(premise)))
    assert(result.statement.left.isEmpty)

  test("reject mismatched typed-variable annotations"):
    val typed = TypedVariable(x.id, a)
    val premise = checked(BasicStep.RightRefl(Sequent(Set(typed ∈ b), Set(a === a))))
    val error = intercept[TacticException]:
      ProofBuilder.withContext(HOLSteps.Clean.variable(TypeAssign(typed, b))(premise))
    assert(error.getCause.isInstanceOf[LisaHOLException])

  test("preserve type annotations that are not syntactically free variables"):
    val typed = TypedVariable(x.id, a)
    val statement = Sequent(Set.empty, Set(typed === typed))
    assert(statement.hasFree(typed))
    assert(!statement.hasFree(a))
    val replaced = statement.substitute(a := b)
    assert(replaced.hasFree(typed))
    assert(replaced.freeVars.collect { case v: TypedVariable => v.typ } == Set(b))
