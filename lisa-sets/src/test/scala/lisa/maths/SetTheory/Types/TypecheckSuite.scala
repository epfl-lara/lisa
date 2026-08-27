package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.*
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.K
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.BasicStep
import lisa.utils.prooflib.Proof
import lisa.utils.prooflib.ProofCarrier
import lisa.utils.prooflib.Thm
import org.scalatest.funsuite.AnyFunSuite

class TypecheckSuite extends AnyFunSuite:
  private given SetTheoryLibrary.type = SetTheoryLibrary

  private val A = variable[Ind](K.Identifier("typecheck-test-A"))
  private val B = variable[Ind](K.Identifier("typecheck-test-B"))
  private val C = variable[Ind](K.Identifier("typecheck-test-C"))
  private val f = variable[Ind](K.Identifier("typecheck-test-f"))
  private val x = variable[Ind](K.Identifier("typecheck-test-x"))
  private val y = variable[Ind](K.Identifier("typecheck-test-y"))

  private def assertTyping(result: ProofCarrier[?], expected: Expr[Prop]): Unit =
    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    val theorem = result.destruct._1
    assert(theorem.statement.right.exists(isSame(_, expected)), s"Expected $expected, obtained ${theorem.statement}")

  private def sorry(statement: Sequent): Thm =
    BasicStep.Sorry(statement).destruct._1

  test("inference threads the intermediate type through nested applications"):
    val term = f * x * y
    val context = Set(f ∈ (A ->: B ->: C), x ∈ A, y ∈ B)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.inferProof(context, term)

    assertTyping(result, term ∈ C)

  test("inference threads the body type out of an abstraction"):
    val term = fun(TypeAssign(x, A), x)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.inferProof(Set.empty, term)

    assertTyping(result, term ∈ (A ->: A))

  test("checking consumes the inferred type payload during conversion"):
    val term = f * x
    val context = Set(f ∈ (A ->: B), x ∈ A)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(context, term, B)

    assertTyping(result, term ∈ B)

  test("functional constants return their instantiated output type"):
    val parameter = variable[Ind](K.Identifier("typecheck-test-parameter"))
    val raw = constant[Ind >>: Ind](K.Identifier("typecheck-test-functional"))
    SetTheoryLibrary.addSymbol(raw)
    val typing = sorry(() |- forall(parameter, top ==> (raw(parameter) ∈ parameter)))
    val functional = TypedConstantFunctional[Ind >>: Ind](raw.id, FunctionalClass(Seq(None), Seq(parameter), parameter), typing)
    val term = functional(A)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.inferProof(Set.empty, term)

    assertTyping(result, term ∈ A)
