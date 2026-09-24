package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.*
import lisa.maths.SetTheory.Cardinal.Predef.universeOf
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
    val theorem = result.justification.get
    assert(theorem.statement.right.exists(isSame(_, expected)), s"Expected $expected, obtained ${theorem.statement}")

  private def sorry(statement: Sequent): Thm =
    BasicStep.Sorry(statement).justification.get

  private def assertChecked(result: ProofCarrier[?], expected: Sequent): Thm =
    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    val theorem = result.justification.get
    assert(!theorem.kernel.usesSorry)
    assert(theorem.statement == expected, s"Expected $expected, obtained ${theorem.statement}")
    theorem

  test("checking an exact type reuses the inferred hypothesis without dropping its premise"):
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(x ∈ A, y ∈ B), x, A)

    val theorem = assertChecked(result, x ∈ A |- x ∈ A)
    assert(theorem.kernel.rule == K.Hypothesis)

  test("checking an exact dependent function type does not build a covariance proof"):
    val family = variable[Ind >>: Ind](K.Identifier("typecheck-test-family"))
    val typ = Pi(A)(λ(x, family(x)))
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(f ∈ typ), f, typ)

    val theorem = assertChecked(result, f ∈ typ |- f ∈ typ)
    assert(theorem.kernel.rule == K.Hypothesis)

  test("checking a beta-equivalent type restates the target and retains the inferred premise"):
    val expectedType = λ(y, y)(A)
    assert(expectedType != A && isSame(expectedType, A))

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(x ∈ A), x, expectedType)

    val theorem = assertChecked(result, x ∈ A |- x ∈ expectedType)
    assert(theorem.kernel.rule == K.Restate)

  test("checking an alpha-equivalent dependent type respects both binders"):
    val family = variable[Ind >>: Ind](K.Identifier("typecheck-test-alpha-family"))
    val inferredType = Pi(A)(λ(x, family(x)))
    val expectedType = Pi(A)(λ(y, family(y)))
    assert(inferredType != expectedType && isSame(inferredType, expectedType))

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(f ∈ inferredType), f, expectedType)

    val theorem = assertChecked(result, f ∈ inferredType |- f ∈ expectedType)
    assert(theorem.kernel.rule == K.Restate)

  test("checking retains a genuine inclusion premise"):
    val context = Set(x ∈ A, A ⊆ B)
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(context, x, B)

    val theorem = assertChecked(result, context |- x ∈ B)
    assert(theorem.kernel.rule == K.Cut)

  test("checking still lifts a term into the next universe"):
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(x ∈ A), x, universeOf(A))

    assertChecked(result, x ∈ A |- x ∈ universeOf(A))

  test("checking still constructs covariance for genuinely different function types"):
    val inferredType = A ->: B
    val expectedType = A ->: universeOf(B)
    assert(!isSame(inferredType, expectedType))

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(f ∈ inferredType), f, expectedType)

    assertChecked(result, f ∈ inferredType |- f ∈ expectedType)

  test("checking does not mistake a free variable for an alpha-renamed binder"):
    val family = variable[Ind >>: Ind](K.Identifier("typecheck-test-free-family"))
    val inferredType = Pi(A)(λ(x, family(x)))
    val expectedType = Pi(A)(λ(y, family(x)))
    assert(!isSame(inferredType, expectedType))

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(f ∈ inferredType), f, expectedType)

    assert(!result.isValid)

  test("checking does not reuse a typing for an unrelated type or context"):
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(x ∈ A), x, B)
    assert(!result.isValid)

    val valid = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(x ∈ B), x, B)
    assertChecked(valid, x ∈ B |- x ∈ B)

  test("a matching result type does not hide an invalid argument typing"):
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set(f ∈ (A ->: B), x ∈ C), f * x, B)

    assert(!result.isValid)

  test("equal nested dependent types use subset reflexivity without binder assumptions"):
    val family = variable[Ind >>: Ind >>: Ind](K.Identifier("typecheck-test-nested-family"))
    val typ = Pi(A)(λ(x, Pi(B)(λ(y, family(x)(y)))))
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.subsetProof(Set.empty, typ, typ)

    val theorem = assertChecked(result, () |- typ ⊆ typ)
    assert(theorem.kernel.rule == K.InstSchema)

  test("inference threads the intermediate type through nested applications"):
    val term = f * x * y
    val context = Set(f ∈ (A ->: B ->: C), x ∈ A, y ∈ B)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.inferProof(context, term)

    assertChecked(result, context |- term ∈ C)

  test("inference threads the body type out of an abstraction"):
    val term = fun(TypeAssign(x, A), x)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.inferProof(Set.empty, term)

    assertChecked(result, () |- term ∈ Pi(A)(λ(x, A)))

  test("checking reuses the inferred type of an application"):
    val term = f * x
    val context = Set(f ∈ (A ->: B), x ∈ A)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(context, term, B)

    assertChecked(result, context |- term ∈ B)

  test("checking an abstraction reuses its body typing without leaking the binder"):
    val term = fun(TypeAssign(x, A), x)
    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set.empty, term, A ->: A)

    assertChecked(result, () |- term ∈ (A ->: A))

  test("exact constant typing reuse preserves the original justification and holes"):
    val raw = constant[Ind](K.Identifier("typecheck-test-reused-constant"))
    SetTheoryLibrary.addSymbol(raw)
    val typing = sorry(() |- raw ∈ A)
    val typed = TypedConstant(raw.id, A, typing)

    val result = Proof.withContext(using SetTheoryLibrary):
      Typecheck.checkProof(Set.empty, typed, A)

    assert(result.isValid)
    assert(result.justification.get eq typing)
    assert(result.justification.get.kernel.usesSorry)

  test("typing reuse preserves axiom dependencies"):
    val raw = constant[Ind](K.Identifier("typecheck-test-axiom-constant"))
    SetTheoryLibrary.addSymbol(raw)
    val statement = () |- raw ∈ A
    val typing = Thm(statement, K.Axiom(using SetTheoryLibrary.theory)(statement.underlying).toOption.get)
    val typed = TypedConstant(raw.id, A, typing)

    for expectedType <- Seq(A, λ(y, y)(A)) do
      val result = Proof.withContext(using SetTheoryLibrary):
        Typecheck.checkProof(Set.empty, typed, expectedType)
      val theorem = assertChecked(result, () |- raw ∈ expectedType)
      assert(theorem.kernel.axioms == Set(statement.underlying))

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
