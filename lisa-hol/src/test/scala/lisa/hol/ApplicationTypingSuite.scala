package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems.𝔹
import lisa.hol.VarsAndFunctions.*
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofHelpers.*
import org.scalatest.funsuite.AnyFunSuite

class ApplicationTypingSuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary

  private def typing(term: Expr[Ind]): Thm =
    val result = Proof.withContext:
      Subproof:
        have(HOLSteps.HOLProofType(term))
    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    result.thm

  test("reuse application typings without losing their hypotheses"):
    HOLSteps.HOLProofType.resetCache()
    val f = TypedVariable(K.Identifier("reuse-function"), 𝔹 ->: 𝔹)
    val x = TypedVariable(K.Identifier("reuse-argument"), 𝔹)
    val inner = typing(f * x)
    val outer = typing(f * (f * x))
    assert(isSameSequent(inner.statement, (f :: f.typ, x :: x.typ) |- ((f * x) ∈ 𝔹)))
    assert(isSameSequent(outer.statement, (f :: f.typ, x :: x.typ) |- ((f * (f * x)) ∈ 𝔹)))
    assert(!outer.kernel.usesSorry)

  test("keep equal kernel applications with different annotations separate"):
    HOLSteps.HOLProofType.resetCache()
    val a = TypeVariable(K.Identifier("reuse-A"))
    val b = TypeVariable(K.Identifier("reuse-B"))
    val id = K.Identifier("reuse-polymorphic-function")
    val argumentId = K.Identifier("reuse-polymorphic-argument")
    for domain <- Seq(a, b) do
      val f = TypedVariable(id, domain ->: domain)
      val x = TypedVariable(argumentId, domain)
      assert(typing(f * x).statement.right.exists(isSame(_, (f * x) ∈ domain)))

  test("reuse application premises without traversing the whole term for a context"):
    HOLSteps.HOLProofType.resetCache()
    val f = TypedVariable(K.Identifier("reuse-context-function"), 𝔹 ->: 𝔹)
    val x = TypedVariable(K.Identifier("reuse-context-argument"), 𝔹)
    val term = new App[Ind, Ind](app(f), x):
      override def freeVars: Set[Variable[?]] = throw new AssertionError("Unnecessary context traversal")
    assert(typing(term).statement.right.exists(isSame(_, term ∈ 𝔹)))

  test("substitute codomain metadata even when the kernel codomain is independent"):
    HOLSteps.HOLProofType.resetCache()
    val bound = variable[Ind](K.Identifier("reuse-bound"))
    val resultType = TypedVariable(K.Identifier("reuse-result-type"), bound)
    val f = TypedVariable(K.Identifier("reuse-metadata-function"), Pi(𝔹)(λ(bound, resultType)))
    val x = TypedVariable(K.Identifier("reuse-metadata-argument"), 𝔹)
    val result = typing(f * x)
    val retained = result.statement.right.head match
      case _ ∈ (typ: TypedVariable) => typ
      case other => fail(s"Expected an annotated codomain, got $other")
    assert(retained.typ == x)

  test("retain the general checker for dependent applications"):
    HOLSteps.HOLProofType.resetCache()
    val bound = variable[Ind](K.Identifier("reuse-dependent-bound"))
    val f = TypedVariable(K.Identifier("reuse-dependent-function"), Pi(𝔹)(λ(bound, bound)))
    val x = TypedVariable(K.Identifier("reuse-dependent-argument"), 𝔹)
    assert(typing(f * x).statement.right.exists(isSame(_, (f * x) ∈ x)))

  test("do not cache a local-context application as a canonical proof"):
    HOLSteps.HOLProofType.resetCache()
    val f = variable[Ind](K.Identifier("reuse-local-function"))
    val x = variable[Ind](K.Identifier("reuse-local-argument"))
    val result = Proof.withContext:
      summon[Proof].assume(Set(f ∈ (𝔹 ->: 𝔹), x ∈ 𝔹))
      ProofJudgement(HOLSteps.HOLProofType(f * x))
    assert(result.isValid)
    assert(result.thm.statement.left.nonEmpty)
    intercept[LisaHOLException](typing(f * x))

  test("preserve sorry dependencies when reusing application typings"):
    HOLSteps.HOLProofType.resetCache()
    val raw = Constant[Ind](K.Identifier("reuse-hole-function"))
    SetTheoryLibrary.addSymbol(raw)
    val fact = BasicStep.Sorry(() |- raw ∈ (𝔹 ->: 𝔹)).thm
    val f = TypedConstant(raw.id, 𝔹 ->: 𝔹, fact)
    val x = TypedVariable(K.Identifier("reuse-hole-argument"), 𝔹)
    assert(typing(f * x).kernel.usesSorry)
    assert(typing(f * (f * x)).kernel.usesSorry)

  test("preserve tracked proof holes when reusing application typings"):
    HOLSteps.HOLProofType.resetCache()
    val raw = Constant[Ind](K.Identifier("reuse-assumed-function"))
    SetTheoryLibrary.addSymbol(raw)
    val statement = () |- raw ∈ (𝔹 ->: 𝔹)
    val fact = Thm(statement, lisa.kernel.proof.Assume(using SetTheoryLibrary.theory)(statement.underlying).toOption.get)
    val f = TypedConstant(raw.id, 𝔹 ->: 𝔹, fact)
    val x = TypedVariable(K.Identifier("reuse-assumed-argument"), 𝔹)
    for term <- Seq(f * x, f * (f * x)) do
      val result = typing(term).kernel
      assert(result.assumptions == Set(statement.underlying))
      assert(!result.usesSorry)

  test("reject incompatible argument types"):
    HOLSteps.HOLProofType.resetCache()
    val f = TypedVariable(K.Identifier("reuse-invalid-function"), 𝔹 ->: 𝔹)
    val x = TypedVariable(K.Identifier("reuse-invalid-argument"), 𝔹 ->: 𝔹)
    intercept[LisaHOLException](typing(f * x))

  test("accept alpha-equivalent argument types"):
    HOLSteps.HOLProofType.resetCache()
    val bound = variable[Ind](K.Identifier("reuse-alpha-bound"))
    val domain = Pi(𝔹)(λ(bound, 𝔹))
    val f = TypedVariable(K.Identifier("reuse-alpha-function"), domain ->: 𝔹)
    val x = TypedVariable(K.Identifier("reuse-alpha-argument"), 𝔹 ->: 𝔹)
    val result = typing(f * x)
    assert(result.statement.right.exists(isSame(_, (f * x) ∈ 𝔹)))
    assert(!result.kernel.usesSorry)
