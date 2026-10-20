package lisa.hol

import lisa.hol.HOLHelperTheorems.*
import lisa.hol.VarsAndFunctions.*
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class HOLRegressionSuite extends AnyFunSuite:
  private object Proofs extends lisa.HOL:
    val A, B = typevar
    val x = typedvar(A)
    val f = typedvar(A ->: B)

    val reflexivity = HOLTheorem(x =:= x):
      val result = have(ExtendedHOLSteps._REFL(x))
      have(thesis) by Weakening(result)

    val abstraction = HOLTheorem(fun(x, f * x) =:= fun(x, f * x)):
      val body = have(ExtendedHOLSteps._REFL(f * x))
      val result = have(ExtendedHOLSteps._ABS(x)(body))
      have(thesis) by Weakening(result)

    val beta = HOLTheorem((fun(x, f * x) * x) =:= (f * x)):
      val result = have(ExtendedHOLSteps._BETA_CONV(fun(x, f * x) * x))
      have(thesis) by Weakening(result)

    val identityCarrier = DEF(λ(A, A))
    val identityNonEmpty = Theorem(nonEmpty(A) |- ∃(x, x ∈ identityCarrier(A))):
      val premise = have(nonEmpty(A) |- nonEmpty(A)) by Hypothesis
      have(thesis) by lisa.automation.Substitution.Apply(identityCarrier.definition)(premise)
    val identityType = HOLPolymorphicType[Ind >>: Ind](identityCarrier.id, Seq(A), identityNonEmpty)
    val instantiatedNonEmpty = Theorem(nonEmpty(B) |- ∃(x, x ∈ identityType(B))):
      val result = have(TypeNonEmptyProof(identityType(B)))
      have(thesis) by Restate.from(result)

    val cleanedComposite = Theorem(⊤):
      val premise = have(∃(x, x ∈ identityType(𝔹)) |- ⊤) by Restate
      val cleaned = have(HOLSteps.Clean.all(premise))
      have(thesis) by Weakening(cleaned)

    // This constructor is typed even for an empty parameter set.
    val totalCarrier = DEF(λ(A, One))
    val totalTyping = Theorem(∀(A, totalCarrier(A) ∈ 𝔹)):
      val typed = have(totalCarrier(A) ∈ 𝔹) by lisa.automation.Substitution.Apply(totalCarrier.definition)(One.justif)
      have(thesis) by RightForall.withParameters(totalCarrier(A) ∈ 𝔹, A)(typed)
    val totalConstant = new lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional[Ind >>: Ind](
      totalCarrier.id, FunctionalClass(List(None), List(A), 𝔹), totalTyping
    )

    def check(theorem: lisa.SetTheoryLibrary.THM): Unit =
      assert(theorem.proofStatistics.kernelSize > 0)
      assert(!theorem.innerJustification.withSorry)

  test("check primitive HOL proofs with the SC checker"):
    Proofs.check(Proofs.reflexivity)
    Proofs.check(Proofs.abstraction)
    Proofs.check(Proofs.beta)

  test("distinguish HOL variable types when their printed names agree"):
    val first = Import.Transformers.mkTypedVar("same-name", Proofs.A)
    val second = Import.Transformers.mkTypedVar("same-name", Proofs.B)
    assert(first.id != second.id)
    assert(first.underlying != second.underlying)
    assert(Import.Transformers.mkTypedVar("same-name", Proofs.A).id == first.id)

  test("instantiate a polymorphic type non-emptiness theorem"):
    Proofs.check(Proofs.instantiatedNonEmpty)

  test("clean non-emptiness exposed by a polymorphic type constructor"):
    Proofs.check(Proofs.cleanedComposite)

  test("include erased type annotations in the HOL typing cache key"):
    import lisa.SetTheoryLibrary.*
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    val first = TypedVariable(K.Identifier("cache-variable"), Proofs.A)
    val second = TypedVariable(K.Identifier("cache-variable"), Proofs.B)
    HOLSteps.HOLProofType.resetCache()
    val firstTyping = HOLSteps.HOLProofType(first)
    val secondTyping = HOLSteps.HOLProofType(second)
    assert(firstTyping.statement.right != secondTyping.statement.right)
    assert(HOLSteps.HOLProofType.cacheSize == 2)
    assert(theory.getTheorem(firstTyping.innerJustification.asInstanceOf[theory.Theorem].name).get.proposition == firstTyping.statement.underlying)
    assert(theory.getTheorem(secondTyping.innerJustification.asInstanceOf[theory.Theorem].name).get.proposition == secondTyping.statement.underlying)

  test("keep canonical typing free of annotation-only non-emptiness premises"):
    import lisa.SetTheoryLibrary.*
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    val typing = HOLSteps.HOLProofType(Proofs.x)
    assert(typing.statement.left == typing.statement.right)
    Proofs.check(typing.asInstanceOf[THM])

  test("retry local typing without caching its assumptions"):
    import lisa.SetTheoryLibrary.*
    import lisa.maths.SetTheory.Functions.Predef.*
    import lisa.maths.SetTheory.Types.TypingHelpers.*
    import lisa.utils.fol.FOL.*
    val f, x = variable[Ind]
    val context = Set(f ∈ (Proofs.A ->: Proofs.B), x ∈ Proofs.A)
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    context.foreach(proof.addAssumption)
    HOLSteps.HOLProofType.resetCache()
    val typing = HOLSteps.HOLProofType(f * x)
    assert(typing.statement.left == context)
    assert(HOLSteps.HOLProofType.cacheSize == 0)
    Proofs.check(typing.asInstanceOf[THM])
    proof.cleanAssumptions
    assertThrows[LisaHOLException](HOLSteps.HOLProofType(f * x))

  test("use the constructor's requirements, not every free type's non-emptiness"):
    import lisa.SetTheoryLibrary.*
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    val typing = HOLSteps.HOLProofType(Proofs.totalConstant(Proofs.A))
    assert(typing.statement.left.isEmpty)
    Proofs.check(typing.asInstanceOf[THM])

  test("check both subset type-definition theorems"):
    Proofs.check(basics.TypeDefs.typeNonEmpty)
    Proofs.check(basics.TypeDefs.absTyping)
    Proofs.check(basics.TypeDefs.repTyping)
    Proofs.check(basics.TypeDefs.absThm)
    Proofs.check(basics.TypeDefs.repThm)

  test("share checked sparse steps across named theorems"):
    import lisa.hol.extractor.*
    val p = "v(step-store-p)(c[bool][])"
    given ExtractorContext = new ExtractorContext(
      Iterator(ProofLine(2, ASSUME(p))),
      Iterator(TheoremStatement(2, RawSequent(List(p), p)))
    )
    val store = new Import.StepStore
    val first = store(2)
    assert(store(2) eq first)
    assert(store.size == 1)
    val named = store.theorem(TheoremRef(2, "STEP_STORE_ALIAS"))
    assert(named.statement.right == first.statement.right)
    assert(first.statement.left.subsetOf(named.statement.left))
    assert(first.statement.left.size == 1) // Do not cache the named theorem's extra typing context.
    assert(store.size == 1)
    Proofs.check(first.asInstanceOf[lisa.SetTheoryLibrary.THM])
    Proofs.check(named.asInstanceOf[lisa.SetTheoryLibrary.THM])
    assertThrows[NoSuchElementException](store(1))
    assertThrows[IllegalArgumentException](store.premise(2, 2))

  test("reject a mismatched intermediate statement in debug mode"):
    import lisa.hol.extractor.*
    given ExtractorContext = new ExtractorContext(
      Iterator(ProofLine(4, ASSUME("v(step-store-p)(c[bool][])"))),
      Iterator(TheoremStatement(4, RawSequent(Nil, "v(step-store-q)(c[bool][])")))
    )
    val store = new Import.StepStore()(using summon[ExtractorContext], Import.Logging.LoggingMode.Debug)
    intercept[Exception](store(4))
    assert(store.size == 0)

  test("do not carry an erased type's non-emptiness through shared REFL and MK_COMB"):
    import lisa.hol.extractor.*
    def function(in: String, out: String) = s"c[fun][[$in][$out]]"
    val bool = "c[bool][]"
    val domain = function("v[A]", function("v[B]", bool))
    val functionType = function(domain, "v[A]")
    val f = s"v(shared-f)($functionType)"
    val r = s"v(shared-r)($domain)"
    def reflexive(term: String, typ: String) = s"C(C(c(=)(${function(typ, function(typ, bool))}))($term))($term)"
    given ExtractorContext = new ExtractorContext(
      Iterator(ProofLine(10, REFL(f)), ProofLine(11, REFL(r)), ProofLine(12, MK_COMB(10, 11))),
      Iterator(
        TheoremStatement(10, RawSequent(Nil, reflexive(f, functionType))),
        TheoremStatement(11, RawSequent(Nil, reflexive(r, domain))),
        TheoremStatement(12, RawSequent(Nil, reflexive(s"C($f)($r)", "v[A]")))
      )
    )
    val store = new Import.StepStore()(using summon[ExtractorContext], Import.Logging.LoggingMode.Debug)
    val result = store(12)
    assert(!result.statement.left.contains(nonEmpty(Proofs.B)))
    Proofs.check(result.asInstanceOf[lisa.SetTheoryLibrary.THM])

  test("skip debug assertions outside debug mode"):
    import Import.Logging.*
    var evaluated = false
    debugAssert(using LoggingMode.Silent)({ evaluated = true; false }, "unused")
    assert(!evaluated)
    assertThrows[AssertionError](debugAssert(using LoggingMode.Debug)(false, "checked"))
