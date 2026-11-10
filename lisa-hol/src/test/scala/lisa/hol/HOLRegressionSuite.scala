package lisa.hol

import lisa.hol.HOLHelperTheorems.*
import lisa.hol.VarsAndFunctions.*
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class HOLRegressionSuite extends AnyFunSuite:
  private def checkTyping(proof: lisa.SetTheoryLibrary.BaseProof)(typing: proof.Fact): Unit =
    import lisa.SetTheoryLibrary.*
    given proof.type = proof
    have(typing)
    assert(K.SCProofChecker.checkSCProof(proof.toSCProof) match
      case K.SCProofCheckerJudgement.SCValidProof(_, usesSorry) => !usesSorry
      case _ => false)
    assert(proof.justifications.forall(justification => !justification.withSorry))
    assert(!proof.justifications.exists(_.fullName.startsWith("lisa.hol.HOLProofType.")))

  private object Proofs extends lisa.HOL:
    val A, B = typevar
    val x, y, z = typedvar(A)
    val f = typedvar(A ->: B)

    val reflexivity = HOLTheorem(x =:= x):
      val result = have(ExtendedHOLSteps._REFL(x))
      have(thesis) by Weakening(result)

    val transitivity = HOLTheorem((x =:= y, y =:= z) |- (x =:= z)):
      val first = HOLassume(x =:= y)
      val second = HOLassume(y =:= z)
      have(ExtendedHOLSteps._TRANS(first, second))

    val compositeTransitivity = HOLTheorem((f * x =:= f * y, f * y =:= f * z) |- (f * x =:= f * z)):
      val first = HOLassume(f * x =:= f * y)
      val second = HOLassume(f * y =:= f * z)
      have(ExtendedHOLSteps._TRANS(first, second))

    val reflexiveTransitivity = HOLTheorem(x =:= x):
      val reflexivity = have(ExtendedHOLSteps._REFL(x))
      have(ExtendedHOLSteps._TRANS(reflexivity, reflexivity))

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

  test("check proof-backed TRANS on variable, composite and reflexive equalities"):
    Proofs.check(Proofs.transitivity)
    Proofs.check(Proofs.compositeTransitivity)
    Proofs.check(Proofs.reflexiveTransitivity)

  test("check closure and transfinite recursion without admitted dependencies"):
    for theorem <- Seq(
      lisa.maths.SetTheory.Relations.Operations.Closure.reflexiveClosureValid,
      lisa.maths.SetTheory.Ordinals.TransfiniteRecursion.transfiniteRecursion
    ) do assert(!theorem.withSorry, theorem.fullName)

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
    val firstTyping = HOLSteps.HOLProofType(first)
    val secondTyping = HOLSteps.HOLProofType(second)
    assert(firstTyping.statement.right != secondTyping.statement.right)
    assert(HOLSteps.HOLProofType.cacheSize == 2)
    checkTyping(proof)(firstTyping)
    checkTyping(proof)(secondTyping)

  test("keep canonical typing free of annotation-only non-emptiness premises"):
    import lisa.SetTheoryLibrary.*
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    val typing = HOLSteps.HOLProofType(Proofs.x)
    assert(typing.statement.left == typing.statement.right)
    checkTyping(proof)(typing)

  test("reuse typing steps only within their root proof without registering theorems"):
    import lisa.SetTheoryLibrary.*
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    val before = lisa.kernel.proof.TheoremRegistrySnapshot.names(theory)
    val first = HOLSteps.HOLProofType(Proofs.x)
    assert(HOLSteps.HOLProofType(Proofs.x).eq(first))
    val other = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    val second = HOLSteps.HOLProofType(using other)(Proofs.x)
    assert(!first.eq(second))
    assert(first.host.eq(proof))
    assert(second.host.eq(other))
    assert(first.bot == second.bot)
    assert(lisa.kernel.proof.TheoremRegistrySnapshot.names(theory) == before)
    checkTyping(proof)(first)
    checkTyping(other)(second)

  test("reuse canonical typings across nested tactics without inheriting assumptions"):
    import lisa.SetTheoryLibrary.*
    import lisa.maths.SetTheory.Functions.Predef.*
    import lisa.maths.SetTheory.Types.TypingHelpers.*
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    val unrelated = variable[Prop]
    proof.addAssumption(unrelated)
    val firstChild = proof.newInnerProof(None)
    val first = HOLSteps.HOLProofType(using firstChild)(Proofs.f * Proofs.x)
    val nested = firstChild.newInnerProof(None)
    val repeated = HOLSteps.HOLProofType(using nested)(Proofs.f * Proofs.x)
    val sibling = proof.newInnerProof(None)
    val last = HOLSteps.HOLProofType(using sibling)(Proofs.f * Proofs.x)
    assert(first.bot == repeated.bot && first.bot == last.bot)
    assert(first.host.eq(firstChild))
    assert(repeated.host.eq(nested))
    assert(last.host.eq(sibling))
    assert(!firstChild.sequentOfFact(first).left.contains(unrelated))
    assert(HOLSteps.HOLProofType.cacheSize == 3)
    val result = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      HOLSteps.HOLProofType(Proofs.f * Proofs.x)
    }
    val typed = result.validate(summon[sourcecode.Line], summon[sourcecode.File])
    assert(!typed.bot.left.contains(unrelated))
    checkTyping(proof)(typed)

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
    val typing = HOLSteps.HOLProofType(f * x)
    assert(typing.statement.left == context)
    // Canonical subterm proofs may remain; the local-context application must not.
    val canonicalEntries = HOLSteps.HOLProofType.cacheSize
    checkTyping(proof)(typing)
    proof.cleanAssumptions
    assertThrows[LisaHOLException](HOLSteps.HOLProofType(f * x))
    assert(HOLSteps.HOLProofType.cacheSize == canonicalEntries)

  test("use the constructor's requirements, not every free type's non-emptiness"):
    import lisa.SetTheoryLibrary.*
    val proof = new BaseProof(Proofs.reflexivity.asInstanceOf[THMFromProof])
    given proof.type = proof
    val typing = HOLSteps.HOLProofType(Proofs.totalConstant(Proofs.A))
    assert(typing.statement.left.isEmpty)
    checkTyping(proof)(typing)

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

  test("keep unnamed steps local while reusing checked named theorems"):
    import lisa.hol.extractor.*
    val start = 10000001L
    val p = "v(local-cache-p)(c[bool][])"
    val equality = s"C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))($p))($p)"
    given ExtractorContext = new ExtractorContext(
      Iterator(
        ProofLine(start, REFL(p)),
        ProofLine(start + 1, TRANS(start, start)),
        ProofLine(start + 2, TRANS(start, start)),
        ProofLine(start + 3, TRANS(start + 1, start + 1))
      ),
      (0 to 3).iterator.map(offset => TheoremStatement(start + offset, RawSequent(Nil, equality)))
    )
    val store = new Import.LocalStepStore
    val first = store.theorem(TheoremRef(start + 1, "LOCAL_CACHE_FIRST"))
    assert(store.size == 2 && store.localCacheSize == 2)
    val second = store.theorem(TheoremRef(start + 2, "LOCAL_CACHE_SECOND"))
    assert(store.size == 4 && store.localCacheSize == 2)
    val third = store.theorem(TheoremRef(start + 3, "LOCAL_CACHE_THIRD"))
    assert(store.size == 5 && store.localCacheSize == 1)
    assert(store.retainedSize == 3)
    List(first, second, third).foreach(result => Proofs.check(result.asInstanceOf[lisa.SetTheoryLibrary.THM]))
    (0 to 3).foreach(offset => assert(lisa.SetTheoryLibrary.theory.getTheorem(s"Import.step${start + offset}").isEmpty))

  test("reject forward and missing dependencies with a theorem-local cache"):
    import lisa.hol.extractor.*
    val p = "v(local-cache-invalid-p)(c[bool][])"
    for target <- List(9L, 11L) do
      val extractor = new ExtractorContext(
        Iterator(ProofLine(10, TRANS(target, target))),
        Iterator(TheoremStatement(10, RawSequent(List(p), p)))
      )
      val store = new Import.LocalStepStore()(using extractor)
      intercept[Exception](store.theorem(TheoremRef(10, s"LOCAL_CACHE_INVALID_$target")))
      assert(store.size == 0 && store.retainedSize == 0)

  test("check intermediate statements in the theorem-local debug variant"):
    import lisa.hol.extractor.*
    val p = "v(local-debug-p)(c[bool][])"
    val q = "v(local-debug-q)(c[bool][])"
    given ExtractorContext = new ExtractorContext(
      Iterator(ProofLine(20, ASSUME(p))),
      Iterator(TheoremStatement(20, RawSequent(List(p), q)))
    )
    val store = new Import.LocalStepStore()(using summon[ExtractorContext], Import.Logging.LoggingMode.Debug)
    intercept[Exception](store.theorem(TheoremRef(20, "LOCAL_CACHE_DEBUG_MISMATCH")))
    assert(store.size == 0 && store.retainedSize == 0)

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
