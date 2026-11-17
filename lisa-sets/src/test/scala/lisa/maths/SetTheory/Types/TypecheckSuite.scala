package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary._
import lisa.maths.SetTheory.Cardinal.Predef.universeOf
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.K
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Check the same typing cases through SC proofs, without LCF test fixtures.
 */
class TypecheckSuite extends AnyFunSuite:
  private given SetTheoryLibrary.type = SetTheoryLibrary
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val A, B, f, x, y = variable[Ind]
  private val family = variable[Ind >>: Ind]
  private val anchor = Theorem(⊤) { have(⊤) by Restate }

  private def check(context: Set[Expr[Prop]], term: Expr[Ind], typ: Expr[Ind], expected: Sequent): Unit =
    val proof = new BaseProof(anchor.asInstanceOf[THMFromProof])
    given proof.type = proof
    val result = Typecheck.checkProof(context, term, typ)
    assert(
      result.isValid,
      result match
        case invalid: proof.InvalidProofTactic => invalid.message
        case _ => "Expected a valid typing derivation"
    )
    val step = have(result)
    assert(step.statement == expected)
    assert(K.SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  private def reject(context: Set[Expr[Prop]], term: Expr[Ind], typ: Expr[Ind]): Unit =
    val proof = new BaseProof(anchor.asInstanceOf[THMFromProof])
    given proof.type = proof
    assert(!Typecheck.checkProof(context, term, typ).isValid)

  test("reuse exact typing without dropping its premise"):
    check(Set(x ∈ A, y ∈ B), x, A, x ∈ A |- x ∈ A)

  test("reuse an exact dependent function type"):
    val typ = Pi(A)(λ(x, family(x)))
    check(Set(f ∈ typ), f, typ, f ∈ typ |- f ∈ typ)

  test("restate beta-equivalent types while retaining the inferred premise"):
    val typ = λ(y, y)(A)
    check(Set(x ∈ A), x, typ, x ∈ A |- x ∈ typ)

  test("restate alpha-equivalent dependent types"):
    val inferred = Pi(A)(λ(x, family(x)))
    val expected = Pi(A)(λ(y, family(y)))
    check(Set(f ∈ inferred), f, expected, f ∈ inferred |- f ∈ expected)

  test("retain a genuine inclusion premise"):
    val context = Set(x ∈ A, A ⊆ B)
    check(context, x, B, context |- x ∈ B)

  test("retain universe lifting"):
    check(Set(x ∈ A), x, universeOf(A), x ∈ A |- x ∈ universeOf(A))

  test("construct covariance only for different function types"):
    check(Set(f ∈ (A ->: B)), f, A ->: universeOf(B), f ∈ (A ->: B) |- f ∈ (A ->: universeOf(B)))

  test("type an application with explicit cuts"):
    val context = Set(f ∈ (A ->: B), x ∈ A)
    check(context, f * x, B, context |- (f * x) ∈ B)

  test("infer a lambda without retaining its bound variable assumption"):
    val context = Set(f ∈ (A ->: B))
    check(context, abs(A)(λ(x, f * x)), A ->: B, context |- abs(A)(λ(x, f * x)) ∈ (A ->: B))

  test("reject unrelated types and missing typing premises"):
    reject(Set(x ∈ A), x, B)
    reject(Set(y ∈ A), x, A)
    reject(Set(x ∈ A), x, universeOf(B))

  test("reject invalid applications and abstraction domains"):
    reject(Set(f ∈ (A ->: B), x ∈ B), f * x, B)
    reject(Set(f ∈ A, x ∈ A), f * x, B)
    reject(Set(f ∈ (A ->: B)), abs(A)(λ(x, f * x)), B ->: B)

  test("reuse repeated subterms without leaking subproof-local references"):
    val combine = variable[Ind]
    val context = Set(combine ∈ (B ->: B ->: B), f ∈ (A ->: B), x ∈ A)
    val term = combine * (f * x) * (f * x)
    check(context, term, B, context |- term ∈ B)

  test("align distinct dependent covariance binders"):
    val from = Pi(A)(λ(x, family(x)))
    val to = Pi(A)(λ(y, universeOf(family(y))))
    check(Set(f ∈ from), f, to, f ∈ from |- f ∈ to)

  test("discharge universe formation with explicit conjuncts and cuts"):
    val proof = new BaseProof(anchor.asInstanceOf[THMFromProof])
    given proof.type = proof
    val goal = () |- (A ->: A) ∈ universeOf(A)
    val result = Typecheck.prove(goal)
    assert(result.isValid)
    val step = have(result)
    assert(step.statement == goal)
    assert(K.SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("freshen nested binders that shadow a different type assignment"):
    val term = abs(A)(λ(x, abs(B)(λ(x, x))))
    check(Set.empty, term, A ->: B ->: B, () |- term ∈ (A ->: B ->: B))

  test("keep free variables in the outer typing context distinct from binders"):
    val term = abs(A)(λ(x, y))
    val context = Set(y ∈ family(x))
    check(context, term, A ->: family(x), context |- term ∈ (A ->: family(x)))

  test("keep function-arrow codomains independent of their hidden binder"):
    assert((A ->: family(x)).freeVars.contains(x))

  test("freshen a binder that shadows a free variable in its domain"):
    val term = abs(x)(λ(x, x))
    check(Set.empty, term, x ->: x, () |- term ∈ (x ->: x))

  test("count only leading universeOf applications in universe depth"):
    val bases = List(A, family(A), family(universeOf(A)), f * x, Pi(A)(λ(x, family(x))), abs(A)(λ(x, x)))
    bases.foreach { base =>
      assert(Typecheck.getDepth(base) == 1, s"Unexpected universe depth for $base")
      assert(Typecheck.getDepth(universeOf(base)) == 2)
      assert(Typecheck.getDepth(universeOf(universeOf(base))) == 3)
    }

  test("use an inclusion from a compound type without a spurious depth mismatch"):
    val context = Set(x ∈ family(A), family(A) ⊆ B)
    check(context, x, B, context |- x ∈ B)

  test("prefer an exact context typing over a convertible alternative"):
    List(x ∈ A, x ∈ B, A ⊆ B).permutations.foreach { assumptions =>
      check(assumptions.toSet, x, B, x ∈ B |- x ∈ B)
    }

  test("use assumed typings of structured terms before reconstructing them"):
    List(f * x, abs(A)(λ(x, x)), Pi(A)(λ(x, family(x)))).foreach { term =>
      val assumption = term ∈ B
      check(Set(assumption), term, B, assumption |- assumption)
    }
    val theorem = Theorem((f * x) ∈ B |- (f * x) ∈ B) {
      have(thesis) by Typecheck.prove
    }
    assert(!theorem.withSorry)

  test("retain the original equivalent member assumption through lookup and subsumption"):
    val assumedTerm = abs(A)(λ(x, x))
    val term = abs(A)(λ(y, y))
    val assumption = assumedTerm ∈ family(A)
    check(Set(assumption), term, family(A), assumption |- term ∈ family(A))
    val context = Set(assumption, family(A) ⊆ B)
    check(context, term, B, context |- term ∈ B)

  test("try every context typing for subsumption without retaining failed candidates"):
    val C = variable[Ind]
    val types = List(A, B, universeOf(A))
    val typings = types.map(x ∈ _).toSet
    types.foreach { actual =>
      val inclusion = actual ⊆ C
      val required = Set(x ∈ actual, inclusion)
      check(typings + inclusion, x, C, required |- x ∈ C)
    }
    reject(typings, x, C)

  test("fall back to structural typing after context candidates fail"):
    val term = f * x
    val required = Set(f ∈ (A ->: B), x ∈ A)
    check(required + (term ∈ family(A)), term, B, required |- term ∈ B)

  test("use assumed inclusions before universe depth checks or function decomposition"):
    val deep = universeOf(A)
    val universeContext = Set(x ∈ deep, deep ⊆ B)
    check(universeContext, x, B, universeContext |- x ∈ B)
    reject(Set(x ∈ deep), x, B)

    val from = Pi(A)(λ(y, family(y)))
    val to = Pi(B)(λ(y, family(y)))
    val inclusion = Pi(A)(λ(x, family(x))) ⊆ Pi(B)(λ(x, family(x)))
    val functionContext = Set(f ∈ from, inclusion)
    check(functionContext, f, to, functionContext |- f ∈ to)
    reject(Set(f ∈ from), f, to)

  test("keep ambient assumptions out of explicit context lookup"):
    val proof = new BaseProof(anchor.asInstanceOf[THMFromProof])
    given proof.type = proof
    proof.addAssumption(x ∈ B)
    proof.addAssumption(A ⊆ B)
    assert(!Typecheck.checkProof(Set(x ∈ A), x, B).isValid)
