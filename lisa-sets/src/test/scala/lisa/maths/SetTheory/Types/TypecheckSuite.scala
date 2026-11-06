package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.*
import lisa.maths.SetTheory.Cardinal.Predef.universeOf
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.K
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/** Check the same typing cases through SC proofs, without LCF test fixtures. */
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
    assert(result.isValid, result match
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
