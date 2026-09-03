package lisa.automation.superposition

import lisa.automation.Problem
import lisa.automation.clausification.CertifiedClausifier
import lisa.automation.superposition.bench.EqFofEvaluation
import lisa.automation.superposition.bench.FofEvaluation
import lisa.kernel.KernelProof
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

/**
 * Tests for [[Clausal]], the superposition prover's side of the clausification boundary:
 *
 *   - **ε-abstraction**: the kernel's ε-terms are not first-order, so ingestion replaces each by a schematic
 *     function of its free variables, sharing one symbol per distinct term and leaving first-order atoms
 *     alone; reconstruction substitutes the discharge map back.
 *   - **clause-slot composition**: every clause the refutation uses maps to its own import slot, including
 *     when two hypotheses clausify to the *same* sequent.
 *   - **the prover contract**: `Clausal.prove`, folded into the `Problem => SCProof` that `certifyClausal`
 *     requires, produces a proof that satisfies it.
 *   - the harnesses' seeded sampling, which must be reproducible for any benchmark number to mean anything.
 *
 * Tests of the clausifier itself moved to `lisa.automation.clausification.CertifiedClausificationTest`
 * (code review, §6.3). They were the majority of this file and were invisible to a clausification-scoped
 * test run.
 */
class ClausalTest extends AnyFunSuite:

  /**
   * The clausal prover as `certifyClausal` wants it; see [[Clausal.prove]], which reports a non-refutation.
   */
  private def prover(p: Problem): K.SCProof =
    Clausal.prove(p).fold(o => fail(s"the clausal prover did not refute: $o"), identity)

  private def vr(n: String): K.Variable = K.Variable(K.Identifier(n), K.Ind)
  private def pred(n: String, arity: Int): K.Constant = K.Constant(K.Identifier(n), sortOf(arity, K.Prop))
  private def fn(n: String, arity: Int): K.Constant = K.Constant(K.Identifier(n), sortOf(arity, K.Ind))
  private def sortOf(arity: Int, base: K.Sort): K.Sort = (0 until arity).foldRight(base)((_, acc) => K.Ind -> acc)
  private def ap(f: K.Expression, args: K.Expression*): K.Expression = args.foldLeft(f)((acc, a) => K.Application(acc, a))
  private def eps(x: K.Variable, phi: K.Expression): K.Expression = K.Application(K.epsilon, K.Lambda(x, phi))

  private def containsLambda(e: K.Expression): Boolean = e match
    case K.Lambda(_, _) => true
    case K.Application(f, a) => containsLambda(f) || containsLambda(a)
    case _ => false

  private def containsForall(e: K.Expression): Boolean = e match
    case K.Application(K.forall, _) => true
    case K.Application(f, a) => containsForall(f) || containsForall(a)
    case K.Lambda(_, b) => containsForall(b)
    case _ => false

  private def containsBotTop(e: K.Expression): Boolean =
    if e == K.bot || e == K.top then true
    else
      e match
        case K.Application(f, a) => containsBotTop(f) || containsBotTop(a)
        case K.Lambda(_, b) => containsBotTop(b)
        case _ => false

  test("abstraction replaces an epsilon term by a schematic function of its free variables") {
    val P = pred("P", 1); val Q = pred("Q", 2); val x = vr("x"); val y = vr("y")
    val e = eps(x, ap(Q, x, y)) //          ε(λx. Q(x, y)), free variable y
    val atom = ap(P, e) //                  P(ε(λx. Q(x, y)))
    val abs = new Clausal.Abstraction
    val out = abs(atom)
    assert(!containsLambda(out)) //          the abstracted atom is first-order
    assert(out != atom)
    assert(abs.dischargeSubst.size == 1) //  one schematic symbol introduced
    val (f, value) = abs.dischargeSubst.head
    assert(value == K.Lambda(y, e)) //       F := λy. ε(λx. Q(x, y))
    assert(out == ap(P, ap(f, y))) //        P(F(y))
  }

  test("abstraction round-trips: substituting the discharge map back recovers the original (mod beta)") {
    val P = pred("P", 2); val Q = pred("Q", 2); val f = fn("f", 1)
    val x = vr("x"); val y = vr("y"); val z = vr("z")
    // P(f(ε(λx.Q(x,y))), z): the ε-term is nested under the first-order f and the predicate P
    val e = eps(x, ap(Q, x, y))
    val atom = ap(P, ap(f, e), z)
    val abs = new Clausal.Abstraction
    val out = abs(atom)
    assert(!containsLambda(out))
    assert(out == ap(P, ap(f, ap(abs.dischargeSubst.head._1, y)), z)) // P(f(F(y)), z)
    // discharge: substitute F := λy.e, beta-normalize, recover the original atom
    val back = K.substituteVariables(out, abs.dischargeSubst).betaNormalForm
    assert(back == atom)
  }

  test("identical non-first-order subterms share one schematic symbol") {
    val P = pred("P", 2); val Q = pred("Q", 1); val x = vr("x")
    val e = eps(x, ap(Q, x)) // ground ε-term, no free variables
    val atom = ap(P, e, e) //   P(ε, ε) -- the same ε-term twice
    val abs = new Clausal.Abstraction
    val out = abs(atom)
    assert(abs.dischargeSubst.size == 1) //   one symbol, shared
    val f = abs.dischargeSubst.head._1
    assert(out == ap(P, f, f)) //             a nullary schematic constant-function, used twice
  }

  test("a purely first-order atom is left unchanged") {
    val P = pred("P", 1); val f = fn("f", 1); val a = fn("a", 0); val x = vr("x")
    val atom = ap(P, ap(f, x)) // P(f(x)) -- already first-order
    val abs = new Clausal.Abstraction
    assert(abs(atom) == atom)
    assert(abs.isEmpty)
    assert(abs(ap(P, a)) == ap(P, a)) // P(a) with a constant
  }

  // --- spike: abstracted ε-clauses through the prover, reconstructed to a kernel-valid proof ---

  /**
   * Refute the two complementary clauses `() ⊢ {atom}` and `{atom} ⊢` (after abstraction) and return the
   *  reconstructed proof, asserting it is kernel-valid and concludes the empty sequent.
   */
  private def refuteComplementary(abs: Clausal.Abstraction, atom: K.Expression): K.SCProof =
    val a = abs(atom)
    val out = Clausal.refute(Seq(K.Sequent(Set.empty, Set(a)), K.Sequent(Set(a), Set.empty)), symbolVars = abs.dischargeSubst.keySet)
    assert(out.isInstanceOf[Clausal.Outcome.Success], s"expected a refutation, got $out")
    val proof = out.asInstanceOf[Clausal.Outcome.Success].reconstructKernelProof
    KernelProof.assertCorrectProofNoSorry(proof, "Clausal.prove")
    assert(proof.conclusion == K.Sequent(Set.empty, Set.empty))
    proof

  test("spike: a ground ε-term (nullary schematic symbol) ingests and reconstructs kernel-valid") {
    val P = pred("P", 1); val Q = pred("Q", 1); val x = vr("x")
    val atom = ap(P, eps(x, ap(Q, x))) // P(ε(λx.Q(x)))
    refuteComplementary(new Clausal.Abstraction, atom)
  }

  test("spike: an ε-term with a free variable (applied schematic symbol) ingests and reconstructs kernel-valid") {
    val P = pred("P", 1); val Q = pred("Q", 2); val x = vr("x"); val y = vr("y")
    val atom = ap(P, eps(x, ap(Q, x, y))) // P(ε(λx.Q(x,y))) -- F applied to the free variable y
    refuteComplementary(new Clausal.Abstraction, atom)
  }

  // --- the certifyClausal prover adapter (Clausal.prove): ε-free and ε-bearing, end to end ---

  test("FofEvaluation.sample: reproducible seeded 100-problem draw from the FOF dataset") {
    assert(FofEvaluation.allProblems.size == 944) //           the full FOF theorem list (CSR/SUMO excluded)
    val s = FofEvaluation.sample() //                          defaults: n = 100, seed = 42
    assert(s.size == 100)
    assert(s.toSet.size == 100) //                             distinct
    assert(s == FofEvaluation.sample(100, 42)) //              deterministic for a fixed seed
    assert(s != FofEvaluation.sample(100, 7)) //               a different seed gives a different draw
    assert(s.forall(_.startsWith("Problems/"))) //             TPTP-root-relative paths
    assert(FofEvaluation.sample(2000, 42).size == 944) //      n larger than the list returns all of it
  }

  test("EqFofEvaluation.sample: reproducible seeded draw from the equality-bearing FOF dataset") {
    assert(EqFofEvaluation.allProblems.size == 5589) //        FOF_THM_{RFO,EPR}_{SEQ,PEQ}, CSR excluded, .p only
    val s = EqFofEvaluation.sample() //                        defaults: n = 100, seed = 42
    assert(s.size == 100 && s.toSet.size == 100) //            distinct
    assert(s == EqFofEvaluation.sample(100, 42)) //            deterministic for a fixed seed
    assert(s != EqFofEvaluation.sample(100, 7)) //             a different seed gives a different draw
    assert(s.forall(_.startsWith("Problems/"))) //             TPTP-root-relative paths
    assert(EqFofEvaluation.sample(9999, 42).size == 5589) //   n larger than the list returns all of it
    assert(EqFofEvaluation.allProblems.forall(p => !p.startsWith("Problems/CSR/") && p.endsWith(".p"))) // CSR excluded, .p only
  }

  test("import composition maps each used clause to its own slot, even with duplicate clauses") {
    // `proveOutcome` bridges each import the reconstruction used back to the clausifier's clause at that slot.
    // Duplicated input clauses are *equal* sequents, so the mapping must still be well-defined, and it resolves to
    // the first matching slot (`Restate` only needs some import proving that sequent). This pins the tie-break
    // the slot lookup has to preserve, and that the composed proof still declares every clause as an import.
    val p = pred("p", 1); val q = pred("q", 1); val a = fn("a", 0)
    val clause = K.Sequent(Set.empty, Set(ap(p, a)))
    val problem = Problem(Seq(clause, clause, K.Sequent(Set.empty, Set(ap(q, a))), K.Sequent(Set.empty, Set(K.neg(ap(p, a))))), None)
    val proof = Clausal.prove(problem).fold(o => fail(s"expected a refutation, got $o"), identity)
    KernelProof.assertCorrectProofNoSorry(proof, "Clausal.prove")
    assert(proof.conclusion == K.Sequent(Set.empty, Set.empty), "the prover must conclude the empty sequent")
    assert(proof.imports == problem.imports, "the composed proof must declare the clausifier's clauses verbatim")
  }

  test("probe: Clausal.prove satisfies the certifyClausal prover contract (kernel-valid final proof)") {
    val P = pred("P", 0)
    // hypothesis P, conjecture P -- clausifies (already-clausal) to {P, ¬P}; refutation uses both. `⊢ P`.
    val problem = Problem(Seq(K.Sequent(Set.empty, Set(P))), Some(K.Sequent(Set.empty, Set(P))))
    val proof = CertifiedClausifier.certifyClausal(problem, prover)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal with Clausal.prove")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(P)))
  }
