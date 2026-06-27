package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K

/** Tests for the Phase-3 clausification wiring. */
class ClausalTest extends AnyFunSuite:

  private def vr(n: String): K.Variable = K.Variable(K.Identifier(n), K.Ind)
  private def pred(n: String, arity: Int): K.Constant = K.Constant(K.Identifier(n), sortOf(arity, K.Prop))
  private def fn(n: String, arity: Int): K.Constant = K.Constant(K.Identifier(n), sortOf(arity, K.Ind))
  private def sortOf(arity: Int, base: K.Sort): K.Sort = (0 until arity).foldRight(base)((_, acc) => K.Ind -> acc)
  private def ap(f: K.Expression, args: K.Expression*): K.Expression = args.foldLeft(f)((acc, a) => K.Application(acc, a))
  private def eps(x: K.Variable, phi: K.Expression): K.Expression = K.Application(K.epsilon, K.Lambda(x, phi))

  private def containsLambda(e: K.Expression): Boolean = e match
    case K.Lambda(_, _)      => true
    case K.Application(f, a) => containsLambda(f) || containsLambda(a)
    case _                   => false

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

  /** Refute the two complementary clauses `() ⊢ {atom}` and `{atom} ⊢` (after abstraction) and return the
   *  reconstructed proof, asserting it is kernel-valid and concludes the empty sequent. */
  private def refuteComplementary(abs: Clausal.Abstraction, atom: K.Expression): K.SCProof =
    val a = abs(atom)
    val out = Bridge.solve(Seq(K.Sequent(Set.empty, Set(a)), K.Sequent(Set(a), Set.empty)), functionVars = abs.dischargeSubst.keySet)
    assert(out.isInstanceOf[Bridge.Outcome.Success], s"expected a refutation, got $out")
    val proof = out.asInstanceOf[Bridge.Outcome.Success].reconstructKernelProof
    assert(K.SCProofChecker.checkSCProof(proof).isValid, s"proof rejected by the kernel: ${K.SCProofChecker.checkSCProof(proof)}")
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
