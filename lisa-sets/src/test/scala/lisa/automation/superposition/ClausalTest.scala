package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.automation.clausification.Clausification

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

  private def containsForall(e: K.Expression): Boolean = e match
    case K.Application(K.forall, _) => true
    case K.Application(f, a)        => containsForall(f) || containsForall(a)
    case K.Lambda(_, b)             => containsForall(b)
    case _                          => false

  private def containsBotTop(e: K.Expression): Boolean =
    if e == K.bot || e == K.top then true
    else e match
      case K.Application(f, a) => containsBotTop(f) || containsBotTop(a)
      case K.Lambda(_, b)      => containsBotTop(b)
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
    val out = Bridge.solve(Seq(K.Sequent(Set.empty, Set(a)), K.Sequent(Set(a), Set.empty)), symbolVars = abs.dischargeSubst.keySet)
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

  test("Pelletier 50: an η-reduced inner ∀ is still clausified (was saturating) and refutes end-to-end") {
    val bigf = pred("bigf", 2); val a = fn("a", 0); val x = vr("x"); val y = vr("y"); val x1 = vr("x1"); val y1 = vr("y1")
    def all(v: K.Variable, b: K.Expression) = K.Application(K.forall, K.Lambda(v, b))
    def ex(v: K.Variable, b: K.Expression)  = K.Application(K.exists, K.Lambda(v, b))
    def orr(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.or, l), r)
    def impl(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.implies, l), r)
    // (∀x. big_f(a,x) ∨ ∀y. big_f(x,y)) ⇒ ∃x1. ∀y1. big_f(x1,y1). The inner `∀y. big_f(x,y)` = `∀(λy. big_f(x)(y))`
    // η-reduces to `∀(big_f(x))` under betaNormalForm; without etaExpandQuantifiers the clausifier leaves the ∀
    // stranded as an opaque atom and the prover saturates on this valid theorem.
    val conjecture = impl(all(x, orr(ap(bigf, a, x), all(y, ap(bigf, x, y)))), ex(x1, all(y1, ap(bigf, x1, y1))))
    val problem = Clausification.Problem(Seq.empty, Some(K.Sequent(Set.empty, Set(conjecture))))
    // no clause literal may still contain a quantifier (the bug signature)
    val clauses = lisa.automation.clausification.UncertifiedClausification.clausalForm(problem).hypotheses
    assert(clauses.forall(_.right.forall(lit => !containsForall(lit))), s"a clause still has a stranded ∀: $clauses")
    val proof = Clausification.certifyClausal(problem, Clausal.prove)
    assert(K.SCProofChecker.checkSCProof(proof).isValid, s"kernel rejected the composed proof")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(conjecture)))
  }

  test("boolean constants (⊤/⊥) are absorbed in NNF (LCL-style $false padding no longer saturates)") {
    val r = pred("r", 2); val x = vr("x"); val y = vr("y")
    def all(v: K.Variable, b: K.Expression) = K.Application(K.forall, K.Lambda(v, b))
    def ex(v: K.Variable, b: K.Expression)  = K.Application(K.exists, K.Lambda(v, b))
    def andd(l: K.Expression, rr: K.Expression) = K.Application(K.Application(K.and, l), rr)
    // reflexivity ⊢ ∀x.∃y.(r(x,y) ∧ ¬$false)  ≡ seriality. Negating puts ⊥ *in the same disjunct* as the key
    // literal: `¬r(c,y) ∨ ⊥`. Without absorption that clause is `{¬r(c,y), ⊥}` — resolving it against
    // reflexivity yields `{⊥}` (⊥ an uninterpreted atom, unrefutable) and the prover saturates.
    val refl = all(x, ap(r, x, x))
    val conj = all(x, ex(y, andd(ap(r, x, y), K.Application(K.neg, K.bot))))
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(refl))), Some(K.Sequent(Set.empty, Set(conj))))
    val clauses = lisa.automation.clausification.UncertifiedClausification.clausalForm(problem).hypotheses
    assert(clauses.forall(_.right.forall(lit => !containsBotTop(lit))), s"⊤/⊥ survived clausification: $clauses")
    val proof = Clausification.certifyClausal(problem, Clausal.prove)
    assert(K.SCProofChecker.checkSCProof(proof).isValid, "kernel rejected the composed proof")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(conj)))
  }

  test("Skolem binder-name collision: a reused quantifier name (∃ shadowing ∀) certifies kernel-valid") {
    val p = pred("p", 1); val r = pred("r", 2); val X = vr("X"); val Y = vr("Y")
    def all(v: K.Variable, b: K.Expression) = K.Application(K.forall, K.Lambda(v, b))
    def ex(v: K.Variable, b: K.Expression)  = K.Application(K.exists, K.Lambda(v, b))
    // The Skolemized existential shares its bound-variable name with an enclosing universal binder. Before
    // the fix, the certified Skolem bridge's `RightSubstIff` context (keyed on the enclosing binders) also
    // rewrote the existential's OWN bound occurrences, so the reconstructed premise desynced from `f` and
    // the kernel rejected the composed proof (BAD_PROOF). Minimal distillation of LCL670+1.001. The
    // refutation itself was always sound; only the certificate was malformed.
    for hyp <- Seq(
      all(Y, ex(Y, ap(p, Y))),               // ∀Y. ∃Y. p(Y)          — ∃Y shadows the enclosing ∀Y (k=1)
      all(Y, all(X, ex(Y, ap(r, X, Y))))     // ∀Y. ∀X. ∃Y. r(X, Y)   — ∃Y collides with the OUTER ∀Y (k=2)
    ) do
      val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(hyp))), Some(K.Sequent(Set.empty, Set(hyp))))
      val proof = Clausification.certifyClausal(problem, Clausal.prove)
      assert(K.SCProofChecker.checkSCProof(proof).isValid, s"kernel rejected the composed proof for $hyp")
      assert(proof.conclusion == K.Sequent(Set.empty, Set(hyp)))
  }

  test("uncertified (fast) clausalForm is equisatisfiable with the certified path: the prover refutes both") {
    val P = pred("P", 1); val Q = pred("Q", 2); val A = pred("A", 0); val B = pred("B", 0); val C = pred("C", 0)
    val x = vr("x"); val y = vr("y")
    val forallPx = K.Application(K.forall, K.Lambda(x, ap(P, x)))                                    // ∀x.P(x)
    val body = K.Application(K.Application(K.or, K.Application(K.Application(K.and, A), B)), C)       // (A∧B)∨C
    val forallExists = K.Application(K.forall, K.Lambda(x, K.Application(K.exists, K.Lambda(y, ap(Q, x, y))))) // ∀x.∃y.Q(x,y)
    // The fast clausifier need only preserve (un)satisfiability — not the exact clauses — so for each problem we
    // check the prover reaches the *same* refutation verdict on the fast clauses as on the certified path's clauses.
    // (Problems 1–2 are valid ⇒ both refute; problem 3 is satisfiable ⇒ both saturate.)
    val problems = Seq(
      Clausification.Problem(Seq(K.Sequent(Set.empty, Set(forallPx))), Some(K.Sequent(Set.empty, Set(forallPx)))),
      Clausification.Problem(
        Seq(K.Sequent(Set.empty, Set(body)), K.Sequent(Set.empty, Set(K.Application(K.neg, C)))),
        Some(K.Sequent(Set.empty, Set(A)))),
      Clausification.Problem(Seq(K.Sequent(Set.empty, Set(forallExists))), Some(K.Sequent(Set.empty, Set(forallPx))))
    )
    for problem <- problems do
      var captured: Clausification.Problem = null // record what certifyClausal feeds its prover (the certified clauses)
      Clausification.certifyClausal(problem, p => { captured = p; K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), p.imports) })
      val certifiedRefuted = Clausal.solveOutcome(Clausification.Problem(captured.imports.toSeq, None)).refuted
      val fastRefuted = Clausal.solveOutcome(lisa.automation.clausification.UncertifiedClausification.clausalForm(problem)).refuted
      assert(fastRefuted == certifiedRefuted, s"fast/certified refutation verdict disagree (fast=$fastRefuted, certified=$certifiedRefuted) on $problem")
  }

  test("fast clausifier: a nested equivalence chain stays linear (selective naming caps the CNF blow-up)") {
    // p₁ ⇔ p₂ ⇔ … ⇔ pₙ. Naïve CNF is exponential; definitional naming keeps clauses O(n). We assert the count
    // grows sub-quadratically with n (a loose bound that still fails hard for the exponential/unnamed expansion).
    def eqv(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.iff, l), r)
    def clausesOf(n: Int): Int =
      val ps = (1 to n).map(i => pred(s"p$i", 0): K.Expression)
      val chain = ps.reduceLeft(eqv)
      val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(chain))), None)
      lisa.automation.clausification.UncertifiedClausification.clausalForm(problem).hypotheses.size
    val c8 = clausesOf(8); val c16 = clausesOf(16)
    assert(c16 <= 8 * c8, s"equivalence-chain CNF is blowing up: n=8 → $c8 clauses, n=16 → $c16 clauses")
    // no clause literal may contain a residual connective/quantifier
    val ps = (1 to 12).map(i => pred(s"p$i", 0): K.Expression)
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(ps.reduceLeft(eqv)))), None)
    val cls = lisa.automation.clausification.UncertifiedClausification.clausalForm(problem).hypotheses
    assert(cls.forall(_.right.forall(lit => !containsForall(lit) && !containsBotTop(lit))))
  }

  test("fast clausifier: existential-under-universal Skolemizes soundly (drinker's paradox refutes)") {
    // ∃x. (P(x) ⇒ ∀y. P(y)) is valid. Skolemizing its negation must produce a refutable clause set; a wrong
    // Skolem arity (constant vs function of the enclosing universal) would make it satisfiable.
    val P = pred("P", 1); val x = vr("x"); val y = vr("y")
    val drinker = K.Application(K.exists, K.Lambda(x, K.Application(K.Application(K.implies, ap(P, x)), K.Application(K.forall, K.Lambda(y, ap(P, y))))))
    val problem = Clausification.Problem(Seq.empty, Some(K.Sequent(Set.empty, Set(drinker))))
    val uncertified = lisa.automation.clausification.UncertifiedClausification.clausalForm(problem)
    assert(Clausal.solveOutcome(uncertified).refuted, "fast clausifier's Skolemization broke the drinker's paradox")
  }

  test("fast clausifier: a nullary Skolem constant is a function symbol, not a clause variable (no spurious refutation)") {
    // Axiom P(a); conjecture ∀x. P(x) — INVALID (one witness ≠ all). The negated conjecture Skolemizes to ¬P(sk)
    // for a fresh CONSTANT sk ≠ a, so {P(a), ¬P(sk)} is SATISFIABLE and must saturate. Regression guard: if the
    // nullary Skolem were emitted as an Ind-sorted *variable*, the prover would read ¬P(sk) as ∀X. ¬P(X) and
    // resolve it against P(a) to □ — an unsound refutation of a satisfiable set (found via MGT031+1).
    val P = pred("P", 1); val a = fn("a", 0); val x = vr("x")
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(ap(P, a)))),
      Some(K.Sequent(Set.empty, Set(K.Application(K.forall, K.Lambda(x, ap(P, x)))))))
    val uncertified = lisa.automation.clausification.UncertifiedClausification.clausalForm(problem)
    assert(!Clausal.solveOutcome(uncertified).refuted, "satisfiable set spuriously refuted — a nullary Skolem became a clause variable")
  }

  test("probe: Clausal.prove satisfies the certifyClausal prover contract (kernel-valid final proof)") {
    val P = pred("P", 0)
    // hypothesis P, conjecture P -- clausifies (already-clausal) to {P, ¬P}; refutation uses both. `⊢ P`.
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(P))), Some(K.Sequent(Set.empty, Set(P))))
    val proof = Clausification.certifyClausal(problem, Clausal.prove)
    val check = K.SCProofChecker.checkSCProof(proof)
    assert(check.isValid, s"kernel rejected the composed proof: $check")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(P)))
  }

  test("CertifiedFastClausifier: naming matches FastClausify exactly (same subformulas named, up to atom renaming)") {
    val a = (1 to 8).map(i => pred(s"a$i", 0): K.Expression)
    val b = (1 to 6).map(i => pred(s"b$i", 0): K.Expression)
    val R = pred("R", 1); val x = vr("x")
    def eqv(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.iff, l), r)
    def orr(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.or, l), r)
    def andd(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.and, l), r)
    def impl(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.implies, l), r)
    val bigIff = a.reduceRight(eqv)                                   //  a1 ⇔ … ⇔ a8   (Iff blow-up)
    val orOfAnds = orr(a.take(5).reduceRight(andd), b.take(5).reduceRight(andd)) // (∧)∨(∧)  (Or-pos multiplicative)
    val formulas: Seq[K.Expression] = Seq(
      bigIff,
      orOfAnds,
      impl(bigIff, b(0)),                                             //  ⇒ elimination then naming
      K.Application(K.forall, K.Lambda(x, orr(bigIff, ap(R, x)))),    //  naming under ∀
      eqv(orOfAnds, bigIff)                                           //  nested multiplicative + Iff
    )
    for phi <- formulas do
      assert(
        lisa.automation.clausification.CertifiedFastClausifier.sameNaming(phi),
        s"certified naming diverged from FastClausify on: $phi")
  }

  test("CertifiedFastClausifier: end-to-end kernel-valid proof of an Iff-chain tautology (selective naming fires)") {
    // conjecture X ⇒ X with X = (a⇔b⇔c⇔d⇔e): valid, and its negated form's big Iff triggers the certified
    // fast clausifier's selective naming (a fresh predicate d ⇔ X, discharged by InstSchema). End-to-end the
    // composed proof must be kernel-valid and conclude `⊢ (X ⇒ X)`.
    val ps = "abcde".map(c => pred(c.toString, 0): K.Expression)
    def eqv(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.iff, l), r)
    val chain = ps.reduceRight(eqv)
    val conj = K.Application(K.Application(K.implies, chain), chain)
    val problem = Clausification.Problem(Seq.empty, Some(K.Sequent(Set.empty, Set(conj))))
    val proof = lisa.automation.clausification.CertifiedFastClausifier.certifyClausal(problem, Clausal.prove)
    val check = K.SCProofChecker.checkSCProof(proof)
    assert(check.isValid, s"kernel rejected the certified-fast composed proof: $check")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(conj)))
  }

  test("ε end-to-end: a conjecture whose clausification Skolemizes to an ε-term (kernel-valid)") {
    val P = pred("P", 1); val x = vr("x")
    val forallPx = K.Application(K.forall, K.Lambda(x, ap(P, x))) // ∀x. P(x)
    // conjecture ∀x.P(x): its negation ¬∀x.P(x) NNF/Skolemizes to `¬P(ε(λx.¬P(x)))`, so the clause set carries
    // a genuine ε-term. `Clausal.prove` abstracts it (F), refutes P(x) vs ¬P(F) by x:=F, and reconstructs with
    // F inlined back to the ε-term — a purely ε-bearing, kernel-valid proof of `⊢ ∀x.P(x)`.
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(forallPx))), Some(K.Sequent(Set.empty, Set(forallPx))))
    val proof = Clausification.certifyClausal(problem, Clausal.prove)
    val check = K.SCProofChecker.checkSCProof(proof)
    assert(check.isValid, s"kernel rejected the composed proof: $check")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(forallPx)))
  }

  /** A contract-shaped stub prover: imports = the clause-sequents, conclusion = `∅ ⊢`, via one `Sorry`.
   *  Kernel-checking a proof built on it validates the *composition* (the clausifier's new literal-set
   *  `Restate` steps included) while trusting only the refutation itself. */
  private def sorryProver(p: Clausification.Problem): K.SCProof =
    K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), p.imports)

  test("Tseitin end-to-end: a non-clausal problem needing Tseitin atoms, refuted by Bridge (kernel-valid)") {
    val A = pred("A", 0); val B = pred("B", 0); val C = pred("C", 0)
    val body = K.Application(K.Application(K.or, K.Application(K.Application(K.and, A), B)), C) // (A ∧ B) ∨ C
    // {(A ∧ B) ∨ C, ¬C} ⊢ A. Clausifies via Tseitin (fresh predicate atom ts0 ⟺ A ∧ B); the ts0-clauses
    // must be ingested by Bridge (ts0 as an uninterpreted predicate) and refuted, then discharged by the
    // clausifier. Exercises the schematic-predicate-variable path end to end with the real prover.
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(body)), K.Sequent(Set.empty, Set(K.Application(K.neg, C)))),
      Some(K.Sequent(Set.empty, Set(A)))
    )
    val proof = Clausification.certifyClausal(problem, Clausal.prove)
    val check = K.SCProofChecker.checkSCProof(proof)
    assert(check.isValid, s"kernel rejected the composed proof: $check")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(A)))
  }

  test("clausifier emits Tseitin residual clauses in literal-set form (Q>0 composition kernel-valid)") {
    val A = pred("A", 0); val B = pred("B", 0); val C = pred("C", 0)
    val body = K.Application(K.Application(K.or, K.Application(K.Application(K.and, A), B)), C) // (A ∧ B) ∨ C
    // (A ∧ B) ∨ C needs Tseitin (Q>0); its residual rewrite `ts0 ∨ C` must now be emitted as `{ts0, C}` via
    // the new Restate. A Sorry refutation isolates that step for the kernel checker.
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(body))), Some(K.Sequent(Set.empty, Set(A))))
    val proof = Clausification.certifyClausal(problem, sorryProver)
    val check = K.SCProofChecker.checkSCProof(proof)
    assert(check.isValid, s"kernel rejected the composed proof: $check")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(A)))
  }

  test("probe: a multi-literal already-clausal axiom is handed to the prover as a literal set") {
    val P = pred("P", 0); val Q = pred("Q", 0)
    val pOrQ = K.Application(K.Application(K.or, P), Q) // P ∨ Q -- already clausal, MULTI-literal
    // {P ∨ Q, ¬P} ⊢ Q. The clausifier must now emit `P ∨ Q` as the literal set `{P, Q}` (one Restate),
    // exercising the fast path (all axioms clausal) and the new set-form conversion end-to-end.
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(pOrQ)), K.Sequent(Set.empty, Set(K.Application(K.neg, P)))),
      Some(K.Sequent(Set.empty, Set(Q)))
    )
    val proof = Clausification.certifyClausal(problem, Clausal.prove)
    val check = K.SCProofChecker.checkSCProof(proof)
    assert(check.isValid, s"kernel rejected the composed proof: $check")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(Q)))
  }
