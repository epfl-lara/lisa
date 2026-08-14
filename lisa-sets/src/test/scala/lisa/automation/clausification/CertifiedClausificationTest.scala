package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.automation.superposition.Clausal
import lisa.kernel.KernelProof

/**
 * End-to-end tests of the certified clausification pipeline: each builds a kernel problem, runs
 * [[CertifiedClausifier.certifyClausal]] with [[Clausal.prove]] as the back-end, and asserts the composed
 * proof is accepted by the kernel and concludes the original goal.
 *
 * These lived in the superposition package's `ClausalTest`, where 16 of its 26 tests were about clausification, so
 * `testOnly lisa.automation.clausification.*` reported a fraction of the real coverage (code review, §6.3).
 * What stayed behind is what genuinely belongs to [[Clausal]]: ε-abstraction, clause-slot composition, and the
 * prover-contract probe.
 *
 * The pipeline is exercised through its real entry point rather than phase by phase, so a test names the
 * *input shape* that used to break it (an η-reduced inner `∀`, `⊤`/`⊥` padding, a shadowed Skolem binder, a
 * free-variable conjecture, a name colliding with a generated prefix). The phases themselves are covered by
 * `ScreenPhaseTest`, `PrenexRewriteTest`, `ProofIRTest` and `ClausifierEquivalenceTest`.
 */
class CertifiedClausificationTest extends AnyFunSuite:

  private def vr(n: String): K.Variable = K.Variable(K.Identifier(n), K.Ind)
  private def pred(n: String, arity: Int): K.Constant = K.Constant(K.Identifier(n), sortOf(arity, K.Prop))
  private def fn(n: String, arity: Int): K.Constant = K.Constant(K.Identifier(n), sortOf(arity, K.Ind))
  private def sortOf(arity: Int, base: K.Sort): K.Sort = (0 until arity).foldRight(base)((_, acc) => K.Ind -> acc)
  private def ap(f: K.Expression, args: K.Expression*): K.Expression = args.foldLeft(f)((acc, a) => K.Application(acc, a))

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
    val clauses = lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem).hypotheses
    assert(clauses.forall(_.right.forall(lit => !containsForall(lit))), s"a clause still has a stranded ∀: $clauses")
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(conjecture)))
  }

  test("an η-reduced quantifier in the INPUT refutes end-to-end (the other source of the Pelletier-50 shape)") {
    // Pelletier 50 above exercises the shape our *own* `betaNormalForm` creates, inside `SkolemPhase`. This is the
    // second source: the caller simply hands us `∀(p)`. Nothing normalised the input, so it travelled every phase
    // as an opaque atom (`hasForall` false, never stripped, delivered to the prover as the literal `∀(p)`), and a
    // valid goal saturated with no diagnostic. `ScreenPhase` now η-expands at entry, which is free at the kernel
    // level (`isSame` compares β-normal forms, so the two shapes are indistinguishable to it).
    val p = K.Variable(K.Identifier("p"), sortOf(1, K.Prop)) // a *variable*: TPTP cannot express this, a Lisa goal can
    val a = fn("a", 0)
    val etaAll: K.Expression = K.Application(K.forall, p) // ∀(p), NOT matched by `K.Forall`
    assert(etaAll match { case K.Forall(_, _) => false; case _ => true }, "premise: the shape evades the Forall extractor")
    // ∀x.p(x) ⊢ p(a)
    val goal = K.Sequent(Set.empty, Set(K.Application(p, a)))
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(etaAll))), Some(goal))
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal on η-reduced ∀ input")
    assert(proof.conclusion == goal)
  }

  test("an η-reduced ∃ in the input is Skolemized rather than stranded, and refutes end-to-end") {
    val p = K.Variable(K.Identifier("p"), sortOf(1, K.Prop))
    val a = fn("a", 0)
    val etaEx: K.Expression = K.Application(K.exists, p) // ∃(p)
    // p(a) ⊢ ∃x.p(x): the negated conjecture is what must be quantifier-stripped here, not the hypothesis.
    val goal = K.Sequent(Set.empty, Set(etaEx))
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(K.Application(p, a)))), Some(goal))
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal on η-reduced ∃ input")
    assert(proof.conclusion == goal, "the caller's η-reduced goal must come back verbatim")
  }

  test("the UNCERTIFIED path η-expands at its own entry too, as CASC and every benchmark go through it") {
    // This path has no `DistributePhase` check behind it: before the fix it emitted `⊢ ∀(p)` as a clause literal
    // with no error of any kind, and `Bridge` interned `∀` as an ordinary unary predicate. So of the two paths it
    // was the *silent* one, and the one every published number came from.
    val p = K.Variable(K.Identifier("p"), sortOf(1, K.Prop))
    val a = fn("a", 0)
    val etaAll: K.Expression = K.Application(K.forall, p) // ∀(p)
    // ∀x.p(x) ⊢ p(a)
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(etaAll))), Some(K.Sequent(Set.empty, Set(K.Application(p, a)))))
    val clausal = UncertifiedClausifier.clausalForm(problem)
    assert(clausal.hypotheses.forall(_.right.forall(lit => !containsForall(lit))),
      s"a quantifier survived into an uncertified clause: ${clausal.hypotheses.mkString(" ; ")}")
    // and the clause set is actually refutable. It was not, while the ∀ sat there as an opaque literal
    assert(Clausal.solveOutcome(clausal).refuted, "the uncertified clause set does not refute")
  }

  test("the uncertified η-expansion runs after the orthologic normalisation, not before") {
    // `reducedNNFForm` rebuilds the formula through the kernel's locally-nameless normal form, so an expansion
    // done *before* it could be undone. Ordering is not observable from the result on ordinary input, so this
    // pins the invariant that matters instead: whatever that step emits, no quantifier reaches a clause.
    val p = K.Variable(K.Identifier("p"), sortOf(1, K.Prop))
    val q = pred("q", 1); val a = fn("a", 0); val x = vr("x")
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(K.Application(K.forall, p))),                       // η-reduced ∀(p)
          K.Sequent(Set.empty, Set(K.Application(K.forall, K.Lambda(x, ap(q, x)))))),  // explicit ∀x.q(x)
      Some(K.Sequent(Set.empty, Set(K.Application(p, a)))))
    for ortho <- Seq(false, true) do
      val clausal = UncertifiedClausifier.clausalForm(problem, orthologic = ortho)
      assert(clausal.hypotheses.forall(_.right.forall(lit => !containsForall(lit))),
        s"orthologic=$ortho: a quantifier survived: ${clausal.hypotheses.mkString(" ; ")}")
      assert(Clausal.solveOutcome(clausal).refuted, s"orthologic=$ortho: the clause set does not refute")
  }

  // --- the two paths must agree on the clause set, not only on η-expansion ---------------------------------
  //
  // Both of these were divergences where the certified path was right and the uncertified path was wrong. Neither is
  // reachable from TPTP (conjectures are closed; no TPTP symbol is named `w`/`sk`/`nm`), which is why the corpus
  // runs never showed them, the same blind spot §1.9 records for the intern key.

  /** Whether the uncertified path's clause set for `prob` is refutable. */
  private def uncertifiedRefutes(prob: Clausification.Problem): Boolean =
    Clausal.solveOutcome(UncertifiedClausifier.clausalForm(prob), maxGiven = 5000, maxMillis = 10000).refuted

  test("uncertified path: a conjecture's free individual variable is frozen, not left a clause variable") {
    // Goal `pp(x)` with `x` free means `∀x. pp(x)`, which does NOT follow from `pp(c)`. Negating `pp(x)` as
    // written and leaving `x` a clause variable refutes only `∃x. pp(x)`, which does follow, so the path answered
    // "refuted" for a goal that is not valid. Freezing `x` makes it a symbol to the prover, which is what blocks
    // the resolution against `pp(c)`; the same check on the certified path is two lines below.
    val pp = pred("pp", 1); val c = fn("c", 0); val x = vr("x")
    val prob = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(ap(pp, c)))), Some(K.Sequent(Set.empty, Set(ap(pp, x)))))
    assert(!uncertifiedRefutes(prob), "the uncertified path refuted `pp(c) ⊢ pp(x)`, which is not valid")
    // the certified path's answer, for comparison: it declines too, on the same frozen variable
    val certProof = scala.util.Try(CertifiedClausifier.certifyClausal(prob, Clausal.prove))
    assert(certProof.isFailure, "the certified path refuted a goal that is not valid")
  }

  test("uncertified path: an input variable named `w` does not merge with a generated clause variable") {
    // `∀x. q(x,w)` with `w` free means `∀w.∀x. q(x,w)`, so `q(a,c)` follows. The uncertified path mints stripped-∀
    // variables as `Identifier("w", n)` starting at n=0, which renders as the bare `w`, the same identifier as the input's variable
    // exactly. The two merged, turning the hypothesis into the weaker `∀w. q(w,w)`, and the refutation was lost.
    val q = pred("q", 2); val a = fn("a", 0); val c = fn("c", 0); val x = vr("x"); val w = vr("w")
    val prob = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(K.Application(K.forall, K.Lambda(x, ap(q, x, w)))))),
      Some(K.Sequent(Set.empty, Set(ap(q, a, c)))))
    assert(uncertifiedRefutes(prob), "the uncertified path lost a valid refutation: the input `w` merged with a clause variable")
    KernelProof.assertCorrectProofNoSorry(CertifiedClausifier.certifyClausal(prob, Clausal.prove), "certified")
  }

  test("boolean constants (⊤/⊥) are absorbed in NNF (LCL-style $false padding no longer saturates)") {
    val r = pred("r", 2); val x = vr("x"); val y = vr("y")
    def all(v: K.Variable, b: K.Expression) = K.Application(K.forall, K.Lambda(v, b))
    def ex(v: K.Variable, b: K.Expression)  = K.Application(K.exists, K.Lambda(v, b))
    def andd(l: K.Expression, rr: K.Expression) = K.Application(K.Application(K.and, l), rr)
    // reflexivity ⊢ ∀x.∃y.(r(x,y) ∧ ¬$false)  ≡ seriality. Negating puts ⊥ *in the same disjunct* as the key
    // literal: `¬r(c,y) ∨ ⊥`. Without absorption that clause is `{¬r(c,y), ⊥}`, and resolving it against
    // reflexivity yields `{⊥}` (⊥ an uninterpreted atom, unrefutable) and the prover saturates.
    val refl = all(x, ap(r, x, x))
    val conj = all(x, ex(y, andd(ap(r, x, y), K.Application(K.neg, K.bot))))
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(refl))), Some(K.Sequent(Set.empty, Set(conj))))
    val clauses = lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem).hypotheses
    assert(clauses.forall(_.right.forall(lit => !containsBotTop(lit))), s"⊤/⊥ survived clausification: $clauses")
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(conj)))
  }

  test("distribution: `a ∨ (b ∧ c)` is distributed to CNF (not named) and refutes end-to-end (kernel-valid)") {
    val a = pred("a", 0); val b = pred("b", 0); val c = pred("c", 0)
    def andd(l: K.Expression, rr: K.Expression) = K.Application(K.Application(K.and, l), rr)
    def orr(l: K.Expression, rr: K.Expression)  = K.Application(K.Application(K.or, l), rr)
    // `a ∨ (b ∧ c)` is below the naming threshold, so it is NOT named: it must be *distributed* into the two
    // clauses `a∨b`, `a∨c`. With `¬b`, `¬c` as further hypotheses and conjecture `a` (negated to `¬a`), the
    // refutation `a∨b, ¬a ⊢ b` then `¬b ⊢ ⊥` closes only if distribution actually happened.
    val hyp1 = orr(a, andd(b, c))
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(hyp1)),
          K.Sequent(Set.empty, Set(K.Application(K.neg, b))),
          K.Sequent(Set.empty, Set(K.Application(K.neg, c)))),
      Some(K.Sequent(Set.empty, Set(a)))
    )
    // Sanity: the uncertified clausifier really produces the two distributed binary clauses `a∨b`, `a∨c`.
    val clauses = lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem).hypotheses
    assert(clauses.count(_.right.size == 2) == 2, s"expected `a∨(b∧c)` to distribute into two binary clauses, got: $clauses")
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(a)))
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
      all(Y, ex(Y, ap(p, Y))),               // ∀Y. ∃Y. p(Y)          (∃Y shadows the enclosing ∀Y, k=1)
      all(Y, all(X, ex(Y, ap(r, X, Y))))     // ∀Y. ∀X. ∃Y. r(X, Y)   (∃Y collides with the OUTER ∀Y, k=2)
    ) do
      val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(hyp))), Some(K.Sequent(Set.empty, Set(hyp))))
      val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
      KernelProof.assertCorrectProofNoSorry(proof, s"certifyClausal for $hyp")
      assert(proof.conclusion == K.Sequent(Set.empty, Set(hyp)))
  }

  test("a conjecture's free individual variables are frozen, and the conclusion is the original goal") {
    val p = pred("p", 1); val r = pred("r", 2)
    val X = vr("X"); val Y = vr("Y"); val A = vr("A"); val B = vr("B")
    def all(v: K.Variable, b: K.Expression) = K.Application(K.forall, K.Lambda(v, b))
    // (1) one free var: ∀X.p(X) ⊢ p(Y). Y free ⇒ the goal is ∀Y.p(Y), which follows. Y is frozen rather than
    // ∀-closed, so it reaches the prover as a symbol and the proof concludes the ORIGINAL `⊢ p(Y)` directly.
    val prob1 = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(all(X, ap(p, X))))), Some(K.Sequent(Set.empty, Set(ap(p, Y)))))
    val proof1 = CertifiedClausifier.certifyClausal(prob1, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof1, "(1) certifyClausal")
    assert(proof1.conclusion == K.Sequent(Set.empty, Set(ap(p, Y))), s"(1) conclusion ${proof1.conclusion} is not the original goal p(Y)")
    // (2) two free vars, so neither may be instantiated by the other's clause: ∀A∀B.r(A,B) ⊢ r(X,Y).
    val prob2 = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(all(A, all(B, ap(r, A, B)))))), Some(K.Sequent(Set.empty, Set(ap(r, X, Y)))))
    val proof2 = CertifiedClausifier.certifyClausal(prob2, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof2, "(2) certifyClausal")
    assert(proof2.conclusion == K.Sequent(Set.empty, Set(ap(r, X, Y))), s"(2) conclusion ${proof2.conclusion} is not the original goal r(X,Y)")
  }

  test("open-variable axiom whose variable name collides with a fresh-symbol prefix is renamed to `v_i` (kernel-valid)") {
    val p = pred("p", 1); val q = pred("q", 1); val s = pred("s", 1); val a = fn("a", 0)
    val w0 = vr("w0"); val nm0 = vr("nm0") // deliberately named like the clause variable `w<n>` / naming atom `nm<n>`
    def impl(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.implies, l), r)
    // ∀w0.(p(w0) ⟹ q(w0)),  p(a),  and an irrelevant ∀nm0. s(nm0). Open `w0`/`nm0` collide with introduced-name
    // prefixes; ScreenPhase must canonicalise them to `v_i` so nothing the clausifier introduces later captures them.
    val ax1 = impl(ap(p, w0), ap(q, w0))
    val ax2 = ap(p, a)
    val ax3 = ap(s, nm0)
    val conj = ap(q, a)
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(ax1)), K.Sequent(Set.empty, Set(ax2)), K.Sequent(Set.empty, Set(ax3))),
      Some(K.Sequent(Set.empty, Set(conj)))
    )
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(conj)))
  }

  test("uncertified (uncertified) clausalForm is equisatisfiable with the certified path: the prover refutes both") {
    val P = pred("P", 1); val Q = pred("Q", 2); val A = pred("A", 0); val B = pred("B", 0); val C = pred("C", 0)
    val x = vr("x"); val y = vr("y")
    val forallPx = K.Application(K.forall, K.Lambda(x, ap(P, x)))                                    // ∀x.P(x)
    val body = K.Application(K.Application(K.or, K.Application(K.Application(K.and, A), B)), C)       // (A∧B)∨C
    val forallExists = K.Application(K.forall, K.Lambda(x, K.Application(K.exists, K.Lambda(y, ap(Q, x, y))))) // ∀x.∃y.Q(x,y)
    // The uncertified clausifier need only preserve (un)satisfiability rather than the exact clauses, so for each problem we
    // check the prover reaches the *same* refutation verdict on the uncertified clauses as on the certified path's clauses.
    // (Problems 1 and 2 are valid ⇒ both refute; problem 3 is satisfiable ⇒ both saturate.)
    val problems = Seq(
      Clausification.Problem(Seq(K.Sequent(Set.empty, Set(forallPx))), Some(K.Sequent(Set.empty, Set(forallPx)))),
      Clausification.Problem(
        Seq(K.Sequent(Set.empty, Set(body)), K.Sequent(Set.empty, Set(K.Application(K.neg, C)))),
        Some(K.Sequent(Set.empty, Set(A)))),
      Clausification.Problem(Seq(K.Sequent(Set.empty, Set(forallExists))), Some(K.Sequent(Set.empty, Set(forallPx))))
    )
    for problem <- problems do
      var captured: Clausification.Problem = null // record what certifyClausal feeds its prover (the certified clauses)
      CertifiedClausifier.certifyClausal(problem, p => { captured = p; K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), p.imports) })
      val certifiedRefuted = Clausal.solveOutcome(Clausification.Problem(captured.imports.toSeq, None)).refuted
      val uncertifiedRefuted = Clausal.solveOutcome(lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem)).refuted
      assert(uncertifiedRefuted == certifiedRefuted, s"uncertified/certified refutation verdict disagree (uncertified=$uncertifiedRefuted, certified=$certifiedRefuted) on $problem")
  }

  /** The clause set `certifyClausal` actually hands its prover, with the prover stubbed out. */
  private def certifiedClauses(problem: Clausification.Problem): Int =
    var captured: Clausification.Problem = null
    CertifiedClausifier.certifyClausal(problem, p => { captured = p; sorryProver(p) })
    captured.imports.size

  test("the certified path's definitions are polarity-directional, so naming caps its blow-up too") {
    // Naming's bound is one-directional: the threshold gates the clause count only in the direction the site's
    // polarity uses. A definition emitted as the full `⇔` drags in the *other*, ungated half, so the certified
    // path used to blow up on inputs the uncertified one handled linearly.
    //
    // The shape has to make the unused direction the expensive one. `c = (a₁∨b₁) ∧ … ∧ (a_k∨b_k)` has
    // `pos = k` but `neg = 2^k`. Placing it at positive polarity under `∨` fires the gate on `pos`, so the
    // needed half `nm ⇒ c` costs k clauses, while the unused half `c ⇒ nm` costs 2^k.
    def andd(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.and, l), r)
    def orr(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.or, l), r)
    def problemOf(k: Int): Clausification.Problem =
      val c = (1 to k).map(i => orr(pred(s"a$i", 0), pred(s"b$i", 0)): K.Expression).reduceLeft(andd)
      Clausification.Problem(Seq(K.Sequent(Set.empty, Set(orr(c, pred("z", 0))))), None)
    val c5 = certifiedClauses(problemOf(5))
    val c12 = certifiedClauses(problemOf(12))
    // Linear in k is ~2.4x here; the bidirectional `⇔` contributed 2^k. A loose bound that still fails hard.
    assert(c12 <= 6 * c5, s"the certified clause set is blowing up: k=5 → $c5 clauses, k=12 → $c12")
    info(s"certified clauses: k=5 → $c5, k=12 → $c12")
    // And it must stay in line with the uncertified twin, which has always emitted only the directional half.
    val uncertified = lisa.automation.clausification.UncertifiedClausifier.clausalForm(problemOf(12)).hypotheses.size
    assert(c12 <= 2 * uncertified, s"certified ($c12) is far larger than uncertified ($uncertified) on the same problem")
  }

  test("uncertified clausifier: a nested equivalence chain stays linear (selective naming caps the CNF blow-up)") {
    // p₁ ⇔ p₂ ⇔ … ⇔ pₙ. Naïve CNF is exponential; definitional naming keeps clauses O(n). We assert the count
    // grows sub-quadratically with n (a loose bound that still fails hard for the exponential/unnamed expansion).
    def eqv(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.iff, l), r)
    def clausesOf(n: Int): Int =
      val ps = (1 to n).map(i => pred(s"p$i", 0): K.Expression)
      val chain = ps.reduceLeft(eqv)
      val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(chain))), None)
      lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem).hypotheses.size
    val c8 = clausesOf(8); val c16 = clausesOf(16)
    assert(c16 <= 8 * c8, s"equivalence-chain CNF is blowing up: n=8 → $c8 clauses, n=16 → $c16 clauses")
    // no clause literal may contain a residual connective/quantifier
    val ps = (1 to 12).map(i => pred(s"p$i", 0): K.Expression)
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(ps.reduceLeft(eqv)))), None)
    val cls = lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem).hypotheses
    assert(cls.forall(_.right.forall(lit => !containsForall(lit) && !containsBotTop(lit))))
  }

  test("uncertified clausifier: existential-under-universal Skolemizes soundly (drinker's paradox refutes)") {
    // ∃x. (P(x) ⇒ ∀y. P(y)) is valid. Skolemizing its negation must produce a refutable clause set; a wrong
    // Skolem arity (constant vs function of the enclosing universal) would make it satisfiable.
    val P = pred("P", 1); val x = vr("x"); val y = vr("y")
    val drinker = K.Application(K.exists, K.Lambda(x, K.Application(K.Application(K.implies, ap(P, x)), K.Application(K.forall, K.Lambda(y, ap(P, y))))))
    val problem = Clausification.Problem(Seq.empty, Some(K.Sequent(Set.empty, Set(drinker))))
    val uncertified = lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem)
    assert(Clausal.solveOutcome(uncertified).refuted, "uncertified clausifier's Skolemization broke the drinker's paradox")
  }

  test("uncertified clausifier: a nullary Skolem constant is a function symbol, not a clause variable (no spurious refutation)") {
    // Axiom P(a); conjecture ∀x. P(x), which is INVALID (one witness is not all). The negated conjecture Skolemizes to ¬P(sk)
    // for a fresh CONSTANT sk ≠ a, so {P(a), ¬P(sk)} is SATISFIABLE and must saturate. Regression guard: if the
    // nullary Skolem were emitted as an Ind-sorted *variable*, the prover would read ¬P(sk) as ∀X. ¬P(X) and
    // resolve it against P(a) to □, an unsound refutation of a satisfiable set (found via MGT031+1).
    val P = pred("P", 1); val a = fn("a", 0); val x = vr("x")
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(ap(P, a)))),
      Some(K.Sequent(Set.empty, Set(K.Application(K.forall, K.Lambda(x, ap(P, x)))))))
    val uncertified = lisa.automation.clausification.UncertifiedClausifier.clausalForm(problem)
    assert(!Clausal.solveOutcome(uncertified).refuted, "satisfiable set spuriously refuted: a nullary Skolem became a clause variable")
  }

  test("CertifiedClausifier: naming matches UncertifiedClausifier exactly (same subformulas named, identical atoms)") {
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
        lisa.automation.clausification.CertifiedClausifier.sameNaming(phi),
        s"certified naming diverged from UncertifiedClausifier on: $phi")
  }

  test("CertifiedClausifier: end-to-end kernel-valid proof of an Iff-chain tautology (selective naming fires)") {
    // conjecture X ⇒ X with X = (a⇔b⇔c⇔d⇔e): valid, and its negated form's big Iff triggers the certified
    // uncertified clausifier's selective naming (a fresh predicate d ⇔ X, discharged by InstSchema). End-to-end the
    // composed proof must be kernel-valid and conclude `⊢ (X ⇒ X)`.
    val ps = "abcde".map(c => pred(c.toString, 0): K.Expression)
    def eqv(l: K.Expression, r: K.Expression) = K.Application(K.Application(K.iff, l), r)
    val chain = ps.reduceRight(eqv)
    val conj = K.Application(K.Application(K.implies, chain), chain)
    val problem = Clausification.Problem(Seq.empty, Some(K.Sequent(Set.empty, Set(conj))))
    val proof = lisa.automation.clausification.CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(conj)))
  }

  test("ε end-to-end: a conjecture whose clausification Skolemizes to an ε-term (kernel-valid)") {
    val P = pred("P", 1); val x = vr("x")
    val forallPx = K.Application(K.forall, K.Lambda(x, ap(P, x))) // ∀x. P(x)
    // conjecture ∀x.P(x): its negation ¬∀x.P(x) NNF/Skolemizes to `¬P(ε(λx.¬P(x)))`, so the clause set carries
    // a genuine ε-term. `Clausal.prove` abstracts it (F), refutes P(x) vs ¬P(F) by x:=F, and reconstructs with
    // F inlined back to the ε-term, giving a purely ε-bearing, kernel-valid proof of `⊢ ∀x.P(x)`.
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(forallPx))), Some(K.Sequent(Set.empty, Set(forallPx))))
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(forallPx)))
  }

  /** A contract-shaped stub prover: imports = the clause-sequents, conclusion = `∅ ⊢`, via one `Sorry`.
   *  Kernel-checking a proof built on it validates the *composition* (the clausifier's new literal-set
   *  `Restate` steps included) while trusting only the refutation itself. */
  private def sorryProver(p: Clausification.Problem): K.SCProof =
    K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), p.imports)

  test("definitional naming end-to-end: a problem needing a naming atom, refuted by Bridge (kernel-valid)") {
    val A = pred("A", 0); val B = pred("B", 0); val C = pred("C", 0)
    val body = K.Application(K.Application(K.or, K.Application(K.Application(K.and, A), B)), C) // (A ∧ B) ∨ C
    // {(A ∧ B) ∨ C, ¬C} ⊢ A. Clausifies via definitional naming (a fresh predicate atom `nm ⟺ A ∧ B`); the
    // nm-clauses must be ingested by Bridge (nm as an uninterpreted predicate) and refuted, then discharged
    // by the clausifier. Exercises the schematic-predicate-variable path end to end with the real prover.
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(body)), K.Sequent(Set.empty, Set(K.Application(K.neg, C)))),
      Some(K.Sequent(Set.empty, Set(A)))
    )
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(A)))
  }

  test("clausifier emits naming-definition residual clauses in literal-set form (Q>0 composition kernel-valid)") {
    val A = pred("A", 0); val B = pred("B", 0); val C = pred("C", 0)
    val body = K.Application(K.Application(K.or, K.Application(K.Application(K.and, A), B)), C) // (A ∧ B) ∨ C
    // (A ∧ B) ∨ C is named (Q>0); its residual rewrite `nm ∨ C` must be emitted as the literal set `{nm, C}`
    // via the Restate. A Sorry refutation isolates that step for the kernel checker.
    val problem = Clausification.Problem(Seq(K.Sequent(Set.empty, Set(body))), Some(K.Sequent(Set.empty, Set(A))))
    val proof = CertifiedClausifier.certifyClausal(problem, sorryProver)
    // `Sorry` is the point here: the prover is stubbed so the kernel checks only the composition around it.
    KernelProof.assertCorrectProof(proof, "certifyClausal with a stubbed prover")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(A)))
  }

  test("probe: a multi-literal already-clausal axiom is handed to the prover as a literal set") {
    val P = pred("P", 0); val Q = pred("Q", 0)
    val pOrQ = K.Application(K.Application(K.or, P), Q) // P ∨ Q -- already clausal, MULTI-literal
    // {P ∨ Q, ¬P} ⊢ Q. The clausifier must now emit `P ∨ Q` as the literal set `{P, Q}` (one Restate),
    // exercising the uncertified path (all axioms clausal) and the new set-form conversion end-to-end.
    val problem = Clausification.Problem(
      Seq(K.Sequent(Set.empty, Set(pOrQ)), K.Sequent(Set.empty, Set(K.Application(K.neg, P)))),
      Some(K.Sequent(Set.empty, Set(Q)))
    )
    val proof = CertifiedClausifier.certifyClausal(problem, Clausal.prove)
    KernelProof.assertCorrectProofNoSorry(proof, "certifyClausal")
    assert(proof.conclusion == K.Sequent(Set.empty, Set(Q)))
  }
