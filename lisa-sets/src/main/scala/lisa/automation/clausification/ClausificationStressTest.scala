package lisa.automation.clausification

import lisa.automation.clausification.Clausification.Problem
import lisa.utils.K.{_, given}
import org.apache.commons.math3.fitting.{PolynomialCurveFitter, WeightedObservedPoints}

/** Stress runner for the certified clausification pipeline.
  *
  * Builds parametric formula families that exercise individual stages
  * (prenex, Skolem, Tseitin) plus a full-pipeline combo, runs the pipeline
  * end-to-end against a `Sorry`-based clausal back-end (so the runtime
  * reflects the clausification pipeline alone, not any propositional prover),
  * and reports:
  *   - input formula size (kernel nodes)
  *   - resulting kernel proof size (recursive step count)
  *   - wall-clock runtime (median over `--repeats`)
  *
  * For each family it then fits both a power law (`y = a · n^k`) and an
  * exponential (`y = a · b^n`) on log-transformed runtime, reports the
  * R² of each, and picks the better-fitting model.
  *
  * Run with:
  *   sbt "lisa-sets/runMain lisa.automation.clausification.ClausificationStressTest"
  *   sbt "lisa-sets/runMain lisa.automation.clausification.ClausificationStressTest --phase skolem"
  *   sbt "lisa-sets/runMain lisa.automation.clausification.ClausificationStressTest --phase prenex,tseitin --family prenex:2,4,8,16 --repeats 5"
  *
  * CLI args (all optional):
  *   --phase  name[,...]  phases to run: prenex, tseitin, skolem, combo, full, all  (default: all)
  *   --family name:n,...  override n-values for one family (repeatable)
  *   --prenex-strategy    heuristic|deconstruct|rewrite  (default: heuristic)
  *   --repeats k          median over k runs per n  (default: 3)
  */
object ClausificationStressTest {

  // ─────────────────────────────────────────────────────────────────────────
  // Sizing helpers
  // ─────────────────────────────────────────────────────────────────────────

  /** Total node count of a kernel expression (variables, constants, applications, lambdas). */
  def formulaSize(e: Expression): Int = e match
    case Application(f, a) => 1 + formulaSize(f) + formulaSize(a)
    case Lambda(_, body)   => 1 + formulaSize(body)
    case _                 => 1

  /** Sum of formula sizes across all sequents in a problem (LHS + RHS, hyps + conj). */
  def problemSize(p: Problem): Int = {
    def seqSize(s: Sequent): Int = s.left.toSeq.map(formulaSize).sum + s.right.toSeq.map(formulaSize).sum
    p.hypotheses.map(seqSize).sum + p.conjecture.fold(0)(seqSize)
  }

  /** Recursive step count of a kernel proof (a subproof contributes its own nested count, not 1). */
  def proofSize(p: SCProof): Int = p.steps.iterator.map {
    case SCSubproof(sp, _) => proofSize(sp)
    case _                 => 1
  }.sum

  // ─────────────────────────────────────────────────────────────────────────
  // Clausal back-end: Sorry stub.
  //
  // The stress runner is interested in the clausification pipeline's cost,
  // not in propositional proof search. We therefore short-circuit the clausal
  // refutation with a single [[Sorry]] step that takes the input clauses as
  // imports and concludes `clauses ⊢`. The kernel checker accepts this
  // (with `usesSorry = true`), the proof remains structurally valid, and the
  // back-end's contribution to runtime is O(1).
  // ─────────────────────────────────────────────────────────────────────────

  def refuteClausalProblem(problem: Problem): SCProof = {
    require(problem.conjecture.isEmpty, "Expected a clausal refutation problem")
    val allLiterals = problem.hypotheses.flatMap(_.right)
    val sorryBot = Sequent(allLiterals.toSet, Set.empty)
    SCProof(IndexedSeq(Sorry(sorryBot)), problem.imports)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Symbol pool
  // ─────────────────────────────────────────────────────────────────────────

  val P  = Variable(Identifier("P", 0), Ind >>: Prop)
  val R  = Variable(Identifier("R", 0), Ind >>: (Ind >>: Prop))

  def xv(i: Int): Variable = Variable(Identifier("x", i), Ind)
  def yv(i: Int): Variable = Variable(Identifier("y", i), Ind)
  def pv(i: Int): Variable = Variable(Identifier("p", i), Prop)

  // ─────────────────────────────────────────────────────────────────────────
  // Formula families
  // ─────────────────────────────────────────────────────────────────────────

  /** Prenex stress: `∀x₁.(P(x₁) ∧ ∀x₂.(P(x₂) ∧ ... ∧ ∀xₙ.P(xₙ)))`.
    *
    * Linear-in-n nesting of `∀` under `∧`-rights.  Every `∀` sits inside an
    * `∧`-right, so the prenex stage must lift each one through every enclosing
    * `∧` connector to reach the root: O(n²) one-layer lifts in total under
    * the rewriting strategy. The deconstruction strategy walks the tree
    * once, O(n). The heuristic switches between the two by formula size. */
  def prenexFamily(n: Int): Problem = {
    require(n >= 1)
    def build(i: Int): Expression =
      val v   = xv(i)
      val pi  = P(v)
      val matrix = if (i == n) pi else and(pi)(build(i + 1))
      forall(Lambda(v, matrix))
    Problem(Seq(() |- build(1)), None)
  }

  /** Flat right-associated conjunction of universals:
    * `(∀x₁.P(x₁)) ∧ ((∀x₂.P(x₂)) ∧ (… ∧ ∀xₙ.P(xₙ)))`.
    * Every ∀ sits at depth 1 in the ∧-tree; the deconstruct strategy
    * handles each independently in O(1) steps → O(n) total. */
  def prenexFlatAndFamily(n: Int): Problem = {
    require(n >= 1)
    val atoms = (1 to n).map(i => forall(Lambda(xv(i), P(xv(i)))): Expression)
    Problem(Seq(() |- atoms.reduceRight(and(_)(_))), None)
  }

  /** Flat right-associated disjunction of universals:
    * `(∀x₁.P(x₁)) ∨ ((∀x₂.P(x₂)) ∨ (… ∨ ∀xₙ.P(xₙ)))`.
    * Each ∀ must be lifted through its sibling disjuncts using the
    * `∀x.(φ∨ψ) ↔ (∀x.φ)∨ψ` prenex-rewrite rule; O(n) lifts total. */
  def prenexFlatOrFamily(n: Int): Problem = {
    require(n >= 1)
    val atoms = (1 to n).map(i => forall(Lambda(xv(i), P(xv(i)))): Expression)
    Problem(Seq(() |- atoms.reduceRight(or(_)(_))), None)
  }

  /** Alternating ∧/∨ of universals (right-associated):
    * `∀x₁.P ∧ (∀x₂.P ∨ (∀x₃.P ∧ (…)))`.
    * Exercises both `∀-over-∧` and `∀-over-∨` rules interleaved. */
  def prenexMixedFamily(n: Int): Problem = {
    require(n >= 1)
    val atoms = (1 to n).map(i => forall(Lambda(xv(i), P(xv(i)))): Expression)
    val formula = atoms.zipWithIndex.foldRight[Expression](atoms.last) { case ((a, i), acc) =>
      if (i == n - 1) a
      else if (i % 2 == 0) and(a)(acc)
      else or(a)(acc)
    }
    Problem(Seq(() |- formula), None)
  }

  /** Skolemization stress: `∃x₁.∀y₁.∃x₂.∀y₂. … ∃xₙ.∀yₙ. R(xₙ,yₙ)`.
    *
    * One alternation `∃∀` per level. The Skolem stage must introduce one
    * Skolem function per `∃` (each parameterised by the enclosing
    * `∀`-bound variables), giving Θ(n) Skolem steps with cumulative
    * arities 0..n. */
  def skolemFamily(n: Int): Problem = {
    require(n >= 1)
    val xn = xv(n); val yn = yv(n)
    val matrix = R(xn)(yn)
    def wrap(i: Int): Expression =
      val body = if (i == n) matrix else wrap(i + 1)
      exists(Lambda(xv(i), forall(Lambda(yv(i), body))))
    Problem(Seq(() |- wrap(1)), None)
  }

  /** Nullary-Skolem stress: `∃x₁.(∃x₂.(...(∃xₙ.R(x₁,xₙ))...))`.  No universals
    * in scope anywhere, so every Skolem function is a constant (arity 0).
    * Bridge cost: O(1) per step (no RightForall needed). */
  def skolemNullaryFamily(n: Int): Problem = {
    require(n >= 1)
    val matrix = if (n == 1) P(xv(1)) else R(xv(1))(xv(n))
    def wrap(i: Int): Expression =
      if (i > n) matrix else exists(Lambda(xv(i), wrap(i + 1)))
    Problem(Seq(() |- wrap(1)), None)
  }

  /** Max-arity-Skolem stress: `∀y₁...∀yₙ.∃x₁.∃x₂...∃xₙ.R(x₁,xₙ)`.
    * Every ∃ is inside all n universals, so each Skolem function has arity n.
    * Bridge cost: O(n) RightForall steps per Skolem → O(n²) bridge total. */
  def skolemMaxArityFamily(n: Int): Problem = {
    require(n >= 1)
    val matrix = if (n == 1) P(xv(1)) else R(xv(1))(xv(n))
    val existsPart = (1 to n).foldRight(matrix: Expression)((i, acc) => exists(Lambda(xv(i), acc)))
    val formula    = (1 to n).foldRight(existsPart: Expression)((i, acc) => forall(Lambda(yv(i), acc)))
    Problem(Seq(() |- formula), None)
  }

  /** Flat-conjunction-Skolem stress: `(∃x₁.P(x₁)) ∧ ((∃x₂.P(x₂)) ∧ (… ∧ ∃xₙ.P(xₙ)))`.
    * Independent existentials in a right-assoc conjunction context.  Arity 0 for every
    * Skolem, but the RightSubstIff context grows with the remaining conjunction at each step. */
  def skolemFlatConjFamily(n: Int): Problem = {
    require(n >= 1)
    val atoms = (1 to n).map(i => exists(Lambda(xv(i), P(xv(i)))): Expression)
    Problem(Seq(() |- atoms.reduceRight(and(_)(_))), None)
  }

  /** Tseitin stress: `(((p₁ ∧ p₂) ∨ p₃) ∧ p₄) ∨ p₅) ∧ ...` (length n).
    *
    * Left-deep alternating ∧/∨: every binary node is a non-clause connector.
    * n atoms → n−1 connectors → Θ(n) Tseitin steps, each AND step adds 3 new
    * clauses and each OR step adds 2 new clauses. */
  def tseitinFamily(n: Int): Problem = {
    require(n >= 1)
    def build(k: Int): Expression =
      if (k == 1) pv(1)
      else if (k % 2 == 0) and(build(k - 1))(pv(k))
      else                 or (build(k - 1))(pv(k))
    Problem(Seq(() |- build(n)), None)
  }

  /** Tseitin stress: `p₁ ∧ (p₂ ∧ (p₃ ∧ … ∧ pₙ))` (right-associative flat ∧).
    *
    * All connectors are AND; n atoms → n−1 AND steps, each adding 3 new clauses. */
  def tseitinFlatAndFamily(n: Int): Problem = {
    require(n >= 1)
    def build(k: Int): Expression =
      if (k == n) pv(n)
      else        and(pv(k))(build(k + 1))
    Problem(Seq(() |- build(1)), None)
  }

  /** Tseitin stress: `p₁ ∨ (p₂ ∨ (p₃ ∨ … ∨ pₙ))` (right-associative flat ∨).
    *
    * All connectors are OR; n atoms → n−1 OR steps, each adding 2 new clauses. */
  def tseitinFlatOrFamily(n: Int): Problem = {
    require(n >= 1)
    def build(k: Int): Expression =
      if (k == n) pv(n)
      else        or(pv(k))(build(k + 1))
    Problem(Seq(() |- build(1)), None)
  }

  /** Combo: alternating `∀∃` chain over a propositional `∧/∨` shell,
    * exercising every stage of the pipeline at once.
    *
    *   `inner = R(xₙ,yₙ)`
    *   `shell = ((p₁ ∧ p₂) ∨ inner)` — gives Tseitin a connector to abstract.
    *   hypothesis = `∀x₁∃y₁∀x₂∃y₂…∀xₙ∃yₙ. shell` */
  def comboFamily(n: Int): Problem = {
    require(n >= 1)
    val xn = xv(n); val yn = yv(n)
    val inner = R(xn)(yn)
    val shell = or(and(pv(1))(pv(2)))(inner)
    def wrap(i: Int): Expression =
      val body = if (i == n) shell else wrap(i + 1)
      forall(Lambda(xv(i), exists(Lambda(yv(i), body))))
    Problem(Seq(() |- wrap(1)), None)
  }

  /** Full-pipeline (linear): n independent hypotheses `∀yᵢ.∃xᵢ. P(xᵢ) ∧ P(yᵢ)`, one per index.
    *
    * Every hypothesis independently exercises every pipeline stage:
    *   NNF (trivial), Skolem (one ∃ of arity 1), Prenex (one ∀), Tseitin (one ∧).
    * Proof size is O(n) under the flat Tseitin/axiomwise design (`certifyTseitinFlat`
    * gathers all per-axiom Tseitin IFFs into a single outer csub, eliminating the
    * O(n²) per-level Weakening cost of the legacy nested layout). */
  def fullLinearFamily(n: Int): Problem = {
    require(n >= 1)
    val hyps = (1 to n).map { i =>
      () |- forall(Lambda(yv(i), exists(Lambda(xv(i), and(P(xv(i)))(P(yv(i)))))))
    }
    Problem(hyps, None)
  }

  /** Full-pipeline (conjecture): the [[comboFamily]] formula posed as a theorem to be disproven.
    *
    * Conjecture: `∀x₁.∃y₁.…∀xₙ.∃yₙ. (p₁ ∧ p₂) ∨ R(xₙ,yₙ)`.
    *
    * [[certifyNegated]] negates it, then the whole pipeline fires on the negated formula
    * `∃x₁.∀y₁.…∃xₙ.∀yₙ. (¬p₁ ∨ ¬p₂) ∧ ¬R(xₙ,yₙ)`.  Skolem introduces n functions of
    * growing arity (0..n−1), giving O(n²) Skolem work; Prenex and Tseitin are O(n) and O(1). */
  def fullConjectureFamily(n: Int): Problem = {
    require(n >= 1)
    val xn = xv(n); val yn = yv(n)
    val inner = R(xn)(yn)
    val shell = or(and(pv(1))(pv(2)))(inner)
    def wrap(i: Int): Expression =
      val body = if (i == n) shell else wrap(i + 1)
      forall(Lambda(xv(i), exists(Lambda(yv(i), body))))
    Problem(Seq.empty, Some(() |- wrap(1)))
  }

  /** Full-pipeline (implication chain): `(∀x₁.P(x₁)) → ((∀x₂.P(x₂)) → (... → ∀xₙ.P(xₙ)))`.
    *
    * NNF unfolds each `A → B` into `¬A ∨ B`, producing
    * `(∃x₁.¬P) ∨ ((∃x₂.¬P) ∨ (… ∨ ∀xₙ.P))` after NNF.
    * Skolem: n−1 nullary constants (all ∃ sit under no enclosing ∀).
    * Prenex: the single remaining `∀xₙ` must cross n−1 ∨-layers via `∀-over-∨` rewrites.
    * Tseitin: n−1 binary ∨ connectors.
    * Dominant cost: O(n²) from Skolem spine traversal +
    *   O(n²) Prenex rewrite steps (n−1 layers × cumulative context size). */
  def fullImplicationChainFamily(n: Int): Problem = {
    require(n >= 1)
    val atoms = (1 to n).map(i => forall(Lambda(xv(i), P(xv(i)))): Expression)
    Problem(Seq(() |- atoms.reduceRight(implies(_)(_))), None)
  }

  /** Full-pipeline (negated ∃∀ interleaved): `¬(∃x₁.∀y₁.∃x₂.∀y₂.….∃xₙ.∀yₙ.R(xₙ,yₙ))`.
    *
    * NNF flips every quantifier (`¬∃ = ∀`, `¬∀ = ∃`), producing
    * `∀x₁.∃y₁.∀x₂.∃y₂.….∀xₙ.∃yₙ.¬R(xₙ,yₙ)` after NNF.
    * Skolem: n Skolem functions of arities 1, 2, …, n — total O(n²) arity sum.
    * Prenex: n universals stripped (trivial; the formula is already prenex after Skolem).
    * Tseitin: `¬R(…)` is a literal — trivial. */
  def fullNegatedInterleavedFamily(n: Int): Problem = {
    require(n >= 1)
    val matrix = R(xv(n))(yv(n))
    def wrap(i: Int): Expression =
      val body = if (i == n) matrix else wrap(i + 1)
      exists(Lambda(xv(i), forall(Lambda(yv(i), body))))
    Problem(Seq(() |- neg(wrap(1))), None)
  }

  /** Full-pipeline (negated ¬∀ alternation): `¬∀x₁.¬∀x₂.….¬∀xₙ.P(xₙ)` (outermost is ¬∀).
    *
    * NNF collapses each `¬∀x.φ → ∃x.¬φ` together with double-negation elimination,
    * producing `∃x₁.∀x₂.∃x₃.….P_or_¬P(xₙ)` (alternating ∃∀, matrix positive iff n even).
    * Skolem: ⌈n/2⌉ functions of arities 0, 1, …, ⌊n/2⌋−1 — O(n²/4) arity sum.
    * Prenex: ⌊n/2⌋ universals stripped.
    * Tseitin: single literal — trivial. */
  def fullNegUnivChainFamily(n: Int): Problem = {
    require(n >= 1)
    def wrap(i: Int): Expression =
      if (i > n) P(xv(n))
      else neg(forall(Lambda(xv(i), wrap(i + 1))))
    Problem(Seq(() |- wrap(1)), None)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Measurement
  // ─────────────────────────────────────────────────────────────────────────

  case class Sample(n: Int, formulaSize: Int, proofSize: Int, timeMs: Double)

  def median(xs: Seq[Double]): Double = {
    val s = xs.sorted
    val n = s.size
    if (n % 2 == 1) s(n / 2) else (s(n / 2 - 1) + s(n / 2)) / 2.0
  }

  /** Run one (n, generator) timing.  Returns median of `repeats` runs.
    *
    * @param runner  the pipeline entry point to benchmark, e.g.
    *                [[Clausification.certifyClausal]], [[Clausification.certifySkolemPhase]],
    *                [[Clausification.certifyPrenexPhase]], or [[Clausification.certifyTseitinPhase]].
    *                Defaults to the full pipeline. */
  def runOne(n: Int, gen: Int => Problem, repeats: Int,
             runner: (Problem, Problem => SCProof) => SCProof = Clausification.certifyClausal): Sample = {
    val problem = gen(n)
    val fsize   = problemSize(problem)
    val ts = scala.collection.mutable.ArrayBuffer.empty[Double]
    var lastProof: SCProof = null
    for (_ <- 0 until repeats) {
      val t0    = System.nanoTime()
      val proof = runner(problem, refuteClausalProblem)
      val ms    = (System.nanoTime() - t0) / 1e6
      lastProof = proof
      ts += ms
    }
    Sample(n, fsize, proofSize(lastProof), median(ts.toSeq))
  }

  /** Run a family across all `ns`, with one warmup pass discarded.
    *
    * @param runner  see [[runOne]]. */
  def measure(name: String, ns: Seq[Int], gen: Int => Problem, repeats: Int,
              runner: (Problem, Problem => SCProof) => SCProof = Clausification.certifyClausal): Seq[Sample] = {
    println(s"\n── $name ──")
    // Warmup with the smallest n to let the JIT stabilize.
    if (ns.nonEmpty) runOne(ns.head, gen, 1, runner)
    println(f"${"n"}%4s  ${"|F|"}%8s  ${"|proof|"}%10s  ${"time(ms)"}%10s")
    ns.map { n =>
      val s = runOne(n, gen, repeats, runner)
      println(f"${s.n}%4d  ${s.formulaSize}%8d  ${s.proofSize}%10d  ${s.timeMs}%10.2f")
      s
    }
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Regression helpers
  // ─────────────────────────────────────────────────────────────────────────

  /** Fit a polynomial of the given `degree` via OLS using Commons Math.
    * Returns `(coeffs, r2)` where `coeffs(k)` is the coefficient of `x^k`
    * (i.e. constant first, then linear, then quadratic, …). */
  def fitPoly(xs: Seq[Double], ys: Seq[Double], degree: Int): (Array[Double], Double) = {
    val obs = new WeightedObservedPoints()
    xs.zip(ys).foreach { case (x, y) => obs.add(x, y) }
    val coeffs = PolynomialCurveFitter.create(degree).fit(obs.toList)
    val yMean  = ys.sum / ys.size
    val ssTot  = ys.map(y => (y - yMean) * (y - yMean)).sum
    val ssRes  = xs.zip(ys).map { case (x, y) =>
      val yp = coeffs.zipWithIndex.map { case (c, k) => c * math.pow(x, k) }.sum
      (y - yp) * (y - yp)
    }.sum
    val r2 = if (ssTot == 0.0) 1.0 else 1.0 - ssRes / ssTot
    (coeffs, r2)
  }

  /** Least-squares fit of `log y = log a + k · log x`. Returns (k, a, R²). */
  def fitPower(xs: Seq[Double], ys: Seq[Double]): (Double, Double, Double) = {
    val (c, r2) = fitPoly(xs.map(math.log), ys.map(math.log), 1)
    (c(1), math.exp(c(0)), r2)
  }

  /** Least-squares fit of `log y = log a + x · log b`. Returns (b, a, R²). */
  def fitExp(xs: Seq[Double], ys: Seq[Double]): (Double, Double, Double) = {
    val (c, r2) = fitPoly(xs, ys.map(math.log), 1)
    (math.exp(c(1)), math.exp(c(0)), r2)
  }

  /** Format `coeffs` (constant-first) as a human-readable polynomial string. */
  private def polyStr(coeffs: Array[Double]): String = {
    val labels = Array("" , "·n", "·n²", "·n³", "·n⁴")
    val terms  = coeffs.zipWithIndex.reverse.flatMap { case (c, k) =>
      if (math.abs(c) < 1e-6) None
      else {
        val lbl = if (k < labels.length) labels(k) else s"·n^$k"
        Some(f"${c}%+.4g$lbl")
      }
    }
    if (terms.isEmpty) "0" else terms.mkString(" ").stripPrefix("+")
  }

  /** Fit degrees 1 and 2; report whichever has a higher R², preferring
    * degree 1 unless degree 2 improves R² by at least 0.005. */
  private def bestPolyReport(label: String, xs: Seq[Double], ys: Seq[Double]): Unit = {
    val (c1, r21) = fitPoly(xs, ys, 1)
    val (c2, r22) = fitPoly(xs, ys, 2)
    val (coeffs, r2, deg) =
      if (r22 > r21 + 0.005) (c2, r22, 2) else (c1, r21, 1)
    println(f"  $label%-14s ~  ${polyStr(coeffs)}  (R² = $r2%.4f, degree $deg)")
  }

  def report(name: String, samples: Seq[Sample]): Unit = {
    if (samples.size < 3) {
      println(s"\n── $name regression ── (need ≥3 samples, got ${samples.size}; skipping)")
      return
    }
    val xs = samples.map(_.n.toDouble)
    val ts = samples.map(s => math.max(s.timeMs, 0.01))
    val ps = samples.map(_.proofSize.toDouble)
    val fs = samples.map(_.formulaSize.toDouble)
    println(s"\n── $name regression ──")
    def both(label: String, ys: Seq[Double]): Unit = {
      val (k, _, r2p) = fitPower(xs, ys)
      bestPolyReport(s"$label (poly)", xs, ys)
      println(f"  ${"" + label + " (power)"}%-20s ~  n^$k%.3f  (R² = $r2p%.4f)")
    }
    both("formula size", fs)
    both("proof size",   ps)
    both("runtime",      ts)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // CLI
  // ─────────────────────────────────────────────────────────────────────────

  val defaultPrenex     = Seq(2, 4, 6, 8, 10, 12, 16, 20)
  val defaultPrenexFlatAnd = Seq(2, 4, 6, 8, 10, 12, 16, 20)
  val defaultPrenexFlatOr  = Seq(2, 4, 6, 8, 10, 12, 16, 20)
  val defaultPrenexMixed   = Seq(2, 4, 6, 8, 10, 12, 16, 20)
  val defaultTseitin        = Seq(8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168, 176, 184, 192, 200)
  val defaultTseitinFlatAnd = defaultTseitin
  val defaultTseitinFlatOr  = defaultTseitin
  val defaultSkolem        = Seq(2, 3, 4, 5, 6, 7, 8)
  val defaultSkolemNullary = Seq(2, 3, 4, 5, 6, 7, 8)
  val defaultSkolemMaxArity= Seq(2, 3, 4, 5, 6, 7, 8)
  val defaultSkolemFlatConj= Seq(2, 3, 4, 5, 6, 7, 8)
  val defaultCombo           = Seq(2, 3, 4, 5, 6)
  val defaultFullLinear         = Seq(2, 4, 8, 16, 32, 64, 128)
  val defaultFullConjecture     = Seq(2, 3, 4, 5, 6, 7, 8)
  val defaultFullImplChain      = Seq(2, 4, 8, 16, 32, 48)
  val defaultFullNegInterleaved = Seq(2, 4, 8, 16, 24, 32)
  val defaultFullNegUnivChain   = Seq(2, 4, 8, 16, 32, 64)

  private def parseInts(s: String): Seq[Int] =
    s.split(",").map(_.trim).filter(_.nonEmpty).map(_.toInt).toSeq

  private case class Cli(
      phases: Option[Set[String]]     = None,           // None = all phases
      familyNs: Map[String, Seq[Int]] = Map.empty,      // per-family n overrides
      repeats: Int                    = 3,
      prenexStrategy: String          = "heuristic"
  )

  private def parseArgs(args: Array[String]): Cli = {
    def loop(rest: List[String], acc: Cli): Cli = rest match
      case Nil => acc
      case "--phase" :: v :: t =>
        val ps = v.split(",").map(_.trim).filter(_.nonEmpty).toSet
        loop(t, acc.copy(phases = Some(acc.phases.fold(ps)(_ ++ ps))))
      case "--family" :: v :: t =>
        val colon = v.indexOf(':')
        require(colon > 0, s"--family requires name:n1,n2,... format; got: $v")
        val name = v.substring(0, colon).trim
        val ns   = parseInts(v.substring(colon + 1))
        loop(t, acc.copy(familyNs = acc.familyNs + (name -> ns)))
      case "--prenex-strategy" :: v :: t =>
        require(Set("heuristic","deconstruct","rewrite").contains(v),
          s"--prenex-strategy must be heuristic, deconstruct, or rewrite; got: $v")
        loop(t, acc.copy(prenexStrategy = v))
      case "--repeats" :: v :: t => loop(t, acc.copy(repeats = v.toInt))
      case "--help" :: _ | "-h" :: _ =>
        println(helpText); sys.exit(0)
      case other :: _ =>
        sys.error(s"Unknown argument: $other (try --help)")
    loop(args.toList, Cli())
  }

  private val helpText: String =
    """ClausificationStressTest — measure pipeline scaling
      |
      |Usage: runMain lisa.automation.clausification.ClausificationStressTest [options]
      |
      |Options:
      |  --phase name[,...]     phases to run (default: all)
      |                         names: prenex, tseitin, skolem, combo, full, all
      |                         can be given multiple times to accumulate
      |  --family name:n1,...   override n-values for a specific family (repeatable)
      |                         family names:
      |                           prenex, prenex-flat-and, prenex-flat-or, prenex-mixed
      |                           tseitin, tseitin-flat-and, tseitin-flat-or
      |                           skolem, skolem-nullary, skolem-max-arity, skolem-flat-conj
      |                           combo
      |                           full-linear, full-conjecture, full-impl-chain,
      |                           full-neg-interleaved, full-neg-univ-chain
      |  --prenex-strategy      heuristic|deconstruct|rewrite  (default: heuristic)
      |  --repeats k            median over k runs per n  (default: 3)
      |  --help, -h             this message
      |""".stripMargin

  def main(args: Array[String]): Unit = {
    val cli = parseArgs(args)

    val prenexRunner: (Problem, Problem => SCProof) => SCProof =
      cli.prenexStrategy match
        case "deconstruct" => Clausification.certifyPrenexDeconstructPhase
        case "rewrite"     => Clausification.certifyPrenexRewritePhase
        case _             => Clausification.certifyPrenexPhase

    def phaseActive(phase: String): Boolean =
      cli.phases.fold(true)(ps => ps("all") || ps(phase))

    def ns(key: String, default: Seq[Int]): Seq[Int] =
      cli.familyNs.getOrElse(key, default)

    // Each entry: (key, label, phase, generator, runner, default n-values)
    type Runner = (Problem, Problem => SCProof) => SCProof
    val allFamilies: Seq[(String, String, String, Int => Problem, Runner, Seq[Int])] = Seq(
      ("prenex",               "Prenex (∀ nested in ∧)",           "prenex",  prenexFamily,                prenexRunner,                       defaultPrenex),
      ("prenex-flat-and",      "Prenex (flat ∧ of ∀)",             "prenex",  prenexFlatAndFamily,         prenexRunner,                       defaultPrenexFlatAnd),
      ("prenex-flat-or",       "Prenex (flat ∨ of ∀)",             "prenex",  prenexFlatOrFamily,          prenexRunner,                       defaultPrenexFlatOr),
      ("prenex-mixed",         "Prenex (alternating ∧/∨ of ∀)",    "prenex",  prenexMixedFamily,           prenexRunner,                       defaultPrenexMixed),
      ("tseitin",              "Tseitin (alternating ∧/∨)",        "tseitin", tseitinFamily,               Clausification.certifyTseitinPhase, defaultTseitin),
      ("tseitin-flat-and",     "Tseitin (flat ∧)",                 "tseitin", tseitinFlatAndFamily,        Clausification.certifyTseitinPhase, defaultTseitinFlatAnd),
      ("tseitin-flat-or",      "Tseitin (flat ∨)",                 "tseitin", tseitinFlatOrFamily,         Clausification.certifyTseitinPhase, defaultTseitinFlatOr),
      ("skolem",               "Skolem (interleaved ∃∀)",          "skolem",  skolemFamily,                Clausification.certifySkolemPhase,  defaultSkolem),
      ("skolem-nullary",       "Skolem (nullary, nested ∃)",        "skolem",  skolemNullaryFamily,         Clausification.certifySkolemPhase,  defaultSkolemNullary),
      ("skolem-max-arity",     "Skolem (max arity, ∀∀…∃∃)",       "skolem",  skolemMaxArityFamily,        Clausification.certifySkolemPhase,  defaultSkolemMaxArity),
      ("skolem-flat-conj",     "Skolem (flat ∧ of ∃)",             "skolem",  skolemFlatConjFamily,        Clausification.certifySkolemPhase,  defaultSkolemFlatConj),
      ("combo",                "Combo (∀∃ chain × ∧)",             "combo",   comboFamily,                 Clausification.certifyClausal,      defaultCombo),
      ("full-linear",          "Full pipeline (n hyps, linear)",   "full",    fullLinearFamily,            Clausification.certifyClausal,      defaultFullLinear),
      ("full-conjecture",      "Full pipeline (conjecture)",        "full",    fullConjectureFamily,        Clausification.certifyClausal,      defaultFullConjecture),
      ("full-impl-chain",      "Full pipeline (impl chain)",        "full",    fullImplicationChainFamily,  Clausification.certifyClausal,      defaultFullImplChain),
      ("full-neg-interleaved", "Full pipeline (neg interleaved)",  "full",    fullNegatedInterleavedFamily,Clausification.certifyClausal,      defaultFullNegInterleaved),
      ("full-neg-univ-chain",  "Full pipeline (neg ¬∀ chain)",      "full",    fullNegUnivChainFamily,      Clausification.certifyClausal,      defaultFullNegUnivChain),
    )

    val results = scala.collection.mutable.ArrayBuffer.empty[(String, Seq[Sample])]
    allFamilies.foreach { case (key, label, phase, gen, runner, defaults) =>
      if (phaseActive(phase))
        results += label -> measure(label, ns(key, defaults), gen, cli.repeats, runner)
    }

    println("\n══════════════════════════════════════════════════════════════")
    println("                       Regression report")
    println("══════════════════════════════════════════════════════════════")
    results.foreach((name, ss) => report(name, ss))
  }
}
