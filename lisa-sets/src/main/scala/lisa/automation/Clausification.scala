package lisa.automation
import lisa.utils.K
import lisa.utils.K.{_, given}

/**
  * This object contains methods to transform sequents into clausal form, as well as produce a proof
  * that assumes the original sequent and proves the clausal form.
  *
  * The clausal form is a set of clauses. Each clause is a set of literals {x, y, z, ...} that is
  * represented as the sequent `() |- x, y, z, …`. A literal is either an atomic formula or its negation.
  *
  * The transformation is done in several steps:
  *   1. Negation of the conjecture:  add ¬conjecture as a hypothesis and target ⊥
  *   2. Negation Normal Form (NNF):  push ¬ inward, eliminate ⇒ and ⇔
  *   3. Skolemization:               eliminate existential quantifiers using ε-terms / Skolem constants
  *   4. Prenex Normal Form (PNF):    pull universal quantifiers to the front and then strip them
  *   5. Tseitin transform:           introduce fresh predicate names for compound sub-formulas
  *
  * Each step is a function `Problem => (Problem, SCProof)` that returns:
  *   - the transformed problem (ready for the next stage), and
  *   - an `SCProof` that, given the *transformed* problem's hypotheses as imports, derives all
  *     *original* problem hypotheses (plus conjecture handling).
  *
  * The full pipeline is assembled in `certify_clausal`, which threads these proofs together via
  * `SCSubproof` to produce a single end-to-end certified proof.
  *
  * A `Problem` is a pair of:
  *   - `hypotheses`: a list of formulas φ_i, each representing the assumed sequent `() |- φ_i`.
  *     Inside an `SCProof` these map to imports, referenced by negative indices (-1, -2, …).
  *   - `conjecture`: `Some(φ)` (the goal to prove) or `None` (derive ⊥ from the hypotheses).
  * There are no names; proof steps are tracked by their integer index, as is standard in Lisa.
  */
object Clausification {

  // ─────────────────────────────────────────────────────────────────────────────
  // Data types
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * A clausification problem.
    *
    * @param hypotheses  The assumed axioms, each expressed as a single formula φ representing
    *                    the sequent `() |- φ`.  Inside an `SCProof` these correspond to the
    *                    imported sequents, referenced by negative indices (-1, -2, …).
    * @param conjecture  `Some(φ)` if the goal is to prove φ; `None` if the goal is already ⊥
    *                    (i.e. a contradiction should be derived from the hypotheses alone).
    *                    When `Some(φ)`, the conjecture import sits at index `-(hypotheses.size + 1)`.
    *
    * Invariant: every hypothesis formula and the conjecture formula (if present) must have sort `Prop`.
    */
  case class Problem(hypotheses: Seq[Expression], conjecture: Option[Expression]) {
    /** All imports of the corresponding `SCProof`: hypotheses first, then (optionally) the conjecture. */
    def imports: IndexedSeq[Sequent] =
      (hypotheses.map(() |- _) ++ conjecture.map(() |- _)).toIndexedSeq

    /** Number of hypothesis imports. */
    def numHyps: Int = hypotheses.size

    /** Import index (negative) for the i-th hypothesis (0-based). */
    def hypIndex(i: Int): Int = -(i + 1)

    /** Import index (negative) for the conjecture (only valid when `conjecture.isDefined`). */
    def conjectureIndex: Int = -(hypotheses.size + 1)
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Top-level pipeline
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * Solves `problem` by running the full certified clausification pipeline and then
    * calling `prover` on the resulting fully-clausal problem.
    *
    * Each pipeline stage `f` has type `Problem => (Problem, SCProof)`:
    *   - The first component is the transformed problem fed to the next stage.
    *   - The second component is an `SCProof` that bridges the two problems:
    *     its imports are exactly `nextProblem.imports` and its conclusion matches the
    *     sequents needed by the previous stage.
    *
    * The stages are composed by nesting each bridge proof inside an `SCSubproof`, threading
    * the import indices through the chain.
    *
    * @param problem  The original problem (hypotheses + optional conjecture).
    * @param prover   Solves the final fully-clausal problem (all hypotheses are unit clauses,
    *                 conjecture is `None`).  Must return an `SCProof` with
    *                 `clausedProblem.imports` as its import list and `() |- ⊥` as its conclusion.
    * @return An `SCProof` with `problem.imports` as its import list and `() |- ⊥` as its conclusion.
    */
  def certify_clausal(problem: Problem, prover: Problem => SCProof): SCProof = {
    // Apply the pipeline stages in order, collecting bridge proofs.
    val (nnfProblem,    nnfBridge)    = certify_negated(problem)
    val (skolemProblem, skolemBridge) = certify_nnf(nnfProblem)
    val (prenexProblem, prenexBridge) = certify_skolem(skolemProblem)
    val (tseitinProblem,tseitinBridge)= certify_prenex(prenexProblem)
    val (clausProblem,  clausBridge)  = certify_tseitin(tseitinProblem)
    val innerProof = prover(clausProblem)

    // Compose: wrap innerProof in SCSubproof, then thread back through each bridge proof.
    // Each bridge proof B_k has imports = nextProblem.imports and adds some steps on top.
    // We compose them by: given a proof P with imports = nextProblem.imports,
    // produce a new proof whose imports = curProblem.imports by wrapping P in an SCSubproof
    // inside B_k.
    //
    // composeWithBridge(bridge, innerSCProof):
    //   bridge.imports  == nextProblem.imports  (already known at construction time)
    //   innerSCProof    is a proof of () |- ⊥ whose imports == nextProblem.imports
    //   result          is a proof of () |- ⊥ whose imports == curProblem.imports
    def composeWithBridge(bridge: SCProof, inner: SCProof): SCProof = {
      // The bridge's last step is a proof of () |- ⊥ that references its own imports.
      // We replace the bridge by appending one SCSubproof step that embeds `inner`,
      // where the i-th import of `inner` is provided by the i-th step of `bridge`.
      // Since each bridge step k produces the sequent for inner import -(k+1), the
      // SCSubproof premises are simply 0, 1, …, inner.imports.size - 1.
      val premises = (0 until inner.imports.size).toSeq
      val sub = SCSubproof(inner, premises)
      SCProof(bridge.steps :+ sub, bridge.imports)
    }

    Seq(clausBridge, tseitinBridge, prenexBridge, skolemBridge, nnfBridge)
      .foldLeft(innerProof)(composeWithBridge)
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Step 1 – Negate the conjecture
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * Stage 1: negate the conjecture.
    *
    * Transforms a problem with a non-trivial conjecture φ into an equivalent problem with
    * `conjecture = None` (i.e. target ⊥) by appending ¬φ as the last hypothesis.
    *
    * Returns:
    *   - `negProblem`: same hypotheses with ¬φ appended, `conjecture = None`.
    *   - `bridge`: an `SCProof` with `negProblem.imports` as its import list.
    *     Its steps produce the sequents `() |- h_0, …, () |- h_{n-1}` (forwarded directly from
    *     the first n imports) and eventually derive the original conjecture `() |- φ`, so that
    *     the outer stage can recover a proof of `() |- φ` from a proof of `() |- ⊥`.
    *
    * Concretely, `bridge` has imports:
    * {{{
    *   -1 … -(n)   : () |- h_0,  …,  () |- h_{n-1}
    *   -(n+1)      : () |- ¬φ
    * }}}
    * and the following steps (indices 0…n+2):
    * {{{
    *   0 … n-1  : Restate( () |- h_i,  -(i+1) )   — forward each hypothesis unchanged
    *   n        : Hypothesis    φ |- φ
    *   n+1      : RightNot(n)   () |- φ, ¬φ
    *   n+2      : Cut(n+1, n+1, ¬φ)  — NOTE: the outer composeWithBridge will fill in the inner proof;
    *              placeholder cut step at n+2 that the composition replaces with SCSubproof + Cut.
    * }}}
    *
    * If `conjecture = None` the problem is returned unchanged together with an identity bridge.
    */
  def certify_negated(problem: Problem): (Problem, SCProof) =
    problem.conjecture match
      case None =>
        // Identity: bridge proof has the same imports and just re-states each hypothesis.
        val steps = problem.hypotheses.zipWithIndex.map { (h, i) =>
          Restate(() |- h, -(i + 1))
        }.toIndexedSeq
        (problem, SCProof(steps, problem.imports))

      case Some(phi) =>
        val negPhi      = neg(phi)
        val negProblem  = Problem(problem.hypotheses :+ negPhi, None)
        val n           = problem.numHyps

        // Bridge imports = negProblem.imports = h_0 … h_{n-1}, ¬φ
        // step 0…n-1:  forward the hypotheses
        val fwdSteps: IndexedSeq[SCProofStep] =
          problem.hypotheses.zipWithIndex.map { (h, i) =>
            Restate(() |- h, -(i + 1))
          }.toIndexedSeq
        // step n:   Hypothesis  φ |- φ
        val stepHyp  = Hypothesis(phi |- phi, phi)
        // step n+1: RightNot    () |- φ, ¬φ   (premise = step n)
        val stepNegR = RightNot(() |- (phi, negPhi), n, phi)
        // step n+2: Cut  () |- φ   cutting on ¬φ between the inner contradiction and step n+1
        // The inner proof (of () |- ⊥) will be spliced in as an SCSubproof at step n+2 by
        // composeWithBridge; so the Cut here is a placeholder using upcoming step indices:
        //   SCSubproof at n+2,  RightNot at n+1  → Cut at n+3
        // We leave those concrete indices to composeWithBridge; the bridge ends at step n+1.
        val bridge = SCProof(fwdSteps ++ IndexedSeq(stepHyp, stepNegR), negProblem.imports)
        (negProblem, bridge)

  // ─────────────────────────────────────────────────────────────────────────────
  // Step 2 – Negation Normal Form
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * Stage 2: rewrite every hypothesis to Negation Normal Form.
    *
    * Because NNF is OL-equivalent to the original formula, each rewrite is certified by a
    * `Restate` step (which the SC proof-checker accepts when `isSame` returns `true`).
    *
    * Returns:
    *   - `nnfProblem`: same conjecture, but each hypothesis φ_i replaced by `toNNF(φ_i)`.
    *   - `bridge`: an `SCProof` with `nnfProblem.imports` as its import list.
    *     Step i is `Restate(() |- φ_i, -(i+1))`, re-deriving the *original* hypothesis from the
    *     NNF version (justified by OL equivalence).
    *
    * Requires: `problem.conjecture == None`.
    */
  def certify_nnf(problem: Problem): (Problem, SCProof) = {
    require(problem.conjecture.isEmpty, "certify_nnf expects conjecture = None")
    val nnfHyps    = problem.hypotheses.map(toNNF(_, negated = false))
    val nnfProblem = Problem(nnfHyps, None)
    // Bridge: imports are nnfProblem.imports.  Step i re-states φ_i from its NNF version.
    val steps: IndexedSeq[SCProofStep] =
      problem.hypotheses.zipWithIndex.map { (h, i) =>
        Restate(() |- h, -(i + 1))
      }.toIndexedSeq
    (nnfProblem, SCProof(steps, nnfProblem.imports))
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Step 3 – Skolemization
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * Stage 3: eliminate existential quantifiers using Hilbert's ε-operator.
    *
    * For each hypothesis containing `∃x.P(x)` (with free variables y₁,…,yₖ), introduces a
    * fresh Skolem constant `Sk_i : Ind^k → Ind` and replaces the existential by `P(Sk_i(y₁,…,yₖ))`.
    * The justification uses:
    * {{{
    *   ∃x.P(x) ⟺ P(εx.P(x))    [classical ε-axiom, RightEpsilon]
    *   P(εx.P(x)) ≡ P(Sk_i(…)) [by definition, RightSubstEq with the equality ε = Sk_i(…)]
    * }}}
    * The process is iterated (innermost-first) until no existential quantifiers remain.
    *
    * Returns:
    *   - `skolProblem`: same structure but every `∃` replaced by the corresponding Skolem term.
    *   - `bridge`: an `SCProof` with `skolProblem.imports` as imports, whose steps re-derive
    *     each original hypothesis from the Skolemized version.
    *
    * Requires: `problem.conjecture == None`.
    */
  def certify_skolem(problem: Problem): (Problem, SCProof) = {
    require(problem.conjecture.isEmpty, "certify_skolem expects conjecture = None")
    val counter = Counter()
    // TODO: implement the certified Skolemization loop.
    // For now, if no hypothesis contains an existential, this is an identity step.
    val skolHyps    = problem.hypotheses.map(skolemize(_, counter))
    val skolProblem = Problem(skolHyps, None)
    val steps: IndexedSeq[SCProofStep] =
      problem.hypotheses.zipWithIndex.map { (h, i) =>
        Restate(() |- h, -(i + 1))  // placeholder — replace with actual justification chain
      }.toIndexedSeq
    (skolProblem, SCProof(steps, skolProblem.imports))
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Step 4 – Prenex Normal Form (strip universal quantifiers)
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * Stage 4: strip universal quantifiers.
    *
    * Each hypothesis `∀x₁.…∀xₖ.M` (already in Skolem normal form, so no `∃`) is transformed into
    * the open formula `M[V₁/x₁, …, Vₖ/xₖ]` by instantiating with fresh free variables `V_j`.
    * The justification uses:
    *   - A `Restate` step to move to the prenex form (OL-equivalent).
    *   - `LeftForall` / `InstSchema` steps to strip each leading `∀`.
    *
    * Returns:
    *   - `prenexProblem`: hypotheses are the open matrices (quantifier-free).
    *   - `bridge`: re-derives the original `∀`-prefixed hypotheses from the open matrices.
    *
    * Requires: `problem.conjecture == None`.
    */
  def certify_prenex(problem: Problem): (Problem, SCProof) = {
    require(problem.conjecture.isEmpty, "certify_prenex expects conjecture = None")
    val counter = Counter()
    // TODO: implement the certified prenex-stripping loop.
    val (prenexHyps, _) = problem.hypotheses.map(stripUniversals(_, counter)).unzip
    val prenexProblem   = Problem(prenexHyps, None)
    val steps: IndexedSeq[SCProofStep] =
      problem.hypotheses.zipWithIndex.map { (h, i) =>
        Restate(() |- h, -(i + 1))  // placeholder
      }.toIndexedSeq
    (prenexProblem, SCProof(steps, prenexProblem.imports))
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Step 5 – Tseitin transform
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * Stage 5: Tseitin encoding — transform every non-clausal hypothesis into a set of clauses.
    *
    * For a hypothesis `() |- C[g ∧ h]` (or `C[g ∨ h]`) where g and h are literals:
    *   1. Introduce a fresh predicate `Ts_i` (with the free variables of `g ∧ h` as parameters).
    *   2. Add the defining clause(s):
    *        `∧` case:  `() |- ¬Ts_i ∨ g`  and  `() |- ¬Ts_i ∨ h`
    *        `∨` case:  `() |- ¬Ts_i ∨ g ∨ h`
    *   3. Replace `g ∧ h` (or `g ∨ h`) by `Ts_i` in the original hypothesis.
    *   4. Certify using `RightSubstEq` / `Restate`.
    * The process repeats until every hypothesis is a disjunction of literals (a clause).
    *
    * Returns:
    *   - `clausProblem`: all hypotheses are clauses.
    *   - `bridge`: re-derives all original hypotheses from the Tseitin clauses.
    *
    * Requires: `problem.conjecture == None`.
    */
  def certify_tseitin(problem: Problem): (Problem, SCProof) = {
    require(problem.conjecture.isEmpty, "certify_tseitin expects conjecture = None")
    val counter = Counter()
    // TODO: implement the certified Tseitin loop.
    // For now this is an identity step (correct when every hypothesis is already a clause).
    val steps: IndexedSeq[SCProofStep] =
      problem.hypotheses.zipWithIndex.map { (h, i) =>
        Restate(() |- h, -(i + 1))
      }.toIndexedSeq
    (problem, SCProof(steps, problem.imports))
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Pure (uncertified) formula transformations  (helpers for the pipeline)
  // ─────────────────────────────────────────────────────────────────────────────

  /**
    * Converts `f` to Negation Normal Form.
    * Eliminates ⇒ and ⇔, and pushes negations down to atoms.
    *
    * @param f        The input formula (of sort Prop).
    * @param negated  True when the formula occurs under an odd number of negations.
    */
  def toNNF(f: Expression, negated: Boolean): Expression = f match
    case `top`          => if negated then bot else top
    case `bot`          => if negated then top else bot
    case Neg(g)         => toNNF(g, !negated)
    case And(g, h)      =>
      if negated then or(toNNF(g, true))(toNNF(h, true))
      else and(toNNF(g, false))(toNNF(h, false))
    case Or(g, h)       =>
      if negated then and(toNNF(g, true))(toNNF(h, true))
      else or(toNNF(g, false))(toNNF(h, false))
    case Implies(g, h)  => toNNF(or(neg(g))(h), negated)
    case Iff(g, h)      => toNNF(and(implies(g)(h))(implies(h)(g)), negated)
    case Forall(x, inner) =>
      if negated then exists(x, toNNF(inner, true))
      else forall(x, toNNF(inner, false))
    case Exists(x, inner) =>
      if negated then forall(x, toNNF(inner, true))
      else exists(x, toNNF(inner, false))
    case atom => if negated then neg(atom) else atom

  /**
    * Replaces the innermost existential quantifier in `f` by a Skolem term built from a fresh
    * constant applied to the free variables of the existential.  Returns `f` unchanged if there
    * is no existential.
    *
    * This is the *uncertified* rewrite; the certified version (in [[certify_skolem]]) wraps it with
    * the appropriate `RightEpsilon` and `RightSubstEq` proof steps.
    */
  def skolemize(f: Expression, counter: Counter): Expression = {
    def go(f: Expression): Option[Expression] = f match
      case Exists(x, inner) =>
        val freeVars = f.freeVariables.toSeq.sortBy(_.id.name)
        val skId     = Identifier(s"Sk${counter.next()}", 0)
        val skSort   = freeVars.foldRight(Ind: Sort)((v, s) => v.sort -> s)
        val sk       = Constant(skId, skSort)
        val skTerm   = freeVars.foldLeft(sk: Expression)((acc, v) => acc(v))
        Some(substituteVariables(inner, Map(x -> skTerm)))
      case Forall(x, inner) =>
        go(inner).map(inner2 => forall(x, inner2))
      case And(g, h)  =>
        go(g).map(and(_)(h)).orElse(go(h).map(and(g)(_)))
      case Or(g, h)   =>
        go(g).map(or(_)(h)).orElse(go(h).map(or(g)(_)))
      case Neg(g)     => go(g).map(neg(_))
      case _          => None
    var cur = f
    var progress = true
    while progress do
      go(cur) match
        case Some(f2) => cur = f2
        case None     => progress = false
    cur
  }

  /** Returns `true` if `f` is a first-order literal (an atom or its negation). */
  def isLiteral(f: Expression): Boolean = f match
    case Neg(g) => isAtom(g)
    case _      => isAtom(f)

  /** Returns `true` if `f` is an atomic formula (no logical connective). */
  def isAtom(f: Expression): Boolean = f match
    case `top` | `bot` => true
    case Neg(_) | And(_, _) | Or(_, _) | Implies(_, _) | Iff(_, _) | Forall(_, _) | Exists(_, _) => false
    case _ => f.sort == Prop

  /** Returns `true` if `f` is a clause (a disjunction of literals, or a single literal). */
  def isClause(f: Expression): Boolean = f match
    case Or(g, h) => isClause(g) && isClause(h)
    case other    => isLiteral(other)

  /** Collects the literals of a clause into a flat sequence.  Precondition: `isClause(f)`. */
  def clauseLiterals(f: Expression): Seq[Expression] = f match
    case Or(g, h) => clauseLiterals(g) ++ clauseLiterals(h)
    case lit      => Seq(lit)

  /** Collects the top-level conjuncts of `f` into a flat sequence. */
  def conjuncts(f: Expression): Seq[Expression] = f match
    case And(g, h) => conjuncts(g) ++ conjuncts(h)
    case other     => Seq(other)

  /**
    * Instantiates all leading universal quantifiers of `f` with fresh free variables.
    * Returns the open matrix and the list of introduced variables (in order).
    */
  def stripUniversals(f: Expression, counter: Counter): (Expression, Seq[Variable]) = {
    def go(f: Expression, acc: Seq[Variable], subst: Map[Variable, Expression]): (Expression, Seq[Variable]) =
      f match
        case Forall(x, inner) =>
          val fresh = Variable(Identifier(s"V${counter.next()}", 0), Ind)
          go(substituteVariables(inner, subst + (x -> fresh)), acc :+ fresh, subst)
        case other =>
          (substituteVariables(other, subst), acc)
    go(f, Seq.empty, Map.empty)
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Counter helper
  // ─────────────────────────────────────────────────────────────────────────────

  /** A mutable integer counter for generating globally fresh names within one clausification run. */
  class Counter(var value: Int = 0) {
    def next(): Int = { val v = value; value += 1; v }
  }
}
