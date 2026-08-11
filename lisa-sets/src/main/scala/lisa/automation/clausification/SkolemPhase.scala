package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Skolemization: remove every `∃` by replacing its witness with a term over the universals it depends on, so
 * the matrix handed to [[PrenexPhase]] is purely universal.
 *
 * '''Why via Hilbert `ε` and not a fresh function symbol.''' A certified phase cannot simply invent a Skolem
 * function — that changes the signature, and no kernel rule licenses it. What the kernel *does* have is
 * [[lisa.maths.Quantifiers.existsEpsilonIff]], `(∃x. P(x)) ⇔ P(ε(λx. P(x)))`, which makes `ε(λx.φ)` a
 * *provably adequate* witness with no new symbol at all. [[skolemizeOne]] instantiates it at `P := λx.φ` and
 * lifts the equivalence under the enclosing binders with `RightSubstIff`. The uncertified [[UncertifiedClausifier]],
 * needing only equisatisfiability, mints ordinary fresh Skolem functions instead.
 *
 * '''Why each ε is then hidden behind a fresh `F(x̄)`.''' The ε-term contains the whole subformula, so a second
 * Skolemization step over it would nest one ε inside the next and square the term size — exponential over a
 * chain of existentials. Each step therefore abstracts its witness to a fresh Skolem-function schema variable
 * `F(x̄)`, carries the *defining equality* `∀x̄. ε(λx.φ) = F(x̄)` as an assumption, and threads the abstracted
 * form onward, so ε-terms neither nest nor grow. The assumptions are discharged latest-first at the end by
 * instantiating `F := λx̄. ε(λx.φ)` — which makes each equality reflexive — plus [[proveQuantifiedReflEq]] and a
 * `Cut`. Latest-first because a later `F`'s value may mention an earlier one.
 *
 * Every `F` is added to the problem's `frozen` set: downstream must treat it as an uninterpreted constant. A
 * nullary `F` is an `Ind`-sorted free variable and [[PrenexPhase]] would otherwise ∀-close it as a clause
 * variable, which is exactly what a Skolem constant must not be.
 *
 * The ε-terms survive into the clause set, where they are not first-order; the prover never sees one, because
 * [[lisa.automation.superposition.Clausal]] abstracts them again on the way in and instantiates them back at
 * the end.
 */
private[clausification] object SkolemPhase:

  /** Certified Skolemization, mirroring [[CertifiedClausifier.certifyNaming]]'s structure: iterate
    * [[skolemizeOne]] over each hypothesis to a fixpoint, threading the **ε-abstracted** form (each witness
    * `ε(λx.φ)` replaced by a fresh Skolem-function schema variable `F(x̄)`), so ε-terms never nest and never blow
    * up. Each step's fresh `F` carries a *defining equality* `∀x̄. ε(λx.φ) = F(x̄)` as an assumption; these are
    * gathered into one outer [[ClausificationSubproof]] and discharged latest-first by instantiating
    * `F := λx̄. ε(λx.φ)` (making the equality reflexive) + a reflexive-equality proof + `Cut`. */
  def certifySkolem(problem: Problem, prover: ClausificationProver): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifySkolem expects a conjecture-free problem (consumed by certifyNegated)")
    val counter = Counter()
    val n = problem.hypotheses.size
    val L = libImports.size
    val outerImports: IndexedSeq[Sequent] = problem.hypotheses.toIndexedSeq ++ libImports

    // Per hypothesis: iterate skolemizeOne to a fixpoint, threading the F-abstracted form.
    final case class HypData(idx: Int, hyp: Sequent, steps: IndexedSeq[SkolemStep], skolemized: Expression)
    val allData: IndexedSeq[HypData] = problem.hypotheses.zipWithIndex.map { case (hyp, i) =>
      val buf = scala.collection.mutable.ArrayBuffer.empty[SkolemStep]
      var current = singleRightFormula(hyp, "hypothesis")
      var continue = true
      while continue do
        skolemizeOne(current, counter) match
          case None    => continue = false
          case Some(s) => buf += s; current = s.skoFormula
      HypData(i, hyp, buf.toIndexedSeq, current)
    }.toIndexedSeq

    val flatSteps: IndexedSeq[SkolemStep] = allData.flatMap(_.steps)
    val Q = flatSteps.size
    val defEqs: IndexedSeq[Expression] = flatSteps.map(_.defEq)

    // Downstream problem: the fully-Skolemized hypotheses. Unlike naming, the defining equalities do NOT become
    // downstream hypotheses (Skolem functions are unconstrained — the def is a proof device only). Every fresh Skolem
    // function `F` is added to `frozen`: downstream must treat it as an uninterpreted constant, never ∀-close it
    // (a nullary `F` is an Ind-sorted free variable and would otherwise be mistaken for a clause variable).
    val newProblem = Problem(allData.map(hd => () |- hd.skolemized).toList, None, problem.frozen ++ flatSteps.map(_.fVar))

    // Inner imports:  [0..n-1] original hyps ; [n..n+L-1] lib ; [n+L..n+L+Q-1] defining equalities (assumptions)
    val innerImports: IndexedSeq[Sequent] = problem.hypotheses.toIndexedSeq ++ libImports ++ defEqs.map(d => () |- d)
    def innerHypRef(i: Int): Int = -(i + 1)
    def innerLibRef(k: Int): Int = -(n + k + 1)
    def innerDefRef(j: Int): Int = -(n + L + j + 1)

    val innerSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val skoRefs = scala.collection.mutable.ArrayBuffer.empty[Int] // ref proving `() ⊢ skolemized_i`
    var jBase = 0
    for hd <- allData do
      var prevRef = innerHypRef(hd.idx)
      var prevFormula: Expression = singleRightFormula(hd.hyp, "hypothesis")
      if hd.steps.isEmpty then skoRefs += prevRef
      else
        for k <- hd.steps.indices do
          val st = hd.steps(k)
          // bridge imports = [existsEpsilonIff, () ⊢ defEq]; supplied from lib slot + this step's def slot.
          innerSteps += KernelStep(SCSubproof(st.bridge, IndexedSeq(innerLibRef(libExistsEpsilonIffIdx), innerDefRef(jBase + k))))
          val bridgeRef = innerSteps.size - 1
          innerSteps += KernelStep(Cut(() |- st.skoFormula, prevRef, bridgeRef, prevFormula))
          prevRef = innerSteps.size - 1
          prevFormula = st.skoFormula
        skoRefs += prevRef
        jBase += hd.steps.size

    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    val recPremises: IndexedSeq[Int] = skoRefs.toIndexedSeq ++ (0 until L).map(innerLibRef)
    innerSteps += ClausificationSubproof(downstream, recPremises)
    val innerProof = ClausificationProof(innerSteps.toIndexedSeq, innerImports)

    // ── Outer: one csub carrying the Q defining equalities as assumptions, discharged latest-first
    //    (F := λx̄. ε(λx.φ) makes each `∀x̄. ε = (λx̄.ε)(x̄)` β-reduce to `ε=ε`; see dischargeAssumptionsLatestFirst). ──
    val csubPremises: IndexedSeq[Int] = negRange(0, n) ++ negRange(n, L)
    val assumptions: IndexedSeq[Assumption] = (0 until Q).toIndexedSeq.map(j => Assumption(defEqs(j), n + L + j))
    val csub = ClausificationSubproof(innerProof, csubPremises, assumptions)

    dischargeAssumptionsLatestFirst(csub, Q, outerImports, { j =>
      val st = flatSteps(j)
      (Map(st.fVar -> NamingSupport.lambdifyAll(st.epsWitness, st.freeVars)), // F := λx̄. ε(λx.φ)
       defEqs(j),
       proveQuantifiedReflEq(st.epsWitness, st.freeVars))
    })

  /** Closed proof of `() ⊢ ∀x̄. (t = t)` — discharges a defining equality after [[InstSchema]] makes it reflexive.
    * The equality twin of [[NamingSupport.proveQuantifiedReflIff]] (`RightRefl` instead of `RightImplies`/`RightIff`). */
  def proveQuantifiedReflEq(t: Expression, freeVars: Seq[Variable]): SCProof =
    val n = freeVars.size
    val steps = new Array[SCProofStep](1 + n)
    val eq = equality(t)(t)
    steps(0) = RightRefl(() |- eq, eq)
    var body: Expression = eq
    var ref = 0
    for (k <- 0 until n) {
      val v = freeVars(n - 1 - k)
      val phi = body
      body = forall(Lambda(v, body))
      steps(1 + k) = RightForall(() |- body, ref, phi, v)
      ref = 1 + k
    }
    SCProof(steps.toIndexedSeq, IndexedSeq.empty)

  /**
    * Result of one Skolemization step.
    *
    *   - `skoFormula` : the input formula with the leftmost outermost `∃x.φ` replaced by `φ[F(x̄)/x]`, where `F` is a
    *                    **fresh Skolem-function schema variable** applied to the enclosing universals `x̄` the witness
    *                    depends on (binding order). Opaque and shared: threaded to the next pass so ε-terms never nest.
    *   - `freeVars`   : `x̄`.
    *   - `fVar`       : `F`.
    *   - `epsWitness` : the Hilbert witness `ε(λx.φ)` that `F` abbreviates, in terms of `x̄`.
    *   - `defEq`      : the defining equality `∀x̄. ε(λx.φ) = F(x̄)` (an assumption discharged at reconstruction).
    *   - `bridge`     : SC proof `f ⊢ skoFormula`, with two imports: [[existsEpsilonIffStatement]] and `() ⊢ defEq`.
    */
  case class SkolemStep(
      skoFormula: Expression,
      freeVars: Seq[Variable],
      fVar: Variable,
      epsWitness: Expression,
      defEq: Expression,
      bridge: SCProof
  )

  /**
    * Single-step Skolemization with bridge proof. Pops the leftmost outermost `∃x.φ` reachable through `∀`/`∧`/`∨`,
    * replaces it by the Hilbert-epsilon witness, then **abstracts** that witness to a fresh Skolem function `F(x̄)`
    * (see [[SkolemStep]]). The bridge derives `f ⊢ skoFormula` in a constant number of steps: instantiate
    * [[Quantifiers.existsEpsilonIff]] at `P := λx.φ` for the local equivalence, lift it via `RightSubstIff`, then
    * swap `ε(λx.φ)` for `F(x̄)` via `RightSubstEq` against the imported defining equality (cut in at the end).
    *
    * Returns `None` if `f` contains no existential under the supported connectives.
    */
  def skolemizeOne(f: Expression, counter: Counter): Option[SkolemStep] = {
    checkInterrupted()
    case class Hit(phi_body: Expression, x: Variable, inner: Expression, p: Variable, enclosing: Seq[Variable])

    def descend(e: Expression, enclosing: Seq[Variable]): Option[Hit] =
      def bin(g: Expression, h0: Expression, op: (Expression, Expression) => Expression): Option[Hit] =
        descend(g, enclosing).map(h => h.copy(phi_body = op(h.phi_body, h0)))
          .orElse(descend(h0, enclosing).map(h => h.copy(phi_body = op(g, h.phi_body))))
      e match
        case Exists(x, inner) =>
          val pSort = enclosing.foldRight(Prop: Sort)((b, acc) => b.sort >>: acc)
          val p     = Variable(Identifier(GeneratedNames.hole, counter.next()), pSort)
          val pApp  = enclosing.foldLeft(p: Expression)(_(_))
          Some(Hit(pApp, x, inner, p, enclosing))
        case Forall(y, body) =>
          descend(body, enclosing :+ y).map(h => h.copy(phi_body = forall(Lambda(y, h.phi_body))))
        case And(g, h0) => bin(g, h0, and(_)(_))
        case Or(g, h0)  => bin(g, h0, or(_)(_))
        case _          => None // In NNF, `Neg` only wraps atoms, so no existential reaches here.

    descend(f, Seq.empty).map { h =>
      // Fresh witnesses u_i (one per enclosing binder), distinct from every name in `f`.
      val taken = scala.collection.mutable.Set.empty[Identifier] ++ f.freeVariables.map(_.id)
      val us = h.enclosing.map { b =>
        val id = freshId(taken, Identifier(GeneratedNames.skolemBound, 0)); taken += id; Variable(id, b.sort)
      }
      // `toMap` keeps the LAST binding, so a shadowed `∀X…∀X` maps X to its innermost (truly-binding) `u`.
      val renaming: Map[Variable, Expression] = h.enclosing.zip(us).toMap
      val uToB: Map[Variable, Expression]      = us.zip(h.enclosing).toMap

      // α-rename x if it clashes with an enclosing binder (else the `renaming` above would rewrite its bound
      // occurrences too, desynchronising the reconstructed RightSubstIff context — kernel-invalid).
      val (xVar, innerX) =
        if h.enclosing.contains(h.x) then
          val xf = Variable(freshId(taken ++ h.enclosing.iterator.map(_.id), h.x.id), h.x.sort)
          (xf, substituteVariablesOpti(h.inner, Map(h.x -> xf)))
        else (h.x, h.inner)

      // Local quantities in terms of the fresh u_i.
      val innerU       = substituteVariablesOpti(innerX, renaming)
      val lambdaInnerU = Lambda(xVar, innerU)
      val targetU      = exists(lambdaInnerU)
      val epsWitnessU  = epsilon(lambdaInnerU)
      val epsFormU     = substituteVariablesOpti(innerU, Map(xVar -> epsWitnessU))
      val localIff     = targetU <=> epsFormU
      val targetLambda = us.foldRight(targetU: Expression)((u, e) => Lambda(u, e))
      val epsLambda    = us.foldRight(epsFormU: Expression)((u, e) => Lambda(u, e))
      val outerIff     = us.foldRight(localIff: Expression)((u, e) => forall(Lambda(u, e)))

      // ── ε-abstraction: fresh Skolem function `F` over the enclosing universals the witness depends on ──
      val mentionedU = us.filter(u => epsWitnessU.freeVariables.contains(u)) // binding order (us is outermost-first)
      val mentionedB = mentionedU.map(u => uToB(u).asInstanceOf[Variable])
      val fSort      = mentionedU.foldRight(Ind: Sort)((u, acc) => u.sort -> acc)
      val fVar       = Variable(Identifier(GeneratedNames.skolemFun, counter.next()), fSort) // schema var; discharged via InstSchema
      val fAppU      = mentionedU.foldLeft(fVar: Expression)((acc, u) => acc(u))
      val qMarker    = Variable(Identifier(GeneratedNames.hole, counter.next()), fSort) // RightSubstEq context marker
      val qAppU      = mentionedU.foldLeft(qMarker: Expression)((acc, u) => acc(u))

      // Fill the ∃-witness in `phi_body` with `w` (in terms of u), β-normalise + η-expand — used identically for the
      // ε-, F- and marker-forms, so ε/F/marker land at the same positions with the same surrounding binder names.
      def fill(w: Expression): Expression =
        val wLambda = us.foldRight(substituteVariablesOpti(innerU, Map(xVar -> w)): Expression)((u, e) => Lambda(u, e))
        etaExpandQuantifiers(substituteVariablesOpti(h.phi_body, Map(h.p -> wLambda)).betaNormalForm)

      val skoFormulaEps = fill(epsWitnessU) // ε-form
      val skoFormulaF   = fill(fAppU)       // F-form (threaded onward)
      val ctxBody       = fill(qAppU)       // marker form (RightSubstEq context body)

      // In terms of the ORIGINAL binders b̄ (as they appear after β in the forms above).
      val epsWitnessB = substituteVariablesOpti(epsWitnessU, uToB)
      val fAppB       = mentionedB.foldLeft(fVar: Expression)((acc, b) => acc(b))
      val sLambda     = mentionedB.foldRight(epsWitnessB: Expression)((b, e) => Lambda(b, e)) // λx̄. ε
      val tLambda     = mentionedB.foldRight(fAppB: Expression)((b, e) => Lambda(b, e))       // λx̄. F(x̄)
      val defEq       = mentionedB.foldRight(equality(epsWitnessB)(fAppB): Expression)((b, e) => forall(Lambda(b, e)))

      // ── bridge: f ⊢ skoFormulaF ; imports [existsEpsilonIff (-1), () ⊢ defEq (-2)] ──
      val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
      steps += InstSchema(() |- localIff, -1, Map(schemaP -> lambdaInnerU)) // 0: () ⊢ localIff
      var current: Expression = localIff
      var ref = 0
      for (i <- us.indices.reverse) {
        val u = us(i); val wrapped = forall(Lambda(u, current))
        steps += RightForall(() |- wrapped, ref, current, u); ref = steps.size - 1; current = wrapped
      }
      val outerIffRef = ref
      steps += Hypothesis(f |- f, f)
      val hypRef = steps.size - 1
      steps += RightSubstIff(Sequent(Set(f, outerIff), Set(skoFormulaEps)), hypRef, Seq((targetLambda, epsLambda)), (Seq(h.p), h.phi_body))
      val substRef = steps.size - 1
      steps += Cut(f |- skoFormulaEps, outerIffRef, substRef, outerIff)
      val epsFormRef = steps.size - 1
      // swap ε → F(x̄) via the defining equality, then cut the defining equality (imported at -2).
      steps += RightSubstEq(Sequent(Set(f, defEq), Set(skoFormulaF)), epsFormRef, Seq((sLambda, tLambda)), (Seq(qMarker), ctxBody))
      val subEqRef = steps.size - 1
      steps += Restate(() |- defEq, -2)
      val defEqRef = steps.size - 1
      steps += Cut(f |- skoFormulaF, defEqRef, subEqRef, defEq)

      SkolemStep(skoFormulaF, mentionedB, fVar, epsWitnessB, defEq,
        SCProof(steps.toIndexedSeq, IndexedSeq(existsEpsilonIffStatement, () |- defEq)))
    }
  }
