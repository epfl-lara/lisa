package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * A **certified** version of the uncertified (Vampire-style) clausifier: it performs the same selective definitional
 * naming as [[UncertifiedClausifier]], but *before* NNF and *producing a kernel proof*, then hands the remaining work to
 * the existing certified phases. The composition is
 *
 *   `certifyScreen → certifyNegated → certifyNaming → certifyNnf → certifySkolem → certifyPrenex → certifyDistribute → prover`
 *
 * so all of NNF (`Restate`), Skolemization (ε via `existsEpsilonIff`) and prenexing are reused unchanged, and the
 * final CNF conversion is ordinary distributivity ([[DistributePhase]]) — exactly like [[UncertifiedClausifier]]. The only
 * new phase is [[certifyNaming]]:
 *
 *  - It replaces a blow-up subformula `subst(x̄)` by a fresh **predicate variable** application `d(x̄)` using a
 *    higher-order [[RightSubstIff]] (the same under-binder machinery [[SkolemPhase.skolemizeOne]] uses for ε),
 *    justified by the definition `∀x̄. d(x̄) ⇔ subst`.
 *  - The definition is added as a fresh hypothesis (clausified by the downstream phases) and carried as a
 *    [[ClausificationSubproof]] *assumption*; at the very end every such assumption is discharged by
 *    `InstSchema(d := λx̄. subst)` + a reflexive-iff proof ([[NamingSupport.proveQuantifiedReflIff]]) + `Cut`.
 *    Instantiating a schema predicate to a (possibly quantified) formula is sound by `InstSchema`.
 *
 * Because the whole thing is kernel-checked, it is a **sound oracle** for the uncertified clausification (it cannot
 * silently produce an unsatisfiable clause set from a satisfiable problem, unlike the uncertified path).
 */
object CertifiedClausifier:

  /** Run the full certified clausification pipeline (screen → selective **naming** → NNF → Skolem → Prenex →
    * distribute) and then call the clausal prover. This is *the* certified clausifier: the `certifyNaming` step
    * (Vampire/E-style threshold-gated definitional CNF) caps the CNF blow-up before NNF, so nested `⇔`/`∧`/`∨` stay
    * polynomial.
    *
    * The caller's names are their own business: [[ScreenPhase]] renames every free input variable into the `v`/`usr`
    * namespaces on the way in and restores the caller's names in the conclusion on the way out, so a goal over a
    * variable named like one of the clausifier's own schemas (`P`, `R`, `esk…`, `nm…`, …) is handled like any other.
    *
    * The returned [[SCProof]] takes, in addition to the user's hypothesis/conjecture imports, the schematic
    * statements of the library theorems ([[libImports]]) as imports, in fixed order at the end of the imports
    * list. A future tactic wrapping this pipeline can discharge them by cutting against the corresponding library
    * theorems.
    *
    * ==Clausal-prover contract (`prover`)==
    * `prover` is called on a conjecture-free clausal [[Problem]] and MUST return an [[SCProof]] such that:
    *  - '''imports''' `== problem.imports` (the clause-sequents), pointwise and in order — the wrapper appends
    *    [[libImports]] and the pipeline asserts `sameImportList` on the result. (Declare every clause even if the
    *    refutation does not use it.)
    *  - '''conclusion''' `== ⊢` (the EMPTY sequent). NOT `{all clause literals} ⊢`: the [[ClausificationSubproof]]
    *    embeds this proof with no assumptions, and [[NegatedPhase.certifyNegated]]'s final `Cut` lifts only the
    *    negated conjecture `¬φ` to the LHS, so it needs `¬φ ⊢` (empty RHS) — i.e. the prover proper must derive `⊢`.
    * ==Clause format the prover receives==
    * Every clause is a [[Sequent]] `a₁, …, aₘ ⊢ b₁, …, bₙ` denoting `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ`: a negative
    * literal is its atom on the LHS, a positive literal sits on the RHS, and the empty sequent is the empty
    * clause (see [[Clausification.clauseSequent]]). No bare disjunctions, no quantifiers, no `¬` at the top of a
    * RHS formula. This is the form a first-order prover works in directly, so no per-clause bridging step is
    * needed, and no `∀`-strip or `∨`-split is required. */
  def certifyClausal(problem: Problem, prover: Problem => SCProof, threshold: Int = UncertifiedClausifier.DefaultThreshold): SCProof =
    val wrappedProver: ClausificationProver = p =>
      val downstream = ClausificationProof.fromSCProof(prover(p))
      ClausificationProof(downstream.steps, downstream.imports ++ libImports)
    val distributeProver: ClausificationProver = DistributePhase.certifyDistribute(_, wrappedProver)
    val prenexProver: ClausificationProver = PrenexPhase.certifyPrenex(_, distributeProver)
    val skolemProver: ClausificationProver = SkolemPhase.certifySkolem(_, prenexProver)
    val nnfProver: ClausificationProver = NnfPhase.certifyNnf(_, skolemProver)
    val namingProver: ClausificationProver = certifyNaming(_, nnfProver, threshold)
    val negatedProver: ClausificationProver = NegatedPhase.certifyNegated(_, namingProver)
    val fullProver: ClausificationProver = ScreenPhase.certifyScreen(_, negatedProver)
    lowerClausificationProof(fullProver(problem))

  // ── one naming step ──────────────────────────────────────────────────────────────────────────

  /** One naming step on `f`: the leftmost blow-up subformula `subst` (reachable through `∀/∃/∧/∨/¬`) replaced by
   *  a fresh predicate application `tsApp = d(x̄)`, together with the bridge proof `f ⊢ named` (which takes the
   *  quantified definition `∀x̄. d(x̄) ⇔ subst` as its single import). `None` if nothing is worth naming. */
  final case class NamingStep(
      named: Expression, //          f with `subst` replaced by `nmApp`
      nm: Variable, //               the fresh naming predicate variable (`GeneratedNames.namingAtom`)
      freeVars: Seq[Variable], //    x̄ (the Ind free variables of `subst`)
      nmApp: Expression, //          d(x̄)
      subst: Expression, //          the named subformula
      pol: Int, //                   the polarity `subst` occurs at (+1 / -1 / 0 under `⇔`)
      bridge: SCProof //             conclusion `f ⊢ named`, one import `() ⊢ quantified`
  ):
    /** The full definition `∀x̄. subst ⇔ d(x̄)`. Used as the *assumption* the bridge rewrites with and that the
      * final discharge instantiates — both need the biconditional. */
    def quantified: Expression = NamingSupport.quantifyAll(subst <=> nmApp, freeVars)

    /** The definition handed to the **downstream phases**, i.e. the one that gets clausified: only the half
      * the site's polarity actually uses (Plaisted–Greenbaum), matching `UncertifiedClausifier.define`.
      *
      * '''Emitting the full `⇔` here would defeat the whole phase.''' The naming threshold bounds the clause
      * count only in the direction the polarity uses; the opposite half is unbounded, so on exactly the shapes
      * naming exists to tame it distributes into exponentially many clauses. Keeping the `⇔` for the bridge and
      * the discharge costs nothing — neither is clausified. */
    def directional: Expression =
      val body =
        if pol > 0 then implies(nmApp)(subst) //      positive occurrence: d ⇒ subst
        else if pol < 0 then implies(subst)(nmApp) // negative occurrence: subst ⇒ d
        else subst <=> nmApp //                       both (under `⇔`): the full definition
      NamingSupport.quantifyAll(body, freeVars)

  // `Est` / `capMul` / `capAdd` (the capped clause-count arithmetic) are shared with UncertifiedClausifier — see `Clausification`.

  /** Pure positive/negative clause-count estimate, matching UncertifiedClausifier.name's bottom-up `Est` combination. Any
   *  atom — including a naming atom already substituted in a previous step — counts as `Est(1, 1)`. */
  private def estimate(f: Expression): Est = f match
    case And(g, h)     => val eg = estimate(g); val eh = estimate(h); Est(capAdd(eg.pos, eh.pos), capMul(eg.neg, eh.neg))
    case Or(g, h)      => val eg = estimate(g); val eh = estimate(h); Est(capMul(eg.pos, eh.pos), capAdd(eg.neg, eh.neg))
    case Neg(g)        => val e = estimate(g); Est(e.neg, e.pos)
    case Implies(g, h) => val eg = estimate(g); val eh = estimate(h); Est(capMul(eg.neg, eh.pos), capAdd(eg.pos, eh.neg))
    case Iff(g, h)     => val eg = estimate(g); val eh = estimate(h)
                          Est(capAdd(capMul(eg.pos, eh.neg), capMul(eg.neg, eh.pos)), capAdd(capMul(eg.pos, eh.pos), capMul(eg.neg, eh.neg)))
    case Forall(_, g)  => estimate(g)
    case Exists(_, g)  => estimate(g)
    case `top`         => Est(0, 1)
    case `bot`         => Est(1, 0)
    case _             => Est(1, 1)

  /** Recursively rewrite `g ⇒ h` to `¬g ∨ h`, exactly as UncertifiedClausifier.name does, so the named formula matches. */
  def eliminateImplies(f: Expression): Expression = f match
    case Implies(g, h) => or(neg(eliminateImplies(g)))(eliminateImplies(h))
    case And(g, h)     => and(eliminateImplies(g))(eliminateImplies(h))
    case Or(g, h)      => or(eliminateImplies(g))(eliminateImplies(h))
    case Neg(g)        => neg(eliminateImplies(g))
    case Iff(g, h)     => eliminateImplies(g) <=> eliminateImplies(h)
    case Forall(x, g)  => forall(Lambda(x, eliminateImplies(g)))
    case Exists(x, g)  => exists(Lambda(x, eliminateImplies(g)))
    case _             => f

  /** The subformula UncertifiedClausifier.name names *next*, plus the `RightSubstIff` context to certify it and the
    * polarity it occurs at — which decides which half of the definition the downstream phases get (see
    * [[NamingStep.directional]]). */
  private final case class Site(subst: Expression, phiBody: Expression, p: Variable, pol: Int)

  /** Find the subformula UncertifiedClausifier.name names next on the (Implies-free) `f`: the larger child of the
   *  deepest-leftmost multiplicative node whose estimate exceeds `threshold`, post-order (so inner sites are
   *  named first, matching UncertifiedClausifier's bottom-up pass). `rebuild(hole)` reconstructs `f` with `hole` in place. */
  private def findSite(f: Expression, pol: Int, threshold: Int, markers: Counter, frozen: Set[Variable]): Option[Site] =
    // `sitePol` is the polarity of `child` itself, which is the enclosing node's polarity for `∧`/`∨` and 0
    // under `⇔` — the same value the gate above each call site tested.
    def mk(child: Expression, sitePol: Int, rebuild: Expression => Expression): Site =
      // Marker `p` over the same variables the naming atom will abstract — [[NamingSupport.namingVars]] is the one
      // definition of that list, so `p` and `nm` cannot drift apart and the `p -> nm` substitution in [[nameOne]]
      // stays well-sorted by construction.
      val xs = NamingSupport.namingVars(child, frozen)
      val pSort = xs.foldRight(Prop: Sort)((v, acc) => v.sort >>: acc)
      val p = Variable(Identifier(GeneratedNames.hole, markers.next()), pSort)
      Site(child, rebuild(xs.foldLeft(p: Expression)(_(_))), p, sitePol)
    def go(f: Expression, pol: Int, rebuild: Expression => Expression): Option[Site] = f match
      case And(g, h) => // pos additive, neg multiplicative
        go(g, pol, hole => rebuild(and(hole)(h))).orElse(go(h, pol, hole => rebuild(and(g)(hole)))).orElse:
          val eg = estimate(g); val eh = estimate(h)
          if pol <= 0 && capMul(eg.neg, eh.neg) > threshold && (eg.neg > 1 || eh.neg > 1) then
            if eg.neg >= eh.neg && eg.neg > 1 then Some(mk(g, pol, hole => rebuild(and(hole)(h))))
            else Some(mk(h, pol, hole => rebuild(and(g)(hole))))
          else None
      case Or(g, h) => // pos multiplicative, neg additive
        go(g, pol, hole => rebuild(or(hole)(h))).orElse(go(h, pol, hole => rebuild(or(g)(hole)))).orElse:
          val eg = estimate(g); val eh = estimate(h)
          if pol >= 0 && capMul(eg.pos, eh.pos) > threshold && (eg.pos > 1 || eh.pos > 1) then
            if eg.pos >= eh.pos && eg.pos > 1 then Some(mk(g, pol, hole => rebuild(or(hole)(h))))
            else Some(mk(h, pol, hole => rebuild(or(g)(hole))))
          else None
      case Neg(g) => go(g, -pol, hole => rebuild(neg(hole)))
      case Iff(g, h) => // children at polarity 0
        go(g, 0, hole => rebuild(hole <=> h)).orElse(go(h, 0, hole => rebuild(g <=> hole))).orElse:
          val eg = estimate(g); val eh = estimate(h)
          val ip = capAdd(capMul(eg.pos, eh.neg), capMul(eg.neg, eh.pos))
          val in = capAdd(capMul(eg.pos, eh.pos), capMul(eg.neg, eh.neg))
          def sz(e: Est) = capAdd(e.pos, e.neg)
          val big = if pol > 0 then ip > threshold else if pol < 0 then in > threshold else ip > threshold || in > threshold
          if big && (sz(eg) > 2 || sz(eh) > 2) then
            if sz(eg) >= sz(eh) && sz(eg) > 2 then Some(mk(g, 0, hole => rebuild(hole <=> h)))
            else Some(mk(h, 0, hole => rebuild(g <=> hole)))
          else None
      case Forall(x, g) => go(g, pol, hole => rebuild(forall(Lambda(x, hole))))
      case Exists(x, g) => go(g, pol, hole => rebuild(exists(Lambda(x, hole))))
      case _            => None
    go(f, pol, identity)

  /** One naming step matching UncertifiedClausifier: name the `findSite` subformula with [[NamingSupport.freshNamingAtom]]
   *  — the *same* generator (and hence the same `nm` atoms) the uncertified [[UncertifiedClausifier]] uses — with the bridge
   *  `f ⊢ named` (via HO `RightSubstIff`, import `() ⊢ ∀x̄. subst ⇔ d(x̄)`). `f` must be Implies-free. */
  def nameOne(f: Expression, counter: Counter, threshold: Int, markers: Counter, frozen: Set[Variable]): Option[NamingStep] =
    checkInterrupted()
    findSite(f, 1, threshold, markers, frozen).map { site =>
      val (nm, freeVars, nmApp) = NamingSupport.freshNamingAtom(site.subst, counter, frozen) // == namingVars(subst, frozen)
      val substLambda = NamingSupport.lambdifyAll(site.subst, freeVars)
      val nmAppLambda = NamingSupport.lambdifyAll(nmApp, freeVars)
      val quantified = NamingSupport.quantifyAll(site.subst <=> nmApp, freeVars)
      // `p` and `nm` have the same sort (both over x̄) and both occur applied to x̄, so a *direct* p→nm
      // substitution gives `nmApp` at the marker while leaving the rest structurally untouched (no β/η, so bound
      // variable names are preserved) — matching UncertifiedClausifier's plain structural naming exactly.
      val named = substituteVariablesOpti(site.phiBody, Map(site.p -> nm))
      val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
      steps += Hypothesis(f |- f, f)
      steps += RightSubstIff(Sequent(Set(f, quantified), Set(named)), 0, Seq((substLambda, nmAppLambda)), (Seq(site.p), site.phiBody))
      steps += Restate(() |- quantified, -1)
      steps += Cut(f |- named, 2, 1, quantified)
      NamingStep(named, nm, freeVars, nmApp, site.subst, site.pol, SCProof(steps.toIndexedSeq, IndexedSeq(() |- quantified)))
    }

  // ── oracles for the uncertified/certified equivalence test ─────────────────────────────────────
  //
  // Everything from here to the end of this block exists only for `ClausifierEquivalenceTest`, which
  // checks that the certified pipeline names and Skolemizes the same way the uncertified [[UncertifiedClausifier]]
  // does. Nothing in the pipeline calls any of it — `certifyClausal` and the phase entry points are the API.
  // `private[clausification]` says so to the compiler, so a reader can tell this object's real surface from
  // its test scaffolding, and so the members stop appearing in the library's public API.

  /** The certified path's named formula (⇒ eliminated, then `nameOne` to a fixpoint) — should equal
   *  [[UncertifiedClausifier.namedFormula]] *identically* (both mint `nm` atoms via the same generator). */
  private[clausification] def namedFormula(phi: Expression, threshold: Int): Expression =
    val counter = Counter(); val markers = Counter()
    var current = eliminateImplies(phi)
    var continue = true
    while continue do nameOne(current, counter, threshold, markers, Set.empty) match { case None => continue = false; case Some(s) => current = s.named }
    current

  /** The certified Skolemization of an NNF formula: iterate [[SkolemPhase.skolemizeOne]], which already abstracts
   *  each witness to an opaque shared Skolem function `esk(x̄)` per pass (so ε-terms never nest or blow up), leaving
   *  `∀` in place (the certified pipeline strips them in prenex). */
  private[clausification] def skolemizeEps(nnf: Expression, counter: Counter): Expression =
    var current = nnf; var continue = true
    while continue do SkolemPhase.skolemizeOne(current, counter) match { case None => continue = false; case Some(s) => current = s.skoFormula }
    current

  /** Drop every `∀`, **α-renaming** its bound variable to a fresh clause variable, to align with UncertifiedClausifier's
   *  Skolemization (which renames when it strips) and the certified pipeline's prenex phase. Without the rename,
   *  shadowed `∀X … ∀X` binders would collapse into one free `X`, spuriously diverging from UncertifiedClausifier's
   *  distinct clause variables (`w`). After [[skolemizeEps]] no `∃` remain, so only `∀` is dropped. */
  private[clausification] def stripForall(f: Expression): Expression =
    val counter = Counter()
    def rec(f: Expression): Expression = f match
      case Forall(x, g) => rec(substituteVariablesOpti(g, Map(x -> Variable(Identifier(GeneratedNames.clauseVar, counter.next()), x.sort))))
      case And(g, h)    => and(rec(g))(rec(h))
      case Or(g, h)     => or(rec(g))(rec(h))
      case Neg(g)       => neg(rec(g))
      case _            => f
    rec(f)

  /** The named formula through NNF and certified (ε-)Skolemization — the raw ε-form, `∀` still present. The
   *  after-Skolem equivalence test ε-abstracts it (over the *original* names, so Skolem arguments line up with
   *  UncertifiedClausifier's) and only then [[stripForall]]s. */
  private[clausification] def namedNnfSkolemEps(phi: Expression, threshold: Int = UncertifiedClausifier.DefaultThreshold): Expression =
    skolemizeEps(NnfPhase.toNNF(namedFormula(phi, threshold), negated = false), Counter())

  /** UncertifiedClausifier's "after Skolem" result for `phi` (∃ → Skolem functions, ∀ stripped) — routed here so the
   *  package-private [[UncertifiedClausifier]] is reachable from the equivalence test. */
  private[clausification] def uncertifiedNamedNnfSkolem(phi: Expression, threshold: Int = UncertifiedClausifier.DefaultThreshold): Expression =
    UncertifiedClausifier.namedNnfSkolem(phi, threshold)

  /** `true` iff UncertifiedClausifier and the certified path name the same subformulas. Both paths mint their naming atoms
   *  with the *same* generator ([[NamingSupport.freshNamingAtom]] → `nm`, same counter progression), so equivalent
   *  naming yields *identical* formulas — a plain structural `==`, no up-to-renaming canonicalization needed. */
  private[clausification] def sameNaming(phi: Expression, threshold: Int = UncertifiedClausifier.DefaultThreshold): Boolean =
    UncertifiedClausifier.namedFormula(phi, threshold, Counter()) == namedFormula(phi, threshold)

  // ── the naming phase ───────────────────────────────────────────────────────────────────────────

  /** Selective definitional naming, before NNF, producing a [[ClausificationProof]]. Names arbitrary
   *  (possibly quantified) subformulas via [[nameOne]] and delegates definition clausification to the
   *  downstream phases; each definition is discharged latest-first (see [[NamingSupport.proveQuantifiedReflIff]]). */
  def certifyNaming(problem: Problem, prover: ClausificationProver, threshold: Int): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifyNaming expects a conjecture-free problem")
    val counter = Counter()
    val n = problem.hypotheses.size
    val L = libImports.size
    val outerImports: IndexedSeq[Sequent] = problem.hypotheses.toIndexedSeq ++ libImports

    // Fresh counter for internal proof markers only, so `counter` (naming atoms) advances exactly as UncertifiedClausifier.
    val markers = Counter()
    // Per-hypothesis: eliminate `⇒`, then iterate nameOne to a fixpoint — mirroring UncertifiedClausifier.name.
    final case class HypData(idx: Int, hyp: Sequent, phiElim: Expression, steps: IndexedSeq[NamingStep], named: Expression)
    val allData: IndexedSeq[HypData] = problem.hypotheses.zipWithIndex.map { case (hyp, i) =>
      val phiElim = eliminateImplies(singleRightFormula(hyp, "hypothesis"))
      val buf = scala.collection.mutable.ArrayBuffer.empty[NamingStep]
      var current = phiElim
      var continue = true
      while continue do
        nameOne(current, counter, threshold, markers, problem.frozen) match
          case None    => continue = false
          case Some(s) => buf += s; current = s.named
      HypData(i, hyp, phiElim, buf.toIndexedSeq, current)
    }.toIndexedSeq

    val flatSteps: IndexedSeq[NamingStep] = allData.flatMap(_.steps)
    val Q = flatSteps.size
    val quantifieds: IndexedSeq[Expression] = flatSteps.map(_.quantified)

    // Downstream problem: the named hypotheses, then one hypothesis per definition. The definitions go down as
    // their *directional* half (see `NamingStep.directional`) — the biconditional stays behind as the
    // assumption, which is not clausified.
    val directionals: IndexedSeq[Expression] = flatSteps.map(_.directional)
    val namedHyps: IndexedSeq[Sequent] = allData.map(hd => () |- hd.named)
    val defHyps: IndexedSeq[Sequent] = directionals.map(d => () |- d)
    val newProblem = Problem((namedHyps ++ defHyps).toList, None, problem.frozen)

    // ── Inner proof: derive each named hypothesis from its original + its own naming steps' definitions. ──
    // Inner imports:  [0..n-1] original hyps ; [n..n+L-1] lib ; [n+L..n+L+Q-1] definitions (assumptions)
    val innerImports: IndexedSeq[Sequent] = problem.hypotheses.toIndexedSeq ++ libImports ++ quantifieds.map(q => () |- q)
    def innerHypRef(i: Int): Int = -(i + 1)
    def innerLibRef(k: Int): Int = -(n + k + 1)
    def innerDefRef(j: Int): Int = -(n + L + j + 1)

    val innerSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val namedRefs = scala.collection.mutable.ArrayBuffer.empty[Int] // ref proving `() ⊢ named_i` (per hyp)
    var jBase = 0
    for hd <- allData do
      // Start from `() ⊢ φ`; bridge to `() ⊢ eliminateImplies(φ)` by one Restate (propositional equivalence), then
      // chain the per-step naming bridges (each `prev ⊢ next` via its definition, Cut in `() ⊢ prev`).
      var prevRef = innerHypRef(hd.idx)
      var prevFormula: Expression = singleRightFormula(hd.hyp, "hypothesis")
      if hd.phiElim != prevFormula then
        innerSteps += KernelStep(Restate(() |- hd.phiElim, prevRef))
        prevRef = innerSteps.size - 1
        prevFormula = hd.phiElim
      if hd.steps.isEmpty then namedRefs += prevRef
      else
        for k <- hd.steps.indices do
          val st = hd.steps(k)
          innerSteps += KernelStep(SCSubproof(st.bridge, IndexedSeq(innerDefRef(jBase + k))))
          val bridgeRef = innerSteps.size - 1
          innerSteps += KernelStep(Cut(() |- st.named, prevRef, bridgeRef, prevFormula))
          prevRef = innerSteps.size - 1
          prevFormula = st.named
        namedRefs += prevRef
        jBase += hd.steps.size

    // Weaken each `⇔` assumption to the directional half the downstream problem declares. One `Weakening` per
    // definition: the kernel's rule is `isImplyingSequent`, an ortholattice *entailment*, and the checker takes
    // `∀x̄.(a ⇔ b) ⊢ ∀x̄.(a ⇒ b)` — it reaches under the binder. At polarity 0 the two coincide and the
    // assumption import is cited directly.
    val defRefs: IndexedSeq[Int] = (0 until Q).map { j =>
      if directionals(j) == quantifieds(j) then innerDefRef(j)
      else
        innerSteps += KernelStep(Weakening(() |- directionals(j), innerDefRef(j)))
        innerSteps.size - 1
    }

    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    // Downstream imports: [named_0..named_{n-1}, def_0..def_{Q-1}] ++ lib.
    val recPremises: IndexedSeq[Int] = namedRefs.toIndexedSeq ++ defRefs ++ (0 until L).map(innerLibRef)
    innerSteps += ClausificationSubproof(downstream, recPremises)
    val innerProof = ClausificationProof(innerSteps.toIndexedSeq, innerImports)

    // ── Outer: one csub carrying the Q definitions as assumptions, discharged latest-first
    //    (d := λx̄. subst makes each `∀x̄. subst ⇔ d(x̄)` reflexive; see dischargeAssumptionsLatestFirst). ──
    val csubPremises: IndexedSeq[Int] = negRange(0, n) ++ negRange(n, L)
    val assumptions: IndexedSeq[Assumption] = (0 until Q).toIndexedSeq.map(j => Assumption(quantifieds(j), n + L + j))
    val csub = ClausificationSubproof(innerProof, csubPremises, assumptions)

    dischargeAssumptionsLatestFirst(csub, Q, outerImports, { j =>
      val st = flatSteps(j)
      (Map(st.nm -> NamingSupport.lambdifyAll(st.subst, st.freeVars)),
       quantifieds(j),
       NamingSupport.proveQuantifiedReflIff(st.subst, st.freeVars))
    })
