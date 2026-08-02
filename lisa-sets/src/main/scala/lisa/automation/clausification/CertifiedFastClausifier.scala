package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * A **certified** version of the fast (Vampire-style) clausifier: it performs the same selective definitional
 * naming as [[FastClausify]], but *before* NNF and *producing a kernel proof*, then hands the remaining work to
 * the existing certified phases. The composition is
 *
 *   `certifyNegated → certifyFastNaming → certifyNnf → certifySkolem → certifyPrenex → certifyDistribute → prover`
 *
 * so all of NNF (`Restate`), Skolemization (ε via `existsEpsilonIff`) and prenexing are reused unchanged, and the
 * final CNF conversion is ordinary distributivity ([[DistributePhase]]) — exactly like [[FastClausify]]. The only
 * new phase is [[certifyFastNaming]]:
 *
 *  - It replaces a blow-up subformula `subst(x̄)` by a fresh **predicate variable** application `d(x̄)` using a
 *    higher-order [[RightSubstIff]] (the same under-binder machinery [[SkolemPhase.skolemizeOne]] uses for ε),
 *    justified by the definition `∀x̄. d(x̄) ⇔ subst`.
 *  - The definition is added as a fresh hypothesis (clausified by the downstream phases) and carried as a
 *    [[ClausificationSubproof]] *assumption*; at the very end every such assumption is discharged by
 *    `InstSchema(d := λx̄. subst)` + a reflexive-iff proof ([[NamingSupport.proveQuantifiedReflIff]]) + `Cut`.
 *    Instantiating a schema predicate to a (possibly quantified) formula is sound by `InstSchema`.
 *
 * Because the whole thing is kernel-checked, it is a **sound oracle** for the fast clausification (it cannot
 * silently produce an unsatisfiable clause set from a satisfiable problem, unlike the uncertified path).
 */
object CertifiedFastClausifier:

  /** Run the full certified clausification pipeline (selective **naming** → NNF → Skolem → Prenex → distribute) and
    * then call the clausal prover. This is *the* certified clausifier: the `certifyFastNaming` step (Vampire/E-style
    * threshold-gated definitional CNF) caps the CNF blow-up before NNF, so nested `⇔`/`∧`/`∨` stay polynomial.
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
    * Every clause is a [[Sequent]] in uniform literal-set form: `Sequent(∅, {literals})` with the literals on the
    * RHS and negatives written `¬A` (no bare disjunctions, no quantifiers). A first-order prover that expects a
    * negative literal's atom on the LHS need only move each `¬A` from the RHS to the LHS as `A`, and bridge each
    * original clause to that working form with a single per-clause `Restate`. No `∀`-strip or `∨`-split is required. */
  def certifyClausal(problem: Problem, prover: Problem => SCProof, threshold: Int = FastClausify.DefaultThreshold): SCProof =
    val wrappedProver: ClausificationProver = p =>
      val downstream = ClausificationProof.fromSCProof(prover(p))
      ClausificationProof(downstream.steps, downstream.imports ++ libImports)
    val distributeProver: ClausificationProver = DistributePhase.certifyDistribute(_, wrappedProver)
    val prenexProver: ClausificationProver = PrenexPhase.certifyPrenex(_, distributeProver)
    val skolemProver: ClausificationProver = SkolemPhase.certifySkolem(_, prenexProver)
    val nnfProver: ClausificationProver = NnfPhase.certifyNnf(_, skolemProver)
    val namingProver: ClausificationProver = certifyFastNaming(_, nnfProver, threshold)
    val renameProver: ClausificationProver = RenamePhase.certifyRename(_, namingProver)
    val fullProver: ClausificationProver = NegatedPhase.certifyNegated(_, renameProver)
    lowerClausificationProof(fullProver(problem))

  // ── one naming step ──────────────────────────────────────────────────────────────────────────

  /** One naming step on `f`: the leftmost blow-up subformula `subst` (reachable through `∀/∃/∧/∨/¬`) replaced by
   *  a fresh predicate application `tsApp = d(x̄)`, together with the bridge proof `f ⊢ named` (which takes the
   *  quantified definition `∀x̄. d(x̄) ⇔ subst` as its single import). `None` if nothing is worth naming. */
  final case class NamingStep(
      named: Expression, //          f with `subst` replaced by `tsApp`
      tsi: Variable, //              the fresh predicate variable
      freeVars: Seq[Variable], //    x̄ (the Ind free variables of `subst`)
      tsApp: Expression, //          d(x̄)
      subst: Expression, //          the named subformula
      bridge: SCProof //             conclusion `f ⊢ named`, one import `() ⊢ quantified`
  ):
    def quantified: Expression = NamingSupport.quantifyAll(subst <=> tsApp, freeVars)

  // `Est` / `capMul` / `capAdd` (the capped clause-count arithmetic) are shared with FastClausify — see `Clausification`.

  /** Pure positive/negative clause-count estimate, matching FastClausify.name's bottom-up `Est` combination. Any
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

  /** Recursively rewrite `g ⇒ h` to `¬g ∨ h`, exactly as FastClausify.name does, so the named formula matches. */
  def eliminateImplies(f: Expression): Expression = f match
    case Implies(g, h) => or(neg(eliminateImplies(g)))(eliminateImplies(h))
    case And(g, h)     => and(eliminateImplies(g))(eliminateImplies(h))
    case Or(g, h)      => or(eliminateImplies(g))(eliminateImplies(h))
    case Neg(g)        => neg(eliminateImplies(g))
    case Iff(g, h)     => eliminateImplies(g) <=> eliminateImplies(h)
    case Forall(x, g)  => forall(Lambda(x, eliminateImplies(g)))
    case Exists(x, g)  => exists(Lambda(x, eliminateImplies(g)))
    case _             => f

  /** The subformula FastClausify.name names *next*, plus the `RightSubstIff` context to certify it. */
  private final case class Site(subst: Expression, phiBody: Expression, p: Variable)

  /** Find the subformula FastClausify.name names next on the (Implies-free) `f`: the larger child of the
   *  deepest-leftmost multiplicative node whose estimate exceeds `threshold`, post-order (so inner sites are
   *  named first, matching FastClausify's bottom-up pass). `rebuild(hole)` reconstructs `f` with `hole` in place. */
  private def findSite(f: Expression, pol: Int, threshold: Int, markers: Counter): Option[Site] =
    def mk(child: Expression, rebuild: Expression => Expression): Site =
      // Marker `p` over the Ind free variables x̄ of `child` (same set/order as freshNamingAtom), applied at the hole.
      val xs = child.freeVariables.toSeq.filter(_.sort == Ind).sortBy(_.id.toString)
      val pSort = xs.foldRight(Prop: Sort)((v, acc) => v.sort >>: acc)
      val p = Variable(Identifier(GeneratedNames.hole, markers.next()), pSort)
      Site(child, rebuild(xs.foldLeft(p: Expression)(_(_))), p)
    def go(f: Expression, pol: Int, rebuild: Expression => Expression): Option[Site] = f match
      case And(g, h) => // pos additive, neg multiplicative
        go(g, pol, hole => rebuild(and(hole)(h))).orElse(go(h, pol, hole => rebuild(and(g)(hole)))).orElse:
          val eg = estimate(g); val eh = estimate(h)
          if pol <= 0 && capMul(eg.neg, eh.neg) > threshold && (eg.neg > 1 || eh.neg > 1) then
            if eg.neg >= eh.neg && eg.neg > 1 then Some(mk(g, hole => rebuild(and(hole)(h))))
            else Some(mk(h, hole => rebuild(and(g)(hole))))
          else None
      case Or(g, h) => // pos multiplicative, neg additive
        go(g, pol, hole => rebuild(or(hole)(h))).orElse(go(h, pol, hole => rebuild(or(g)(hole)))).orElse:
          val eg = estimate(g); val eh = estimate(h)
          if pol >= 0 && capMul(eg.pos, eh.pos) > threshold && (eg.pos > 1 || eh.pos > 1) then
            if eg.pos >= eh.pos && eg.pos > 1 then Some(mk(g, hole => rebuild(or(hole)(h))))
            else Some(mk(h, hole => rebuild(or(g)(hole))))
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
            if sz(eg) >= sz(eh) && sz(eg) > 2 then Some(mk(g, hole => rebuild(hole <=> h)))
            else Some(mk(h, hole => rebuild(g <=> hole)))
          else None
      case Forall(x, g) => go(g, pol, hole => rebuild(forall(Lambda(x, hole))))
      case Exists(x, g) => go(g, pol, hole => rebuild(exists(Lambda(x, hole))))
      case _            => None
    go(f, pol, identity)

  /** One naming step matching FastClausify: name the `findSite` subformula with [[NamingSupport.freshNamingAtom]]
   *  — the *same* generator (and hence the same `nm` atoms) the uncertified [[FastClausify]] uses — with the bridge
   *  `f ⊢ named` (via HO `RightSubstIff`, import `() ⊢ ∀x̄. subst ⇔ d(x̄)`). `f` must be Implies-free. */
  def nameOne(f: Expression, counter: Counter, threshold: Int, markers: Counter): Option[NamingStep] =
    checkInterrupted()
    findSite(f, 1, threshold, markers).map { site =>
      val (tsi, freeVars, tsApp) = NamingSupport.freshNamingAtom(site.subst, counter) // freeVars = site's Ind free vars
      val substLambda = NamingSupport.lambdifyAll(site.subst, freeVars)
      val tsAppLambda = NamingSupport.lambdifyAll(tsApp, freeVars)
      val quantified = NamingSupport.quantifyAll(site.subst <=> tsApp, freeVars)
      // `p` and `tsi` have the same sort (both over x̄) and both occur applied to x̄, so a *direct* p→tsi
      // substitution gives `tsApp` at the marker while leaving the rest structurally untouched (no β/η, so bound
      // variable names are preserved) — matching FastClausify's plain structural naming exactly.
      val named = substituteVariablesOpti(site.phiBody, Map(site.p -> tsi))
      val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
      steps += Hypothesis(f |- f, f)
      steps += RightSubstIff(Sequent(Set(f, quantified), Set(named)), 0, Seq((substLambda, tsAppLambda)), (Seq(site.p), site.phiBody))
      steps += Restate(() |- quantified, -1)
      steps += Cut(f |- named, 2, 1, quantified)
      NamingStep(named, tsi, freeVars, tsApp, site.subst, SCProof(steps.toIndexedSeq, IndexedSeq(() |- quantified)))
    }

  /** The certified path's named formula (⇒ eliminated, then `nameOne` to a fixpoint) — should equal
   *  [[FastClausify.namedFormula]] *identically* (both mint `nm` atoms via the same generator). Exposed for the equivalence test. */
  def namedFormula(phi: Expression, threshold: Int): Expression =
    val counter = Counter(); val markers = Counter()
    var current = eliminateImplies(phi)
    var continue = true
    while continue do nameOne(current, counter, threshold, markers) match { case None => continue = false; case Some(s) => current = s.named }
    current

  /** The certified Skolemization of an NNF formula: iterate [[SkolemPhase.skolemizeOne]], which already abstracts
   *  each witness to an opaque shared Skolem function `esk(x̄)` per pass (so ε-terms never nest or blow up), leaving
   *  `∀` in place (the certified pipeline strips them in prenex). Exposed for the after-Skolem equivalence test. */
  def skolemizeEps(nnf: Expression, counter: Counter): Expression =
    var current = nnf; var continue = true
    while continue do SkolemPhase.skolemizeOne(current, counter) match { case None => continue = false; case Some(s) => current = s.skoFormula }
    current

  /** Drop every `∀`, **α-renaming** its bound variable to a fresh clause variable, to align with FastClausify's
   *  Skolemization (which renames when it strips) and the certified pipeline's prenex phase. Without the rename,
   *  shadowed `∀X … ∀X` binders would collapse into one free `X`, spuriously diverging from FastClausify's
   *  distinct clause variables (`w`). After [[skolemizeEps]] no `∃` remain, so only `∀` is dropped. */
  def stripForall(f: Expression): Expression =
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
   *  FastClausify's) and only then [[stripForall]]s. */
  def namedNnfSkolemEps(phi: Expression, threshold: Int = FastClausify.DefaultThreshold): Expression =
    skolemizeEps(NnfPhase.toNNF(namedFormula(phi, threshold), negated = false), Counter())

  /** FastClausify's "after Skolem" result for `phi` (∃ → Skolem functions, ∀ stripped) — routed here so the
   *  package-private [[FastClausify]] is reachable from the equivalence test. */
  def fastNamedNnfSkolem(phi: Expression, threshold: Int = FastClausify.DefaultThreshold): Expression =
    FastClausify.namedNnfSkolem(phi, threshold)

  /** `true` iff FastClausify and the certified path name the same subformulas. Both paths mint their naming atoms
   *  with the *same* generator ([[NamingSupport.freshNamingAtom]] → `nm`, same counter progression), so equivalent
   *  naming yields *identical* formulas — a plain structural `==`, no up-to-renaming canonicalization needed. */
  def sameNaming(phi: Expression, threshold: Int = FastClausify.DefaultThreshold): Boolean =
    FastClausify.namedFormula(phi, threshold, Counter()) == namedFormula(phi, threshold)

  // ── the naming phase ───────────────────────────────────────────────────────────────────────────

  /** Selective definitional naming, before NNF, producing a [[ClausificationProof]]. Names arbitrary
   *  (possibly quantified) subformulas via [[nameOne]] and delegates definition clausification to the
   *  downstream phases; each definition is discharged latest-first (see [[NamingSupport.proveQuantifiedReflIff]]). */
  def certifyFastNaming(problem: Problem, prover: ClausificationProver, threshold: Int): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifyFastNaming expects a conjecture-free problem")
    val counter = Counter()
    val n = problem.hypotheses.size
    val L = libImports.size
    val outerImports: IndexedSeq[Sequent] = problem.hypotheses.toIndexedSeq ++ libImports

    // Fresh counter for internal proof markers only, so `counter` (naming atoms) advances exactly as FastClausify.
    val markers = Counter()
    // Per-hypothesis: eliminate `⇒`, then iterate nameOne to a fixpoint — mirroring FastClausify.name.
    final case class HypData(idx: Int, hyp: Sequent, phiElim: Expression, steps: IndexedSeq[NamingStep], named: Expression)
    val allData: IndexedSeq[HypData] = problem.hypotheses.zipWithIndex.map { case (hyp, i) =>
      val phiElim = eliminateImplies(singleRightFormula(hyp, "hypothesis"))
      val buf = scala.collection.mutable.ArrayBuffer.empty[NamingStep]
      var current = phiElim
      var continue = true
      while continue do
        nameOne(current, counter, threshold, markers) match
          case None    => continue = false
          case Some(s) => buf += s; current = s.named
      HypData(i, hyp, phiElim, buf.toIndexedSeq, current)
    }.toIndexedSeq

    val flatSteps: IndexedSeq[NamingStep] = allData.flatMap(_.steps)
    val Q = flatSteps.size
    val quantifieds: IndexedSeq[Expression] = flatSteps.map(_.quantified)

    // Downstream problem: the named hypotheses, then one hypothesis per definition.
    val namedHyps: IndexedSeq[Sequent] = allData.map(hd => () |- hd.named)
    val defHyps: IndexedSeq[Sequent] = quantifieds.map(q => () |- q)
    val newProblem = Problem((namedHyps ++ defHyps).toList, None)

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

    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    // Downstream imports: [named_0..named_{n-1}, def_0..def_{Q-1}] ++ lib.
    val recPremises: IndexedSeq[Int] = namedRefs.toIndexedSeq ++ (0 until Q).map(innerDefRef) ++ (0 until L).map(innerLibRef)
    innerSteps += ClausificationSubproof(downstream, recPremises)
    val innerProof = ClausificationProof(innerSteps.toIndexedSeq, innerImports)

    // ── Outer: one csub carrying the Q definitions as assumptions, discharged latest-first
    //    (d := λx̄. subst makes each `∀x̄. subst ⇔ d(x̄)` reflexive; see dischargeAssumptionsLatestFirst). ──
    val csubPremises: IndexedSeq[Int] = negRange(0, n) ++ negRange(n, L)
    val assumptions: IndexedSeq[Assumption] = (0 until Q).toIndexedSeq.map(j => Assumption(quantifieds(j), n + L + j))
    val csub = ClausificationSubproof(innerProof, csubPremises, assumptions)

    dischargeAssumptionsLatestFirst(csub, Q, outerImports, { j =>
      val st = flatSteps(j)
      (Map(st.tsi -> NamingSupport.lambdifyAll(st.subst, st.freeVars)),
       quantifieds(j),
       NamingSupport.proveQuantifiedReflIff(st.subst, st.freeVars))
    })
