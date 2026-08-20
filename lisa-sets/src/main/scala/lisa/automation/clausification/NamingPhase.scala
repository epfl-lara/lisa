package lisa.automation.clausification

import lisa.utils.K.{_, given}
import lisa.automation.Problem
import Clausification.*

/**
 * Selective definitional naming (Tseitin/Plaisted-Greenbaum, README §1.4): replace a subformula whose CNF
 * estimate exceeds the threshold by a fresh predicate application `d(x̄)`, and record `∀x̄. d(x̄) ⇔ subst` as a
 * definition. The replacement is certified with a second-order substitution, and the definition is eliminated
 * instantiation, reflexivity and cut.
 * The phase runs before NNF, so it names arbitrary, possibly quantified subformulas.
 */
private[clausification] object NamingPhase:

  /** One naming step on `f`: the leftmost blow-up subformula `subst` replaced by
    * a fresh predicate application `tsApp = d(x̄)`, together with the bridge proof `f ⊢ named`
    */
  final case class NamingStep(
      named: Expression, //          f with `subst` replaced by `nmApp`
      nm: Variable, //               the fresh naming predicate variable (`GeneratedNames.namingAtom`)
      freeVars: Seq[Variable], //    x̄ (the Ind free variables of `subst`)
      nmApp: Expression, //          d(x̄)
      subst: Expression, //          the named subformula
      pol: Int, //                   the polarity `subst` occurs at (+1 / -1 / 0 under `⇔`)
      quantified: Expression, //     the full definition `∀x̄. subst ⇔ d(x̄)`, which the bridge below imports
      bridge: SCProof //             conclusion `f ⊢ named`, one import `() ⊢ quantified`
  ):
    /** The definition handed to the downstream phases, i.e. the one that gets clausified: only the half
      * the site's polarity actually uses (Plaisted-Greenbaum).
      */
    def directional: Expression =
      val body =
        if pol > 0 then implies(nmApp)(subst) //      positive occurrence: d ⇒ subst
        else if pol < 0 then implies(subst)(nmApp) // negative occurrence: subst ⇒ d
        else subst <=> nmApp //                       both (under `⇔`): the full definition
      NamingSupport.quantifyAll(body, freeVars)

  // `Est` / `capMul` / `capAdd` (the capped clause-count arithmetic) are shared with UncertifiedClausifier: see `Clausification`.

  /** The subformula UncertifiedClausifier.name names *next*, plus the `RightSubstIff` context to certify it and the
    * polarity it occurs at, which decides which half of the definition the downstream phases get (see
    * [[NamingStep.directional]]). */
  private final case class Site(subst: Expression, phiBody: Expression, p: Variable, pol: Int,
                                xs: Seq[Variable], rebuild: Expression => Expression)

  /** Find the larger child of the deepest-leftmost multiplicative node whose estimate exceeds `threshold`, 
   * post-order (same as the uncertified version)). */
  private def findSite(f: Expression, pol: Int, threshold: Int, markers: Counter, frozen: Set[Variable]): Option[Site] =
    // `sitePol` is the polarity of `child` itself, which is the enclosing node's polarity for `∧`/`∨` and 0 under `⇔`.
    def mk(child: Expression, sitePol: Int, rebuild: Expression => Expression): Site =
      val xs = NamingSupport.namingVars(child, frozen)
      val pSort = xs.foldRight(Prop: Sort)((v, acc) => v.sort >>: acc)
      val p = Variable(Identifier(GeneratedNames.hole, markers.next()), pSort)
      // `xs` and `rebuild` are kept: `nameOne` sizes the naming atom from the first, rather than recomputing the
      // same free-variable list, and fills the same context with it through the second.
      Site(child, rebuild(xs.foldLeft(p: Expression)(_(_))), p, sitePol, xs, rebuild)
      
    // Returns the site, if any, together with the node's own estimate, which is combined from the children's
    // rather than recomputed: asking for it separately at each node would walk every subtree again. The two
    // children are always searched, where the old `orElse` chain stopped at the first hit, so `markers` may
    // advance further; the numbers never leave the step, being substituted away with `p`.
    def go(f: Expression, pol: Int, rebuild: Expression => Expression): (Option[Site], Est) = f match
      case And(g, h) => // pos additive, neg multiplicative 
        val (og, eg) = go(g, pol, hole => rebuild(and(hole)(h)))
        val (oh, eh) = go(h, pol, hole => rebuild(and(g)(hole)))
        val here = og.orElse(oh).orElse:
          if pol <= 0 && capMul(eg.neg, eh.neg) > threshold && (eg.neg > 1 || eh.neg > 1) then
            if eg.neg >= eh.neg && eg.neg > 1 then Some(mk(g, pol, hole => rebuild(and(hole)(h))))
            else Some(mk(h, pol, hole => rebuild(and(g)(hole))))
          else None
        (here, Est.and(eg, eh))
      case Or(g, h) => // pos multiplicative, neg additive
        val (og, eg) = go(g, pol, hole => rebuild(or(hole)(h)))
        val (oh, eh) = go(h, pol, hole => rebuild(or(g)(hole)))
        val here = og.orElse(oh).orElse:
          if pol >= 0 && capMul(eg.pos, eh.pos) > threshold && (eg.pos > 1 || eh.pos > 1) then
            if eg.pos >= eh.pos && eg.pos > 1 then Some(mk(g, pol, hole => rebuild(or(hole)(h))))
            else Some(mk(h, pol, hole => rebuild(or(g)(hole))))
          else None
        (here, Est.or(eg, eh))
      // `g ⇒ h` is searched as `¬g ∨ h`, so the sites and their polarities are the `Or` case's and no gate is
      // duplicated. A site found under it rebuilds into that expanded form, which is OL-equal to the original,
      // so the bridge's `RightSubstIff` context still matches; where nothing is named the `⇒` is left alone.
      case Implies(g, h) => go(or(neg(g))(h), pol, rebuild)
      case Neg(g) =>
        val (og, eg) = go(g, -pol, hole => rebuild(neg(hole)))
        (og, Est.neg(eg))
      case Iff(g, h) => // children at polarity 0
        val (og, eg) = go(g, 0, hole => rebuild(hole <=> h))
        val (oh, eh) = go(h, 0, hole => rebuild(g <=> hole))
        val here = og.orElse(oh).orElse:
          val e = Est.iff(eg, eh)
          val big = if pol > 0 then e.pos > threshold else if pol < 0 then e.neg > threshold else e.pos > threshold || e.neg > threshold
          if big && (Est.size(eg) > 2 || Est.size(eh) > 2) then
            if Est.size(eg) >= Est.size(eh) && Est.size(eg) > 2 then Some(mk(g, 0, hole => rebuild(hole <=> h)))
            else Some(mk(h, 0, hole => rebuild(g <=> hole)))
          else None
        (here, Est.iff(eg, eh))
      case Forall(x, g) => go(g, pol, hole => rebuild(forall(Lambda(x, hole))))
      case Exists(x, g) => go(g, pol, hole => rebuild(exists(Lambda(x, hole))))
      case `top`        => (None, Est(0, 1))
      case `bot`        => (None, Est(1, 0))
      case _            => (None, atomEst)
    go(f, pol, identity)._1

  /** One naming step matching UncertifiedClausifier: name the `findSite` subformula with [[NamingSupport.freshNamingAtom]]
   *  using the *same* generator, and hence the same `nm` atoms, as the uncertified [[UncertifiedClausifier]], with the bridge
   *  `f ⊢ named` (via HO `RightSubstIff`, import `() ⊢ ∀x̄. subst ⇔ d(x̄)`). */
  def nameOne(f: Expression, counter: Counter, threshold: Int, markers: Counter, frozen: Set[Variable]): Option[NamingStep] =
    checkInterrupted()
    findSite(f, 1, threshold, markers, frozen).map { site =>
      val (nm, freeVars, nmApp) = NamingSupport.freshNamingAtomOver(site.xs, counter)
      val substLambda = NamingSupport.lambdifyAll(site.subst, freeVars)
      val nmAppLambda = NamingSupport.lambdifyAll(nmApp, freeVars)
      val quantified = NamingSupport.quantifyAll(site.subst <=> nmApp, freeVars)
      // The context filled with `nmApp` instead of the marker, which rebuilds only the spine down to the site.
      // Substituting `p -> nm` through `phiBody` would give the same formula by walking all of it.
      val named = site.rebuild(nmApp)
      val steps = IndexedSeq(
        Hypothesis(f |- f, f), //                                                                              0
        RightSubstIff(Sequent(Set(f, quantified), Set(named)), 0, Seq((substLambda, nmAppLambda)), (Seq(site.p), site.phiBody)),
        Restate(() |- quantified, -1), //                                                                      2
        Cut(f |- named, 2, 1, quantified))
      NamingStep(named, nm, freeVars, nmApp, site.subst, site.pol, quantified, SCProof(steps, IndexedSeq(() |- quantified)))
    }

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
    /** One hypothesis on its way through naming: the formula naming starts from, and the [[NamingStep]]s applied
      * to it in order. The form they end at, which is what goes downstream, is the last one's. */
    final case class HypData(phi: Expression, steps: IndexedSeq[NamingStep]):
      def named: Expression = steps.lastOption.map(_.named).getOrElse(phi)
    // Per-hypothesis: iterate nameOne to a fixpoint, mirroring UncertifiedClausifier.name.
    val allData: IndexedSeq[HypData] = problem.hypotheses.toIndexedSeq.map { hyp =>
      val phi = singleRightFormula(hyp, "hypothesis")
      HypData(phi, Iterator.unfold(phi)(current =>
        nameOne(current, counter, threshold, markers, problem.frozen).map(s => (s, s.named))).toIndexedSeq)
    }

    val flatSteps: IndexedSeq[NamingStep] = allData.flatMap(_.steps)
    val Q = flatSteps.size
    val quantifieds: IndexedSeq[Expression] = flatSteps.map(_.quantified)

    // Downstream problem: the named hypotheses, then one hypothesis per definition. The definitions go down as
    // their *directional* half (see `NamingStep.directional`). The biconditional stays behind as the
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
    val defBase = allData.map(_.steps.size).scanLeft(0)(_ + _) // defBase(i): hypothesis i's first definition slot
    for (hd, i) <- allData.zipWithIndex do
      // Start from `() ⊢ φ` and chain the per-step naming bridges (each `prev ⊢ next` via its definition, Cut
      // in `() ⊢ prev`). With no steps the loop does not run and the import reference is what goes downstream.
      var prevRef = innerHypRef(i)
      var prevFormula: Expression = hd.phi
      for k <- hd.steps.indices do
        val st = hd.steps(k)
        innerSteps += SCSubproof(st.bridge, IndexedSeq(innerDefRef(defBase(i) + k)))
        val bridgeRef = innerSteps.size - 1
        innerSteps += Cut(() |- st.named, prevRef, bridgeRef, prevFormula)
        prevRef = innerSteps.size - 1
        prevFormula = st.named
      namedRefs += prevRef

    // Weaken each `⇔` assumption to the directional half the downstream problem declares. One `Weakening` per
    // definition: the kernel's rule is `isImplyingSequent`, an ortholattice *entailment*, and the checker takes
    // `∀x̄.(a ⇔ b) ⊢ ∀x̄.(a ⇒ b)`, reaching under the binder. At polarity 0 the two coincide and the
    // assumption import is cited directly.
    val defRefs: IndexedSeq[Int] = (0 until Q).map { j =>
      if directionals(j) == quantifieds(j) then innerDefRef(j)
      else
        innerSteps += Weakening(() |- directionals(j), innerDefRef(j))
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
    val csubPremises: IndexedSeq[Int] = negRange(0, n + L)
    val assumptions: IndexedSeq[Int] = (0 until Q).toIndexedSeq.map(j => n + L + j)
    val csub = ClausificationSubproof(innerProof, csubPremises, assumptions)

    dischargeAssumptionsLatestFirst(csub, Q, outerImports, { j =>
      val st = flatSteps(j)
      (Map(st.nm -> NamingSupport.lambdifyAll(st.subst, st.freeVars)),
       quantifieds(j),
       NamingSupport.proveQuantifiedReflIff(st.subst, st.freeVars))
    })
