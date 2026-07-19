package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * A **certified** version of the fast (Vampire-style) clausifier: it performs the same selective definitional
 * naming as [[FastClausify]], but *before* NNF and *producing a kernel proof*, then hands the remaining work to
 * the existing certified phases. The composition is
 *
 *   `certifyNegated → certifyFastNaming → certifyNnf → certifySkolem → certifyPrenex → certifyTseitin → prover`
 *
 * so all of NNF (`Restate`), Skolemization (ε via `existsEpsilonIff`), prenexing and the residual clausification
 * are reused unchanged. The only new phase is [[certifyFastNaming]]:
 *
 *  - It replaces a blow-up subformula `subst(x̄)` by a fresh **predicate variable** application `d(x̄)` using a
 *    higher-order [[RightSubstIff]] (the same under-binder machinery [[SkolemPhase.skolemizeOne]] uses for ε),
 *    justified by the definition `∀x̄. d(x̄) ⇔ subst`.
 *  - The definition is added as a fresh hypothesis (clausified by the downstream phases) and carried as a
 *    [[ClausificationSubproof]] *assumption*; at the very end every such assumption is discharged by
 *    `InstSchema(d := λx̄. subst)` + a reflexive-iff proof + `Cut` — exactly [[TseitinPhase.certifyTseitinFlat]]'s
 *    discharge. Instantiating a schema predicate to a (possibly quantified) formula is sound by `InstSchema`.
 *
 * Because the whole thing is kernel-checked, it is a **sound oracle** for the fast clausification (it cannot
 * silently produce an unsatisfiable clause set from a satisfiable problem, unlike the uncertified path).
 */
object CertifiedFastClausifier:

  /** Certify the clausal form and hand it to `prover` (same contract as [[Clausification.certifyClausal]]). */
  def certifyClausal(problem: Problem, prover: Problem => SCProof, threshold: Int = FastClausify.DefaultThreshold): SCProof =
    val wrappedProver: ClausificationProver = p =>
      val downstream = ClausificationProof.fromSCProof(prover(p))
      ClausificationProof(downstream.steps, downstream.imports ++ libImports)
    val tseitinProver: ClausificationProver = TseitinPhase.certifyTseitinFlat(_, wrappedProver)
    val prenexProver: ClausificationProver = PrenexPhase.certifyPrenex(_, tseitinProver)
    val skolemProver: ClausificationProver = SkolemPhase.certifySkolem(_, prenexProver)
    val nnfProver: ClausificationProver = NnfPhase.certifyNnf(_, skolemProver)
    val namingProver: ClausificationProver = certifyFastNaming(_, nnfProver, threshold)
    val fullProver: ClausificationProver = NegatedPhase.certifyNegated(_, namingProver)
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
    def quantified: Expression = TseitinPhase.quantifyAll(subst <=> tsApp, freeVars)

  def nameOne(f: Expression, counter: Counter, threshold: Int): Option[NamingStep] =
    checkInterrupted()
    // Marker `p` (higher-order), parameterised by the enclosing binders `b̄` so that capture-avoiding substitution
    // cannot strand the surrounding quantifiers (identical to SkolemPhase's descent).
    case class Hit(phiBody: Expression, subst: Expression, p: Variable, enclosing: Seq[Variable])

    def descend(e: Expression, enclosing: Seq[Variable]): Option[Hit] =
      def here(sub: Expression): Hit =
        val pSort = enclosing.foldRight(Prop: Sort)((b, acc) => b.sort >>: acc)
        val p = Variable(Identifier(s"_np${counter.next()}", 0), pSort)
        Hit(enclosing.foldLeft(p: Expression)(_(_)), sub, p, enclosing)
      def bin(g: Expression, h0: Expression, op: (Expression, Expression) => Expression): Option[Hit] =
        descend(g, enclosing).map(h => h.copy(phiBody = op(h.phiBody, h0)))
          .orElse(descend(h0, enclosing).map(h => h.copy(phiBody = op(g, h.phiBody))))
      // Name this node if its estimated CNF blows up past the threshold; otherwise recurse.
      if worthNaming(e, threshold) then Some(here(e))
      else e match
        case Forall(y, body) => descend(body, enclosing :+ y).map(h => h.copy(phiBody = forall(Lambda(y, h.phiBody))))
        case Exists(y, body) => descend(body, enclosing :+ y).map(h => h.copy(phiBody = exists(Lambda(y, h.phiBody))))
        case And(g, h0)      => bin(g, h0, and(_)(_))
        case Or(g, h0)       => bin(g, h0, or(_)(_))
        case Neg(g)          => descend(g, enclosing).map(h => h.copy(phiBody = neg(h.phiBody)))
        case Implies(g, h0)  => bin(g, h0, implies(_)(_))
        case Iff(g, h0)      => bin(g, h0, (a, b) => a <=> b)
        case _               => None

    descend(f, Seq.empty).map { h =>
      val taken = scala.collection.mutable.Set.empty[Identifier] ++ f.freeVariables.map(_.id)
      // Fresh witnesses u_i for the enclosing binders (as in SkolemPhase), so the marker/RightSubstIff and the
      // definition are all abstracted over the *same* variables `ū`.
      val us: Seq[Variable] = h.enclosing.map { b =>
        val id = freshId(taken, Identifier("u", 0)); taken += id; Variable(id, b.sort)
      }
      val renaming: Map[Variable, Expression] = h.enclosing.zip(us).toMap
      val substU = substituteVariablesOpti(h.subst, renaming) //   subst[b_i := u_i]

      // Fresh predicate `d` over ALL enclosing binders ū (arity |ū|), matching the marker `p`. The name must be
      // reparseable (it persists into the clauses handed to the prover), so avoid the `_`-prefixed marker style.
      val dSort = us.foldRight(Prop: Sort)((u, acc) => u.sort >>: acc)
      val tsi = Variable(Identifier(s"dNm${counter.next()}", 0), dSort)
      val tsApp = us.foldLeft(tsi: Expression)(_(_)) //           d(u_1)…(u_k)   (= d when ū empty)
      val substLambda = us.foldRight(substU: Expression)((u, e) => Lambda(u, e)) // λū. subst
      val tsAppLambda = us.foldRight(tsApp: Expression)((u, e) => Lambda(u, e)) // λū. d(ū)
      val quantified  = TseitinPhase.quantifyAll(substU <=> tsApp, us)          // ∀ū. subst ⇔ d(ū)   — the definition/iff

      // The named formula: substitute the marker p by λū. d(ū), β-normalise, re-expand η.
      val named = etaExpandQuantifiers(substituteVariablesOpti(h.phiBody, Map(h.p -> tsAppLambda)).betaNormalForm)

      // Bridge: f, quantified ⊢ named via RightSubstIff (rewrite subst → tsApp), then Cut the imported iff.
      val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
      steps += Hypothesis(f |- f, f)
      steps += RightSubstIff(Sequent(Set(f, quantified), Set(named)), 0, Seq((substLambda, tsAppLambda)), (Seq(h.p), h.phiBody))
      steps += Restate(() |- quantified, -1)
      steps += Cut(f |- named, 2, 1, quantified)
      NamingStep(named, tsi, us, tsApp, substU, SCProof(steps.toIndexedSeq, IndexedSeq(() |- quantified)))
    }

  /** Whether `e`'s estimated CNF (in the positive polarity) blows up past `threshold` — the naming trigger.
   *  A conservative first cut: name a subformula whose CNF-clause estimate exceeds the threshold. */
  private def worthNaming(e: Expression, threshold: Int): Boolean =
    e match
      case Iff(_, _) => estimatePos(e, threshold) > threshold //  Iff is the primary blow-up source
      case _         => false

  /** Rough positive-polarity CNF clause-count estimate, capped at `cap+1`. */
  private def estimatePos(e: Expression, cap: Int): Long =
    def go(f: Expression, pol: Boolean): Long =
      val c = cap.toLong + 1
      f match
        case Neg(g)        => go(g, !pol)
        case And(g, h)     => if pol then math.min(c, go(g, true) + go(h, true)) else math.min(c, go(g, false) * go(h, false))
        case Or(g, h)      => if pol then math.min(c, go(g, true) * go(h, true)) else math.min(c, go(g, false) + go(h, false))
        case Implies(g, h) => if pol then math.min(c, go(g, false) * go(h, true)) else math.min(c, go(g, true) + go(h, false))
        case Iff(g, h)     => math.min(c, go(g, true) * go(h, false) + go(g, false) * go(h, true))
        case Forall(_, g)  => go(g, pol)
        case Exists(_, g)  => go(g, pol)
        case _             => 1L
    go(e, true)

  // ── the naming phase ───────────────────────────────────────────────────────────────────────────

  /** Selective definitional naming, before NNF, producing a [[ClausificationProof]]. Mirrors
   *  [[TseitinPhase.certifyTseitinFlat]] but names arbitrary (possibly quantified) subformulas via [[nameOne]]
   *  and delegates definition clausification to the downstream phases. */
  def certifyFastNaming(problem: Problem, prover: ClausificationProver, threshold: Int): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifyFastNaming expects a conjecture-free problem")
    val counter = Counter()
    val n = problem.hypotheses.size
    val L = libImports.size
    val outerImports: IndexedSeq[Sequent] = problem.hypotheses.toIndexedSeq ++ libImports

    // Per-hypothesis: iterate nameOne to a fixpoint, collecting the naming steps and the final named formula.
    final case class HypData(idx: Int, hyp: Sequent, steps: IndexedSeq[NamingStep], named: Expression)
    val allData: IndexedSeq[HypData] = problem.hypotheses.zipWithIndex.map { case (hyp, i) =>
      val phi = singleRightFormula(hyp, "hypothesis")
      val buf = scala.collection.mutable.ArrayBuffer.empty[NamingStep]
      var current = phi
      var continue = true
      while continue do
        nameOne(current, counter, threshold) match
          case None    => continue = false
          case Some(s) => buf += s; current = s.named
      HypData(i, hyp, buf.toIndexedSeq, current)
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
      if hd.steps.isEmpty then namedRefs += innerHypRef(hd.idx)
      else
        // Chain the per-step bridges: from `() ⊢ φ`, each step's bridge gives `() ⊢ named_after_step` using its
        // definition import. (Bridge concludes `prev ⊢ next`; Cut `() ⊢ prev` into it → `() ⊢ next`.)
        var prevRef = innerHypRef(hd.idx)
        var prevFormula: Expression = singleRightFormula(hd.hyp, "hypothesis")
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

    // ── Outer: one csub carrying the Q definitions as assumptions, discharged latest-first. ──
    val csubPremises: IndexedSeq[Int] = negRange(0, n) ++ negRange(n, L)
    val assumptions: IndexedSeq[Assumption] = (0 until Q).toIndexedSeq.map(j => Assumption(quantifieds(j), n + L + j))
    val csub = ClausificationSubproof(innerProof, csubPremises, assumptions)

    val outerSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    outerSteps += csub
    val rhs = csub.bot.right
    val mutableLhs = scala.collection.mutable.HashSet.from(csub.bot.left)
    var prevBotRef = 0
    for j <- (Q - 1) to 0 by -1 do
      val st = flatSteps(j)
      val schemaSubst = Map(st.tsi -> TseitinPhase.lambdifyAll(st.subst, st.freeVars))
      val quantRefl = substituteVariablesOpti(quantifieds(j), schemaSubst)
      mutableLhs -= quantifieds(j); mutableLhs += quantRefl
      outerSteps += KernelStep(InstSchema(Sequent(mutableLhs.toSet, rhs), prevBotRef, schemaSubst))
      val instRef = outerSteps.size - 1
      outerSteps += KernelStep(SCSubproof(TseitinPhase.proveQuantifiedReflIff(st.subst, st.freeVars), IndexedSeq.empty))
      val reflRef = outerSteps.size - 1
      mutableLhs -= quantRefl
      outerSteps += KernelStep(Cut(Sequent(mutableLhs.toSet, rhs), reflRef, instRef, quantRefl))
      prevBotRef = outerSteps.size - 1

    ClausificationProof(outerSteps.toIndexedSeq, outerImports)
