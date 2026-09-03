package lisa.automation.clausification

import lisa.automation.Problem
import lisa.utils.K.{_, given}

import Clausification._

/**
 * The certified clausifier: [[certifyClausal]] composes the phases (README §2.2). Being kernel-checked
 * throughout, this path is a sound oracle for [[UncertifiedClausifier]], which can offer no such guarantee, and
 * the block at the end of this file exposes it at the stages `ClausifierEquivalenceTest` compares.
 */
object CertifiedClausifier:

  /**
   * Run the certified pipeline (screen → negate → name → NNF → Skolem → prenex → distribute) and call `prover`
   * on the clauses. Beyond the caller's hypothesis and conjecture imports, the returned proof imports the
   * library statements ([[libImports]]) in fixed order at the end, for a wrapping tactic to discharge.
   *
   * ==Contract on `prover`==
   * It is called on a conjecture-free clausal [[Problem]] and must return an [[SCProof]] whose '''imports''' are
   * `problem.imports` pointwise and in order, every clause declared even if the refutation does not use it, and
   * whose '''conclusion''' is the empty sequent. Not `{all clause literals} ⊢`: [[NegatedPhase]]'s closing `Cut`
   * lifts only `¬φ` to the left, so it needs the prover proper to derive `⊢`. Each clause it receives is
   * `a₁, …, aₘ ⊢ b₁, …, bₙ` for `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ` (README §1.2), with no
   * disjunctions, quantifiers, or right-hand negations left to unpack.
   */
  def certifyClausal(problem: Problem, prover: Problem => SCProof, threshold: Int = UncertifiedClausifier.DefaultThreshold): SCProof =
    val wrappedProver: ClausificationProver = p =>
      val downstream = ClausificationProof.fromSCProof(prover(p))
      ClausificationProof(downstream.steps, downstream.imports ++ libImports)
    val distributeProver: ClausificationProver = DistributePhase.certifyDistribute(_, wrappedProver)
    val prenexProver: ClausificationProver = PrenexPhase.certifyPrenex(_, distributeProver)
    val skolemProver: ClausificationProver = SkolemPhase.certifySkolem(_, prenexProver)
    val nnfProver: ClausificationProver = NnfPhase.certifyNnf(_, skolemProver)
    val namingProver: ClausificationProver = NamingPhase.certifyNaming(_, nnfProver, threshold)
    val negatedProver: ClausificationProver = NegatedPhase.certifyNegated(_, namingProver)
    val fullProver: ClausificationProver = ScreenPhase.certifyScreen(_, negatedProver)
    clausificationProofToSCProof(fullProver(problem))

  // ── oracles for the uncertified/certified equivalence test ─────────────────────────────────────
  //
  // Everything from here to the end of this block exists only for `ClausifierEquivalenceTest`, which
  // checks that the certified pipeline names and Skolemizes the same way the uncertified [[UncertifiedClausifier]]
  // does. Nothing in the pipeline calls any of it: `certifyClausal` and the phase entry points are the API.

  /**
   * The certified path's named formula (`nameOne` to a fixpoint). Should equal
   *  [[UncertifiedClausifier.namedFormula]] *identically* (both mint `nm` atoms via the same generator).
   */
  private[clausification] def namedFormula(phi: Expression, threshold: Int): Expression =
    val counter = Counter(); val markers = Counter()
    var current = phi
    var continue = true
    while continue do NamingPhase.nameOne(current, counter, threshold, markers, Set.empty) match { case None => continue = false; case Some(s) => current = s.named }
    current

  /**
   * The certified Skolemization of an NNF formula: iterate [[SkolemPhase.skolemizeOne]], which already abstracts
   *  each witness to an opaque shared Skolem function `esk(x̄)` per pass (so ε-terms never nest or blow up), leaving
   *  `∀` in place (the certified pipeline strips them in prenex).
   */
  private[clausification] def skolemizeEps(nnf: Expression, counter: Counter): Expression =
    var current = nnf; var continue = true
    while continue do SkolemPhase.skolemizeOne(current, counter) match { case None => continue = false; case Some(s) => current = s.skoFormula }
    current

  /**
   * Drop every `∀`, **α-renaming** its bound variable to a fresh clause variable, to align with UncertifiedClausifier's
   *  Skolemization (which renames when it strips) and the certified pipeline's prenex phase. Without the rename,
   *  shadowed `∀X … ∀X` binders would collapse into one free `X`, spuriously diverging from UncertifiedClausifier's
   *  distinct clause variables (`w`). After [[skolemizeEps]] no `∃` remain, so only `∀` is dropped.
   */
  private[clausification] def stripForall(f: Expression): Expression =
    val counter = Counter()
    def rec(f: Expression): Expression = f match
      case Forall(x, g) => rec(substituteVariablesOpti(g, Map(x -> Variable(Identifier(GeneratedNames.clauseVar, counter.next()), x.sort))))
      case And(g, h) => and(rec(g))(rec(h))
      case Or(g, h) => or(rec(g))(rec(h))
      case Neg(g) => neg(rec(g))
      case _ => f
    rec(f)

  /**
   * The named formula through NNF and certified (ε-)Skolemization, giving the raw ε-form with `∀` still present. The
   *  after-Skolem equivalence test ε-abstracts it (over the *original* names, so Skolem arguments line up with
   *  UncertifiedClausifier's) and only then [[stripForall]]s.
   */
  private[clausification] def namedNnfSkolemEps(phi: Expression, threshold: Int = UncertifiedClausifier.DefaultThreshold): Expression =
    skolemizeEps(NnfPhase.toNNF(namedFormula(phi, threshold), negated = false), Counter())

  /**
   * UncertifiedClausifier's "after Skolem" result for `phi` (∃ → Skolem functions, ∀ stripped), placed beside
   *  [[namedNnfSkolemEps]] so the equivalence test reads the two oracles off one object at one signature.
   */
  private[clausification] def uncertifiedNamedNnfSkolem(phi: Expression, threshold: Int = UncertifiedClausifier.DefaultThreshold): Expression =
    UncertifiedClausifier.namedNnfSkolem(phi, threshold)

  /**
   * `true` iff UncertifiedClausifier and the certified path name the same subformulas. Both paths mint their naming atoms
   *  with the *same* generator ([[NamingSupport.freshNamingAtom]] → `nm`, same counter progression), so equivalent
   *  naming yields *identical* formulas, compared by a plain structural `==` with no canonicalization needed.
   */
  private[clausification] def sameNaming(phi: Expression, threshold: Int = UncertifiedClausifier.DefaultThreshold): Boolean =
    UncertifiedClausifier.namedFormula(phi, threshold, Counter()) == namedFormula(phi, threshold)
