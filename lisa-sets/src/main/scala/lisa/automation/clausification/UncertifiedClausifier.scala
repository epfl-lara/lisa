package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * The **uncertified** clausifier: an equisatisfiable clause set with **no proof**, for the callers that do not
 * need a kernel-checkable certificate (CASC, the benchmark harnesses, and measuring how much of the certified
 * pipeline's cost is proof-building). Vampire/E-style, and a single pass rather than the certified path's chain
 * of phases:
 *
 *   1. **Selective naming** (definitional CNF, polarity-sensitive): a bottom-up pass over the formula-with-`⇔`
 *      that replaces a subformula by a fresh predicate atom `d(x̄)` (over its Ind free vars) + a directional
 *      definition, but **only** where a multiplicative context (`∨` positive, `∧` negative, `⇔`) would blow the
 *      estimated clause count past `threshold`. This keeps both the clause count *and* the Skolem-function count
 *      polynomial (a named subformula's existentials are Skolemized once, in its definition).
 *   2. **NNF** ([[NnfPhase.toNNF]]) — bounded, since the blow-up-prone `⇔`s now have bounded children.
 *   3. **Single-pass Skolemization** with fresh Skolem **functions** (no ε, which the certified path needs only
 *      because it may not extend the signature): one descent threading the in-scope universals, α-renaming
 *      `∀`-bound vars and stripping the quantifiers.
 *   4. **Distribution** to clauses, in the shape given by [[Clausification.clauseSequent]].
 *
 * Equisatisfiability is all this path claims, so fresh Skolem functions and definition predicates are free to
 * use. [[CertifiedClausifier]] is the certified twin, phase for phase, and need only agree with this up to
 * equisatisfiability rather than clause for clause. `ClausifierEquivalenceTest` holds the two to the stronger
 * agreement they actually reach: the same naming decisions, and Skolemized forms equal up to a renaming.
 */
object UncertifiedClausifier:

  /** Name a subformula once its CNF estimate exceeds this (clauses vs fresh-symbol trade-off; ~break-even at 4). */
  val DefaultThreshold: Int = 4

  // `Est` / `atomEst` / `capMul` / `capAdd` are shared with the certified twin — see `Clausification`.

  // ── top level: one formula → clauses (each a set of literals) ──────────────────────────────────

  // The three below are the halves of [[clausify]] exposed individually so the certified twin can be checked
  // against them stage by stage (`ClausifierEquivalenceTest`, via `CertifiedClausifier`'s oracle
  // block). `clausify` is this object's real entry point; these are `private[clausification]` to say so.

  /** The named formula (⇒ eliminated, blow-up subformulas replaced by fresh atoms) — the naming half of
   *  [[clausify]]. */
  private[clausification] def namedFormula(phi: Expression, threshold: Int, counter: Counter): Expression =
    name(phi, 1, threshold, Set.empty, scala.collection.mutable.ListBuffer.empty[Expression], counter)._1

  /** The uncertified Skolemization of an NNF formula (∃ → Skolem functions, ∀ stripped): seeds [[skolemize]]
   *  with an empty substitution and the formula's own `Ind` free variables mapped to themselves. */
  private[clausification] def skolemizeNnf(nnf: Expression, counter: Counter): Expression =
    skolemize(nnf, Map.empty, nnf.freeVariables.iterator.filter(_.sort == Ind).map(v => (v, v)).toList, counter)

  /** The named formula (naming step) put through NNF and Skolemization — the "after Skolem" result for `phi`. */
  private[clausification] def namedNnfSkolem(phi: Expression, threshold: Int): Expression =
    skolemizeNnf(NnfPhase.toNNF(namedFormula(phi, threshold, Counter()), negated = false), Counter())

  def clausify(phi: Expression, threshold: Int, frozen: Set[Variable], counter: Counter): List[Set[Expression]] =
    val defs = scala.collection.mutable.ListBuffer.empty[Expression]
    val (named, _) = name(phi, 1, threshold, frozen, defs, counter)
    (named :: defs.toList).flatMap { g =>
      val nnf = NnfPhase.toNNF(g, negated = false)
      // Free Ind vars are the top-level universals; they aren't α-renamed, so orig = renamed.
      val univs = nnf.freeVariables.iterator.filter(_.sort == Ind).map(v => (v, v)).toList
      toClauses(skolemize(nnf, Map.empty, univs, counter))
    }

  /** Clausal form of `problem`, mirroring [[UncertifiedClausifier.clausalForm]]'s conjecture handling
   *  (append `¬conjecture` as the last hypothesis) but with the single-pass pipeline. */
  def clausalForm(problem: Problem, threshold: Int = DefaultThreshold, orthologic: Boolean = false): Problem =
    Problem(clausalFormWithOrigins(problem, threshold, orthologic).map(_._1).toList, None)

  /** Like [[clausalForm]] but pairs each clause with the **index of the source formula it was clausified from** —
   *  an index into `hypotheses ++ [¬conjecture]` (so `hypotheses.size` denotes the negated conjecture). Lets a
   *  proof-printing front-end attribute every clause to its single origin axiom. */
  def clausalFormWithOrigins(problem: Problem, threshold: Int = DefaultThreshold, orthologic: Boolean = false): IndexedSeq[(Sequent, Int)] =
    val hyps0: IndexedSeq[Sequent] = problem.conjecture match
      case Some(c) =>
        // Universally close the conjecture's free individual variables before negating, exactly as
        // [[NegatedPhase.certifyNegated]] does. A goal `φ(x̄)` means `∀x̄. φ(x̄)`, so its negation is `∃x̄. ¬φ`,
        // which Skolemizes to fresh constants. Negating `φ(x̄)` as-is would leave x̄ as universal clause
        // variables — i.e. refuting only `∃x̄. φ`, a strictly easier task — and this path would then claim
        // refutations the certified path correctly does not (`pp(c) ⊢ pp(x)` is the smallest such goal).
        // Invisible on TPTP, whose conjectures are closed; it only shows up on Lisa goals with free variables.
        val phi = singleRightFormula(c, "conjecture")
        val freeInd: Seq[Variable] = phi.freeVariables.toSeq.filter(_.sort == Ind).sortBy(_.id.toString)
        problem.hypotheses.toIndexedSeq :+ (() |- neg(freeInd.foldRight(phi)((v, acc) => forall(Lambda(v, acc)))))
      case None => problem.hypotheses.toIndexedSeq
    val counter = Counter(freshCounterStart(hyps0))
    hyps0.zipWithIndex.flatMap { (h, origin) =>
      // `orthologic`: after negating the conjecture (done in `hyps0`) but before naming + clausification, replace
      // each axiom / negated conjecture by its orthologic normal form — exactly one `reducedNNFForm` step each.
      val f0 = singleRightFormula(h, "hypothesis")
      // η-expand every quantifier — this path's entry point, the counterpart of what [[ScreenPhase]] does for the
      // certified pipeline (see [[Clausification.etaExpandQuantifiers]] for the invariant and why it matters).
      // Nothing else normalises the caller's formulas, and the phases below match on [[Forall]]/[[Exists]], which
      // need an explicit `Lambda`: an η-reduced `∀(p)` would otherwise travel all the way into a clause as an
      // opaque literal, with no equivalent of the certified path's `DistributePhase` check to catch it.
      // *After* the orthologic step, never before: `reducedNNFForm` rebuilds the formula through the kernel's
      // locally-nameless normal form, so whatever we normalised beforehand can come back reshaped.
      val f  = etaExpandQuantifiers(if orthologic then reducedNNFForm(f0) else f0)
      clausify(f, threshold, problem.frozen, counter).map(lits => (clauseSequent(lits), origin))
    }

  /**
   * Where the shared fresh-name counter must start so that nothing this path mints can collide with a name
   * already in the input.
   *
   * All three generated kinds draw from one counter and one of three prefixes — `w` clause variables (stripped
   * `∀`s), `sk` Skolem functions, `nm` naming atoms — as `Identifier(prefix, n)`. The counter starts at 0, so the
   * *first* of each kind is `Identifier(prefix, 0)`, which renders as the bare `w` / `sk` / `nm`. An input symbol
   * of exactly that identifier is therefore the same symbol, and the two silently merge.
   *
   * Measured: for `∀x. q(x, w) ⊢ q(a, c)` with `w` free, this path produced the clause `q(w, w)` — the stripped
   * `∀x` and the input's `w` collapsed into one variable — turning `∀w.∀x. q(x,w)` into the strictly weaker
   * `∀w. q(w,w)` and losing the (valid) refutation. The certified path is immune for a structural reason rather
   * than a lucky one: [[ScreenPhase]] renames every input variable into `v`/`usr` before any phase runs, and
   * every name the certified phases mint is a `Variable`, so an input `Constant` cannot collide either.
   *
   * Rather than screen (which would rewrite names this path has no proof obligation to restore, and would change
   * what `CascProver` prints), start the counter past any input identifier that could clash. When the input uses
   * none of the three prefixes — every TPTP problem — this is `0` and nothing changes.
   *
   * Both `Variable`s and `Constant`s are scanned: this path mints Skolem symbols as `Constant`s, so a constant
   * named `sk` collides just as a variable named `w` does. Bound occurrences are scanned too; capture is already
   * handled by `substituteVariablesOpti`, but including them costs one comparison and removes the question.
   */
  private def freshCounterStart(hypotheses: Seq[Sequent]): Int =
    val prefixes = Set(GeneratedNames.clauseVar, GeneratedNames.uncertifiedSkolem, GeneratedNames.namingAtom)
    var maxNo = -1
    def note(id: Identifier): Unit = if prefixes(id.name) && id.no > maxNo then maxNo = id.no
    def scan(e: Expression): Unit = e match
      case Application(f, a) => scan(f); scan(a)
      case Lambda(v, b)      => note(v.id); scan(b)
      case v: Variable       => note(v.id)
      case c: Constant       => note(c.id)
    hypotheses.foreach(s => { s.left.foreach(scan); s.right.foreach(scan) })
    maxNo + 1

  // ── selective naming (definitional CNF) ────────────────────────────────────────────────────────

  // Introduce a fresh atom for `c` (occurring at polarity `pol`) + its directional definition; returns the atom.
  private def define(c: Expression, pol: Int, frozen: Set[Variable], defs: scala.collection.mutable.ListBuffer[Expression], counter: Counter): Expression =
    val (_, _, atom) = NamingSupport.freshNamingAtom(c, counter, frozen)
    defs +=
      (if pol > 0 then or(neg(atom))(c) //            positive occurrence: d ⇒ c
       else if pol < 0 then or(atom)(neg(c)) //       negative occurrence: c ⇒ d
       else and(or(neg(atom))(c))(or(atom)(neg(c)))) // both (under ⇔):     d ⟺ c
    atom

  private inline def relevantBig(pos: Long, neg: Long, pol: Int, threshold: Int): Boolean =
    if pol > 0 then pos > threshold else if pol < 0 then neg > threshold else pos > threshold || neg > threshold

  /** Rewrite `f` (at polarity `pol`) naming blow-up subformulas in multiplicative contexts; return the rewritten
   *  formula and its (capped) clause-count estimate. Single bottom-up pass — each node's estimate is combined from
   *  its (already-processed) children's, never recomputed. */
  private def name(f: Expression, pol: Int, threshold: Int, frozen: Set[Variable], defs: scala.collection.mutable.ListBuffer[Expression], counter: Counter): (Expression, Est) =
    f match
      case And(g, h) => // pos = Σ (additive), neg = Π (multiplicative)
        var (g2, eg) = name(g, pol, threshold, frozen, defs, counter)
        var (h2, eh) = name(h, pol, threshold, frozen, defs, counter)
        while pol <= 0 && capMul(eg.neg, eh.neg) > threshold && (eg.neg > 1 || eh.neg > 1) do
          if eg.neg >= eh.neg && eg.neg > 1 then { g2 = define(g2, pol, frozen, defs, counter); eg = atomEst }
          else { h2 = define(h2, pol, frozen, defs, counter); eh = atomEst }
        (and(g2)(h2), Est(capAdd(eg.pos, eh.pos), capMul(eg.neg, eh.neg)))
      case Or(g, h) => // pos = Π (multiplicative), neg = Σ (additive)
        var (g2, eg) = name(g, pol, threshold, frozen, defs, counter)
        var (h2, eh) = name(h, pol, threshold, frozen, defs, counter)
        while pol >= 0 && capMul(eg.pos, eh.pos) > threshold && (eg.pos > 1 || eh.pos > 1) do
          if eg.pos >= eh.pos && eg.pos > 1 then { g2 = define(g2, pol, frozen, defs, counter); eg = atomEst }
          else { h2 = define(h2, pol, frozen, defs, counter); eh = atomEst }
        (or(g2)(h2), Est(capMul(eg.pos, eh.pos), capAdd(eg.neg, eh.neg)))
      case Neg(g) =>
        val (g2, eg) = name(g, -pol, threshold, frozen, defs, counter)
        (neg(g2), Est(eg.neg, eg.pos))
      case Implies(g, h) => name(or(neg(g))(h), pol, threshold, frozen, defs, counter) // eliminate → to ¬g ∨ h
      case Iff(g, h) => // children live at both polarities; both pos and neg are multiplicative
        var (g2, eg) = name(g, 0, threshold, frozen, defs, counter)
        var (h2, eh) = name(h, 0, threshold, frozen, defs, counter)
        def ip(a: Est, b: Est): Long = capAdd(capMul(a.pos, b.neg), capMul(a.neg, b.pos))
        def in(a: Est, b: Est): Long = capAdd(capMul(a.pos, b.pos), capMul(a.neg, b.neg))
        def sz(e: Est): Long = capAdd(e.pos, e.neg)
        while relevantBig(ip(eg, eh), in(eg, eh), pol, threshold) && (sz(eg) > 2 || sz(eh) > 2) do
          if sz(eg) >= sz(eh) && sz(eg) > 2 then { g2 = define(g2, 0, frozen, defs, counter); eg = atomEst }
          else { h2 = define(h2, 0, frozen, defs, counter); eh = atomEst }
        (g2 <=> h2, Est(ip(eg, eh), in(eg, eh)))
      case Forall(x, g) => val (g2, eg) = name(g, pol, threshold, frozen, defs, counter); (forall(x, g2), eg)
      case Exists(x, g) => val (g2, eg) = name(g, pol, threshold, frozen, defs, counter); (exists(x, g2), eg)
      case `top`        => (top, Est(0, 1))
      case `bot`        => (bot, Est(1, 0))
      case atom         => (atom, atomEst)

  // ── single-pass Skolemization (fresh Skolem functions; strip ∀; α-rename) ───────────────────────

  // `univs` pairs each in-scope universal's ORIGINAL bound variable with its α-renamed clause variable (used in the
  // Skolem term). Each ∃ gets its **own** fresh Skolem symbol (the textbook rule — unconditionally sound); we do NOT
  // dedup syntactically-identical existentials. The certified ε-path does merge them (identical ε-terms are one
  // term), so the uncertified path is a strict *refinement* of the certified one: every uncertified Skolem symbol maps onto one certified symbol.
  private def skolemize(f: Expression, subst: Map[Variable, Expression], univs: List[(Variable, Variable)], counter: Counter): Expression =
    f match
      case And(g, h) => and(skolemize(g, subst, univs, counter))(skolemize(h, subst, univs, counter))
      case Or(g, h)  => or(skolemize(g, subst, univs, counter))(skolemize(h, subst, univs, counter))
      case Forall(x, g) => // α-rename to a fresh var (avoid capture), strip the ∀, extend the universal context
        val v = Variable(Identifier(GeneratedNames.clauseVar, counter.next()), x.sort)
        skolemize(g, subst + (x -> v), if x.sort == Ind then univs :+ (x, v) else univs, counter)
      case Exists(x, g) => // fresh Skolem function over ONLY the universals the witness can depend on (⇒ smaller terms)
        // Free variables of the SUBSTITUTED body: this reveals *transitive* dependencies on a universal `u` that
        // reach the body only through an earlier ∃-variable's Skolem term `sk…(u)` — using `g.freeVariables`
        // (original, unsubstituted) would miss them and unsoundly drop `u` from the Skolem's arguments.
        val bodyFree = substituteVariablesOpti(f, subst).freeVariables // renamed (w) clause-var names + Skolem-term vars (x bound)
        // In **binding order** (outermost enclosing universal first — `univs` is built outermost-first): a canonical
        // argument order that needs no names, so it matches the certified path's `abstractEpsTerms` ordering of an
        // ε-term's free variables (which the certified Skolemizer may have α-renamed, breaking a name-based sort).
        val mentioned = univs.collect { case (_, v) if bodyFree.contains(v) => v }
        val skSort = mentioned.foldRight(x.sort)((u, acc) => u.sort -> acc)
        // A **Constant** (function symbol), NOT a Variable: a *nullary* Skolem has result sort `Ind`, so as a
        // Variable it would be mistaken for a clause variable (universally quantified) — unsound.
        val skTerm = mentioned.foldLeft(Constant(Identifier(GeneratedNames.uncertifiedSkolem, counter.next()), skSort): Expression)((acc, u) => acc(u))
        skolemize(g, subst + (x -> skTerm), univs, counter)
      case lit => if subst.isEmpty then lit else substituteVariablesOpti(lit, subst)

  // ── distribution to clauses ─────────────────────────────────────────────────────────────────────

  private def toClauses(f: Expression): List[Set[Expression]] =
    f match
      case And(g, h) => toClauses(g) ++ toClauses(h)
      case Or(g, h)  => val cg = toClauses(g); val ch = toClauses(h); for a <- cg; b <- ch yield a ++ b
      case `top`     => Nil //             ⊤ conjunct contributes no clause
      case `bot`     => List(Set.empty) // ⊥ conjunct is the empty clause
      case lit       => List(Set(lit))

  // ── the prover-facing entry point ───────────────────────────────────────────────────────────────

  /**
   * Compute the clausal form and hand it to `prover`, returning the prover's proof verbatim (imports = the
   * clauses, conclusion `∅ ⊢`). The same signature as [[CertifiedClausifier.certifyClausal]], so a caller can
   * swap one for the other, but the clausification is **not** certified: nothing links the clauses back to the
   * original conjecture, and the returned proof refutes the clause set only.
   */
  def uncertifyClausal(problem: Problem, prover: Problem => SCProof): SCProof =
    prover(clausalForm(problem))
