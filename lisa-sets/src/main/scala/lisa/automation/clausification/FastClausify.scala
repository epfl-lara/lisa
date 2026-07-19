package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Fast, **non-proof-producing** clausifier (Vampire/E-style), for [[UncertifiedClausification]]. It replaces the
 * quadratic one-rewrite-per-step `skolemizeAll` + full-Tseitin `tseitinAll` (and the prenex phase) with a small
 * set of **single-pass** transforms:
 *
 *   1. **Selective naming** (definitional CNF, polarity-sensitive): a bottom-up pass over the formula-with-`⇔`
 *      that replaces a subformula by a fresh predicate atom `d(x̄)` (over its Ind free vars) + a directional
 *      definition, but **only** where a multiplicative context (`∨` positive, `∧` negative, `⇔`) would blow the
 *      estimated clause count past `threshold`. This keeps both the clause count *and* the Skolem-function count
 *      polynomial (a named subformula's existentials are Skolemized once, in its definition).
 *   2. **NNF** ([[NnfPhase.toNNF]]) — now bounded, since the blow-up-prone `⇔`s have bounded children.
 *   3. **Single-pass Skolemization** with fresh Skolem **functions** (no ε): one descent threading the in-scope
 *      universals, α-renaming `∀`-bound vars and stripping the quantifiers.
 *   4. **Distribution** to clauses.
 *
 * The result is **equisatisfiable** (fresh Skolem functions + definition predicates), which is all the uncertified
 * path needs — there is no clausification proof. See `Phase5DemodulationResearch.md`'s clausification comparison
 * and the JOURNAL.
 */
private[clausification] object FastClausify:

  /** Name a subformula once its CNF estimate exceeds this (clauses vs fresh-symbol trade-off; ~break-even at 4). */
  val DefaultThreshold: Int = 4

  private val Cap: Long = 1L << 20 // clause-count estimates are saturated here (we only compare against `threshold`)
  private inline def capMul(a: Long, b: Long): Long = math.min(Cap, a * b)
  private inline def capAdd(a: Long, b: Long): Long = math.min(Cap, a + b)

  /** Estimated number of CNF clauses of a formula, positive and negative polarity (both saturated at [[Cap]]). */
  private final case class Est(pos: Long, neg: Long)
  private val atomEst = Est(1, 1)

  // ── top level: one formula → clauses (each a set of literals) ──────────────────────────────────

  def clausify(phi: Expression, threshold: Int, counter: Counter): List[Set[Expression]] =
    val defs = scala.collection.mutable.ListBuffer.empty[Expression]
    val (named, _) = name(phi, 1, threshold, defs, counter)
    (named :: defs.toList).flatMap { g =>
      val nnf = NnfPhase.toNNF(g, negated = false)
      val univs = nnf.freeVariables.iterator.filter(_.sort == Ind).toList
      toClauses(skolemize(nnf, Map.empty, univs, counter))
    }

  /** Clausal form of `problem`, mirroring [[UncertifiedClausification.clausalForm]]'s conjecture handling
   *  (append `¬conjecture` as the last hypothesis) but with the single-pass pipeline. */
  def clausalForm(problem: Problem, threshold: Int = DefaultThreshold): Problem =
    val hyps0: IndexedSeq[Sequent] = problem.conjecture match
      case Some(c) => problem.hypotheses.toIndexedSeq :+ (() |- neg(singleRightFormula(c, "conjecture")))
      case None    => problem.hypotheses.toIndexedSeq
    val counter = Counter()
    val clauses = hyps0.flatMap { h =>
      clausify(singleRightFormula(h, "hypothesis"), threshold, counter).map(lits => Sequent(Set.empty, lits))
    }
    Problem(clauses.toList, None)

  // ── selective naming (definitional CNF) ────────────────────────────────────────────────────────

  // Introduce a fresh atom for `c` (occurring at polarity `pol`) + its directional definition; returns the atom.
  private def define(c: Expression, pol: Int, defs: scala.collection.mutable.ListBuffer[Expression], counter: Counter): Expression =
    val (_, _, atom) = TseitinPhase.freshTseitinAtom(c, counter)
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
  private def name(f: Expression, pol: Int, threshold: Int, defs: scala.collection.mutable.ListBuffer[Expression], counter: Counter): (Expression, Est) =
    f match
      case And(g, h) => // pos = Σ (additive), neg = Π (multiplicative)
        var (g2, eg) = name(g, pol, threshold, defs, counter)
        var (h2, eh) = name(h, pol, threshold, defs, counter)
        while pol <= 0 && capMul(eg.neg, eh.neg) > threshold && (eg.neg > 1 || eh.neg > 1) do
          if eg.neg >= eh.neg && eg.neg > 1 then { g2 = define(g2, pol, defs, counter); eg = atomEst }
          else { h2 = define(h2, pol, defs, counter); eh = atomEst }
        (and(g2)(h2), Est(capAdd(eg.pos, eh.pos), capMul(eg.neg, eh.neg)))
      case Or(g, h) => // pos = Π (multiplicative), neg = Σ (additive)
        var (g2, eg) = name(g, pol, threshold, defs, counter)
        var (h2, eh) = name(h, pol, threshold, defs, counter)
        while pol >= 0 && capMul(eg.pos, eh.pos) > threshold && (eg.pos > 1 || eh.pos > 1) do
          if eg.pos >= eh.pos && eg.pos > 1 then { g2 = define(g2, pol, defs, counter); eg = atomEst }
          else { h2 = define(h2, pol, defs, counter); eh = atomEst }
        (or(g2)(h2), Est(capMul(eg.pos, eh.pos), capAdd(eg.neg, eh.neg)))
      case Neg(g) =>
        val (g2, eg) = name(g, -pol, threshold, defs, counter)
        (neg(g2), Est(eg.neg, eg.pos))
      case Implies(g, h) => name(or(neg(g))(h), pol, threshold, defs, counter) // eliminate → to ¬g ∨ h
      case Iff(g, h) => // children live at both polarities; both pos and neg are multiplicative
        var (g2, eg) = name(g, 0, threshold, defs, counter)
        var (h2, eh) = name(h, 0, threshold, defs, counter)
        def ip(a: Est, b: Est): Long = capAdd(capMul(a.pos, b.neg), capMul(a.neg, b.pos))
        def in(a: Est, b: Est): Long = capAdd(capMul(a.pos, b.pos), capMul(a.neg, b.neg))
        def sz(e: Est): Long = capAdd(e.pos, e.neg)
        while relevantBig(ip(eg, eh), in(eg, eh), pol, threshold) && (sz(eg) > 2 || sz(eh) > 2) do
          if sz(eg) >= sz(eh) && sz(eg) > 2 then { g2 = define(g2, 0, defs, counter); eg = atomEst }
          else { h2 = define(h2, 0, defs, counter); eh = atomEst }
        (g2 <=> h2, Est(ip(eg, eh), in(eg, eh)))
      case Forall(x, g) => val (g2, eg) = name(g, pol, threshold, defs, counter); (forall(x, g2), eg)
      case Exists(x, g) => val (g2, eg) = name(g, pol, threshold, defs, counter); (exists(x, g2), eg)
      case `top`        => (top, Est(0, 1))
      case `bot`        => (bot, Est(1, 0))
      case atom         => (atom, atomEst)

  // ── single-pass Skolemization (fresh Skolem functions; strip ∀; α-rename) ───────────────────────

  private def skolemize(f: Expression, subst: Map[Variable, Expression], univs: List[Variable], counter: Counter): Expression =
    f match
      case And(g, h) => and(skolemize(g, subst, univs, counter))(skolemize(h, subst, univs, counter))
      case Or(g, h)  => or(skolemize(g, subst, univs, counter))(skolemize(h, subst, univs, counter))
      case Forall(x, g) => // α-rename to a fresh var (avoid capture), strip the ∀, extend the universal context
        val v = Variable(Identifier(s"sV${counter.next()}", 0), x.sort)
        skolemize(g, subst + (x -> v), if x.sort == Ind then univs :+ v else univs, counter)
      case Exists(x, g) => // fresh Skolem function over the in-scope universals; strip the ∃
        val skSort = univs.foldRight(x.sort)((u, acc) => u.sort -> acc)
        // A **Constant** (function symbol), NOT a Variable: a *nullary* Skolem (no enclosing universals) has result
        // sort `Ind`, so as a Variable it would be indistinguishable from a clause variable and the prover would
        // treat the Skolem constant as universally quantified — unsound. As a Constant it is always a function symbol.
        val sk = Constant(Identifier(s"sK${counter.next()}", 0), skSort)
        val skTerm = univs.foldLeft(sk: Expression)((acc, u) => acc(u))
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
