package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K.*
import lisa.automation.clausification.Clausification

/**
 * Configuration of the SInE axiom filter. It is sound but incomplete: dropping hypotheses can only make an
 * unsatisfiable set satisfiable, so a refutation stays valid but a saturation is no longer a satisfiability
 * verdict. The reference implementations are E's `ccl_sine.c` and Vampire's `SineUtils.cpp`.
 *
 * @param tolerance a symbol whose generality is within this factor of the least general one in a formula also
 *                  triggers it. `1.0` keeps only the rarest, which is the most aggressive setting.
 * @param depth     rounds of search outward from the goal; `0` is the full closure.
 * @param minAxioms below this many hypotheses, keep everything.
 */
final case class SineConfig(tolerance: Double = 3.0, depth: Int = 0, minAxioms: Int = 500)

object Sine:

  /** The kernel's logical constants: the connectives, the `∀`/`∃`/`ε` binders, `⊤`/`⊥`, and `=`. None is a user
   *  function/predicate symbol, so SInE must never treat one as a trigger. */
  private val LogicalConstants: Set[Expression] =
    Set(and, or, neg, implies, iff, forall, exists, epsilon, top, bot, equality)

  /** The user function/predicate symbols in a formula: every [[Constant]] that is not a [[LogicalConstants]] one.
   *  Used by [[shouldFilter]] for the "conjecture has a symbol to seed from" gate. */
  private[superposition] def symbolsOf(e: Expression): Set[Constant] =
    val acc = mutable.HashSet.empty[Constant]
    // A shared sub-DAG (e.g. the opaque `F(x̄)` witnesses that abstraction and Skolemization reuse across many atoms)
    // must be traversed once, not re-unfolded per occurrence, or a heavily-shared expression blows up
    // exponentially. Memoise by the kernel's `uniqueNumber` (reference identity: shared occurrences are the same node).
    val seen = mutable.HashSet.empty[Long]
    def walk(e: Expression): Unit = if seen.add(e.uniqueNumber) then e match
      case Application(f, a) => walk(f); walk(a) // covers connectives/quantifiers too, which are applications
      case Lambda(_, b)      => walk(b) //           a `∀`/`∃`/`ε` body; the bound variable carries no symbol
      case c: Constant       => if !LogicalConstants(c) then acc += c
      case _                 => () //                a variable
    walk(e)
    acc.toSet

  /** Fold a hypothesis sequent's formulas (left ∪ right) into one expression for symbol extraction, so SInE sees
   *  *every* literal of a multi-literal CNF hypothesis (`() ⊢ {l₁, l₂, …}`) or a two-sided sequent, not just
   *  `right.head`. The connective is immaterial ([[symbolsOf]] ignores it and walks both sides); an empty sequent
   *  yields `⊤` (no symbols). */
  private[superposition] def sequentFormula(s: Sequent): Expression =
    (s.left.iterator ++ s.right.iterator).reduceOption((a, b) => and(a)(b)).getOrElse(top)

  /** The indices (into `hypotheses`) SInE keeps, seeded from `conjecture`. Always keeps symbol-less hypotheses.
    * Keeps **all** hypotheses when there are fewer than `cfg.minAxioms` (nothing to prune). */
  def selectIndices(hypotheses: IndexedSeq[Expression], conjecture: Expression, cfg: SineConfig): Set[Int] =
    if hypotheses.size < cfg.minAxioms then hypotheses.indices.toSet
    else
      val hypSyms: IndexedSeq[Set[Constant]] = hypotheses.map(symbolsOf)
      val conjSyms: Set[Constant] = symbolsOf(conjecture)

      // generality(sym) = number of input formulas (hypotheses + conjecture) containing it
      val gen = mutable.HashMap.empty[Constant, Int].withDefaultValue(0)
      hypSyms.foreach(_.foreach(c => gen(c) += 1))
      conjSyms.foreach(c => gen(c) += 1)

      // D-relation: each hypothesis is triggered by its least-general symbol(s), and any within tolerance of them.
      val dRel = mutable.HashMap.empty[Constant, mutable.ArrayBuffer[Int]]
      val symbolless = mutable.ArrayBuffer.empty[Int]
      hypSyms.iterator.zipWithIndex.foreach { (syms, i) =>
        if syms.isEmpty then symbolless += i
        else
          val limit = cfg.tolerance * syms.iterator.map(gen).min
          syms.foreach(c => if gen(c) <= limit then dRel.getOrElseUpdate(c, mutable.ArrayBuffer.empty) += i)
      }

      // BFS from the conjecture's symbols, up to `depth` rounds; each newly-kept axiom widens the frontier.
      val kept = mutable.HashSet.empty[Int] ++= symbolless
      val seenSyms = mutable.HashSet.empty[Constant] ++= conjSyms
      var frontier: Set[Constant] = conjSyms
      var round = 0
      while frontier.nonEmpty && (cfg.depth == 0 || round < cfg.depth) do
        val next = mutable.HashSet.empty[Constant]
        frontier.foreach { sym =>
          dRel.get(sym).foreach(_.foreach { i =>
            if kept.add(i) then hypSyms(i).foreach(c => if seenSyms.add(c) then next += c)
          })
        }
        frontier = next.toSet
        round += 1
      kept.toSet

  /** Prune a [[Clausification.Problem]]'s hypotheses by SInE; returns it unchanged when there is no conjecture. */
  def select(problem: Clausification.Problem, cfg: SineConfig): Clausification.Problem =
    problem.conjecture match
      case Some(conj) =>
        val hyps = problem.hypotheses.toIndexedSeq
        val keep = selectIndices(hyps.map(sequentFormula), sequentFormula(conj), cfg)
        Clausification.Problem(hyps.zipWithIndex.collect { case (h, i) if keep(i) => h }, problem.conjecture, problem.frozen)
      case None => problem

  // ── whether to filter at all ──────────────────────────────────────────────────────────────────────
  //
  // Decided per prover invocation, on its own copy of the problem, with nothing shared between strategies.
  // The trigger is how much the filter would actually prune, not the axiom count, since a problem with 5000
  // axioms whose conjecture reaches 4800 of them is not one SInE can help with. Two gates are checked here:
  // that there is a conjecture to seed from and at least `minAxioms` axioms, and that a conservative probe
  // keeps at most `keepRatioCutoff` of them. The third gate, how aggressively to filter, is the strategy's
  // own [[SineConfig]].

  /** Gate thresholds. Not yet calibrated against a corpus, unlike E's equivalent table.
   *
   *  @param keepRatioCutoff filter only if the probe keeps at most this fraction of the axioms.
   *  @param probe           the filter used to measure prunability. It is independent of the strategy's own
   *                         aggression, so every strategy makes the same decision on a given problem, and its
   *                         [[SineConfig.minAxioms]] is the single size floor, shared with [[selectIndices]]
   *                         so that the gate and the selection cannot disagree.
   */
  final case class Params(
      keepRatioCutoff: Double = 0.9,
      probe: SineConfig = SineConfig(tolerance = 3.0, depth = 0))

  /** Should this invocation actually run its filter? `hypotheses`/`conjecture` are the pre-clausification
    * formulas, the same ones [[selectIndices]] consumes. */
  def shouldFilter(hypotheses: IndexedSeq[Expression], conjecture: Expression, p: Params = Params()): Boolean =
    hypotheses.size >= p.probe.minAxioms             // gate 1a: enough axioms to be worth it (the single floor)
      && symbolsOf(conjecture).nonEmpty              // gate 1b: a symbol to seed the search from
      && {                                           // gate 2: does a conservative probe prune?
        val kept = selectIndices(hypotheses, conjecture, p.probe)
        kept.size.toDouble / hypotheses.size <= p.keepRatioCutoff
      }

  /** Convenience over a [[Clausification.Problem]]: true iff the gates pass for its hypotheses/conjecture. */
  def shouldFilter(problem: Clausification.Problem, p: Params): Boolean =
    problem.conjecture match
      case Some(conj) => shouldFilter(problem.hypotheses.toIndexedSeq.map(sequentFormula), sequentFormula(conj), p)
      case None       => false
