package lisa.automation.superposition

import lisa.automation.Problem
import lisa.utils.K._

import scala.collection.mutable

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

  /**
   * The kernel's logical constants: the connectives, the `∀`/`∃`/`ε` binders, `⊤`/`⊥`, and `=`. None is a user
   *  function/predicate symbol, so SInE must never treat one as a trigger.
   */
  private val LogicalConstants: Set[Expression] =
    Set(and, or, neg, implies, iff, forall, exists, epsilon, top, bot, equality)

  /**
   * The user function/predicate symbols of a hypothesis or a conjecture: every [[Constant]] that is not a
   *  [[LogicalConstants]] one, over both sides, so that every literal of a multi-literal clause
   *  `() ⊢ {l₁, l₂, …}` contributes and not just one of them.
   */
  private def symbolsOf(s: Sequent): Set[Constant] =
    val acc = mutable.HashSet.empty[Constant]
    // A shared sub-DAG (e.g. the opaque `F(x̄)` witnesses that abstraction and Skolemization reuse across many
    // atoms) must be traversed once, not re-unfolded per occurrence, or a heavily-shared expression blows up
    // exponentially. Memoise by the kernel's `uniqueNumber` (reference identity: shared occurrences are the
    // same node), across the whole sequent rather than per formula.
    val seen = mutable.HashSet.empty[Long]
    def walk(e: Expression): Unit = if seen.add(e.uniqueNumber) then
      e match
        case Application(f, a) => walk(f); walk(a) // covers connectives/quantifiers too, which are applications
        case Lambda(_, b) => walk(b) //           a `∀`/`∃`/`ε` body; the bound variable carries no symbol
        case c: Constant => if !LogicalConstants(c) then acc += c
        case _ => () //                a variable
    s.left.foreach(walk)
    s.right.foreach(walk)
    acc.toSet

  /**
   * What every part of the filter reads: the symbols of each hypothesis and of the conjecture, and how general
   * each symbol is, meaning the number of input formulas it occurs in. None of it depends on a [[SineConfig]],
   * so a run that both probes and filters walks the input once and calls [[Analysis.select]] twice.
   */
  def analyse(hypotheses: IndexedSeq[Sequent], conjecture: Sequent): Analysis =
    val hypSyms: IndexedSeq[Set[Constant]] = hypotheses.map(symbolsOf)
    val conjSyms: Set[Constant] = symbolsOf(conjecture)
    val gen = mutable.HashMap.empty[Constant, Int]
    def count(c: Constant): Unit = gen(c) = gen.getOrElse(c, 0) + 1
    hypSyms.foreach(_.foreach(count))
    conjSyms.foreach(count)
    new Analysis(hypSyms, conjSyms, gen)

  final class Analysis private[Sine] (hypSyms: IndexedSeq[Set[Constant]], conjSyms: Set[Constant], gen: collection.Map[Constant, Int]):

    /**
     * The indices (into the hypotheses) SInE keeps, seeded from the conjecture. Always keeps a symbol-less
     * hypothesis, since nothing can trigger one. Keeps **all** of them when there are fewer than
     * `cfg.minAxioms`, where there is nothing to prune.
     */
    def select(cfg: SineConfig): Set[Int] =
      if hypSyms.size < cfg.minAxioms then hypSyms.indices.toSet
      else
        // D-relation: each hypothesis is triggered by its least-general symbol(s), and any within tolerance of them.
        val dRel = mutable.HashMap.empty[Constant, mutable.ArrayBuffer[Int]]
        val kept = mutable.HashSet.empty[Int]
        hypSyms.iterator.zipWithIndex.foreach { (syms, i) =>
          if syms.isEmpty then kept += i
          else
            val limit = cfg.tolerance * syms.iterator.map(gen).min
            syms.foreach(c => if gen(c) <= limit then dRel.getOrElseUpdate(c, mutable.ArrayBuffer.empty) += i)
        }
        // BFS from the conjecture's symbols, up to `depth` rounds; each newly-kept axiom widens the frontier.
        val seenSyms = mutable.HashSet.empty[Constant] ++= conjSyms
        var frontier: Set[Constant] = conjSyms
        var round = 0
        while frontier.nonEmpty && (cfg.depth == 0 || round < cfg.depth) do
          val next = mutable.HashSet.empty[Constant]
          frontier.foreach { sym =>
            dRel
              .get(sym)
              .foreach(_.foreach { i =>
                if kept.add(i) then hypSyms(i).foreach(c => if seenSyms.add(c) then next += c)
              })
          }
          frontier = next.toSet
          round += 1
        kept.toSet

    /**
     * Should the filter run at all? The trigger is how much it would actually prune, not the axiom count,
     * since a problem with 5000 axioms whose conjecture reaches 4800 of them is not one SInE can help with.
     * Two gates: a large enough problem with a symbol in the conjecture to seed from, and a conservative probe
     * that keeps at most `keepRatioCutoff` of the axioms. How aggressively to filter is the strategy's own
     * [[SineConfig]], asked for separately.
     */
    def shouldFilter(p: Params): Boolean =
      hypSyms.size >= p.probe.minAxioms
        && conjSyms.nonEmpty
        && select(p.probe).size.toDouble / hypSyms.size <= p.keepRatioCutoff

  /**
   * Gate thresholds. Not yet calibrated against a corpus, unlike E's equivalent table.
   *
   *  @param keepRatioCutoff filter only if the probe keeps at most this fraction of the axioms.
   *  @param probe           the filter used to measure prunability. It is independent of the strategy's own
   *                         aggression, so every strategy makes the same decision on a given problem, and its
   *                         [[SineConfig.minAxioms]] is the single size floor, shared with [[Analysis.select]]
   *                         so that the gate and the selection cannot disagree.
   */
  final case class Params(keepRatioCutoff: Double = 0.9, probe: SineConfig = SineConfig(tolerance = 3.0, depth = 0))

  /**
   * The hypothesis indices to keep, or `None` when the filter should not run — the gates said it would not
   * pay, or there is no conjecture to seed from. Decided per prover invocation, on its own copy of the
   * problem, with nothing shared between strategies.
   */
  def selection(problem: Problem, cfg: SineConfig, p: Params = Params()): Option[Set[Int]] =
    problem.conjecture.flatMap { conj =>
      val a = analyse(problem.hypotheses.toIndexedSeq, conj)
      Option.when(a.shouldFilter(p))(a.select(cfg))
    }
