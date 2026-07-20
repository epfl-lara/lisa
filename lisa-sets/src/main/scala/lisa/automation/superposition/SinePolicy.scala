package lisa.automation.superposition

import lisa.utils.K.*
import lisa.automation.clausification.Clausification

/**
 * The SInE **activation policy**: decides, for a *single* prover invocation, whether the strategy's SInE filter
 * ([[Sine]]) should actually fire. This is a purely local decision — each invocation runs it independently on its
 * own copy of the problem; nothing is shared or precomputed across strategies. It sits above the pure mechanism
 * in [[Sine]] and below the per-strategy filter config in [[Strategy]].
 *
 * The trigger is **actual prunability**, not a raw axiom count: a 5000-axiom problem whose conjecture touches
 * 4800 axioms is *not* a SInE problem, while a 300-axiom one touching 20 *is* — and raw count cannot tell them
 * apart. Because SInE is cheap (symbol bookkeeping + BFS), we run a conservative probe and read off how much it
 * prunes. Three gates, checked in order:
 *
 *   1. **Prerequisites** — there is a conjecture with at least one symbol to seed from, and the axiom count is at
 *      least [[Params.minAxioms]] (below that a good prover just chews through them; filtering only risks harm).
 *      The floor is set conservatively (400): SInE earns its keep on the thousand-plus-axiom SUMO/Mizar theories,
 *      not on medium problems where dropping a needed axiom costs more than the search it would save.
 *   2. **Prunability** — a conservative probe ([[Params.probe]]) keeps at most [[Params.keepRatioCutoff]] of the
 *      axioms, i.e. it drops a meaningful fraction. If it barely prunes, running filtered ≈ running unfiltered.
 *   3. **Aggression** — supplied per strategy by its own [[SineConfig]] tolerance/depth (applied by the caller
 *      via [[Sine.select]]); the seven SInE-active strategies vary it for portfolio diversity.
 *
 * Gates 1–2 are this object; gate 3 is the strategy's filter. Dropping an axiom keeps the run **sound** (a
 * refutation over a subset is still a refutation) but **incomplete** (a saturation is not a valid
 * (Counter)Satisfiable verdict) — hence at least one portfolio strategy runs unfiltered as the completeness /
 * Satisfiable-verdict backstop (see [[Strategy.portfolio]]).
 */
object SinePolicy:

  /** Gate thresholds. Placeholders — calibrate on large-theory TPTP (CSR/SUMO, MPTP) before CASC; E learned the
   *  equivalent table from a corpus.
   *
   *  @param minAxioms       gate-1 floor: below this many axioms, never filter.
   *  @param keepRatioCutoff gate-2: filter only if the probe keeps ≤ this fraction (drops ≥ `1 - cutoff`).
   *  @param probe           the conservative filter used to *measure* prunability (independent of the strategy's
   *                         own aggression, so all strategies make the same gate-1/2 call on a given problem).
   */
  final case class Params(
      minAxioms: Int = 400,
      keepRatioCutoff: Double = 0.9,
      probe: SineConfig = SineConfig(tolerance = 3.0, depth = 0, minAxioms = 0))

  /**
   * Gates 1–2: should this invocation actually run its SInE filter? `hypotheses`/`conjecture` are the
   * pre-clausification formulas (the same ones [[Sine.selectIndices]] consumes).
   */
  def shouldFilter(hypotheses: IndexedSeq[Expression], conjecture: Expression, p: Params = Params()): Boolean =
    hypotheses.size >= p.minAxioms                                   // gate 1a: enough axioms to be worth it
      && Sine.symbolsOf(conjecture).nonEmpty                        // gate 1b: a symbol to seed the BFS from
      && {                                                          // gate 2: does a conservative probe prune?
        val kept = Sine.selectIndices(hypotheses, conjecture, p.probe)
        kept.size.toDouble / hypotheses.size <= p.keepRatioCutoff
      }

  /** Convenience over a [[Clausification.Problem]]: true iff the gates pass for its hypotheses/conjecture. */
  def shouldFilter(problem: Clausification.Problem, p: Params): Boolean =
    problem.conjecture match
      case Some(conj) => shouldFilter(problem.hypotheses.toIndexedSeq.map(_.right.head), conj.right.head, p)
      case None       => false
