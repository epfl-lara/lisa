package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K.*
import lisa.automation.clausification.Clausification

/**
 * SInE (Sumo INference Engine) axiom selection: a **preprocessing** relevance filter for large axiom sets, run
 * *before* clausification. Seeded from the conjecture, it keeps only the hypotheses transitively reachable through
 * the trigger ("D") relation, and deletes the rest. See [[PortfolioStrategy.md]] §implications and E's `ccl_sine.c`
 * / Vampire's `SineUtils.cpp`.
 *
 * It is an **incomplete** transformation (it can drop a needed axiom), but **sound** — removing hypotheses can
 * only turn an unsatisfiable set satisfiable (⇒ we fail to refute), never produce a spurious refutation. Hence it
 * is used only in dedicated portfolio slices, alongside complete strategies.
 *
 * @param tolerance a symbol whose generality ≤ `tolerance × (least generality in the formula)` also triggers it
 *                  (E's "benevolence"). `1.0` = strict/aggressive (rarest only); higher keeps more (safer).
 * @param depth     BFS rounds outward from the goal; `0` = unlimited (full closure), `1` = most aggressive.
 * @param minAxioms below this many hypotheses there is nothing worth pruning — keep everything.
 */
final case class SineConfig(tolerance: Double = 3.0, depth: Int = 0, minAxioms: Int = 32)

object Sine:

  /** The kernel identifier of the equality predicate — excluded from SInE symbols (it is universal). */
  private val EqualityName = "="

  /** The user function/predicate symbols occurring in a formula: every [[Constant]] that is not a logical
   *  connective, a quantifier binder, a variable, or `=`. (Connectives/binders are peeled by the extractors;
   *  equality is excluded by name; variables carry no symbol.) Exposed to [[SinePolicy]] for the gate-1
   *  "conjecture has a symbol to seed from" check. */
  private[superposition] def symbolsOf(e: Expression): Set[Constant] =
    val acc = mutable.HashSet.empty[Constant]
    def formula(e: Expression): Unit = e match
      case And(g, h)     => formula(g); formula(h)
      case Or(g, h)      => formula(g); formula(h)
      case Neg(g)        => formula(g)
      case Implies(g, h) => formula(g); formula(h)
      case Iff(g, h)     => formula(g); formula(h)
      case Forall(_, b)  => formula(b)
      case Exists(_, b)  => formula(b)
      case `top` | `bot` => ()
      case _             => term(e) // a predicate atom or an equality
    def term(t: Expression): Unit = t match
      case Application(f, a) => term(f); term(a)
      case Lambda(_, b)      => term(b)
      case c: Constant       => if c.id.name != EqualityName then acc += c
      case _                 => () // a variable
    formula(e)
    acc.toSet

  /**
   * The indices (into `hypotheses`) SInE keeps, seeded from `conjecture`. Always keeps symbol-less hypotheses.
   * Keeps **all** hypotheses when there are fewer than `cfg.minAxioms` (nothing to prune).
   */
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
        val keep = selectIndices(hyps.map(_.right.head), conj.right.head, cfg)
        Clausification.Problem(hyps.zipWithIndex.collect { case (h, i) if keep(i) => h }, problem.conjecture, problem.frozen)
      case None => problem
