package lisa.automation.superposition
package ordering

import Core.*

/** Literal-selection strategies (Bachmair-Ganzinger selection) for the DISCOUNT loop, together with
  * the shared Comparator10 quality order they rank by.
  *
  * A [[LiteralSelector]] maps a clause's literals to the indices selected for inference, **one or many**, and
  * only those are used as resolution or factoring partners: by Bachmair-Ganzinger, selecting a negative literal
  * restricts a clause to it, while selecting the maximal positive ones keeps it complete. Indices are into the
  * literal array as stored, which is never reordered, so they stay valid as parent positions for reconstruction.
  * The active selector is [[Core.TermBank.selector]], consulted at clause activation. */
trait LiteralSelector:
  def select(bank: TermBank, literals: Array[Literal]): Array[Int]

/** Which [[LiteralSelector]] a strategy uses.
 *  - [[Complete]] selects a negative literal, or else every maximal literal, which are the two admissible
 *    choices. It is the default and the one to use when completeness matters.
 *  - [[FirstNegative]] selects one negative literal, but falls back to the first literal in syntactic order
 *    on an all-positive clause rather than to all maximal ones, so it is not refutation-complete.
 *  - [[BestLiteral]] always selects the single best literal, ignoring maximality, and is not complete either.
 *  The latter two are safe as portfolio members only because a complete one runs alongside them. */
enum LiteralSelection:
  case FirstNegative, BestLiteral, Complete

object LiteralSelection:
  /** Build the concrete selector for `bank` (only [[CompleteBestLiteralSelector]] needs the order). */
  def selector(kind: LiteralSelection, bank: TermBank): LiteralSelector = kind match
    case FirstNegative => FirstNegativeSelector
    case BestLiteral   => BestLiteralSelector
    case Complete      => new CompleteBestLiteralSelector(bank.order)

/** Shared empty selection (no literals -- e.g. the empty clause `□`); avoids per-call allocation. */
private[superposition] val EmptySelection: Array[Int] = Array.empty[Int]

/** Vampire's `Comparator10` quality order, without the colour key, which is not modelled here. A positive
  * result means `l1` is the more selectable literal. In decreasing priority: a negative equality, since
  * equality resolution can remove it; then the heavier literal, being more constraining; then a negative
  * literal; then a structural comparison of the atoms as a total tie-break. */
def compareLiteralQuality(bank: TermBank, l1: Literal, l2: Literal): Int =
  var c: Int = java.lang.Boolean.compare(bank.isNegativeEquality(l1), bank.isNegativeEquality(l2))
  if c != 0 then c
  else
    c = Integer.compare(bank.literalWeight(l1), bank.literalWeight(l2))
    if c != 0 then c
    else
      c = java.lang.Boolean.compare(bank.isNegative(l1), bank.isNegative(l2))
      if c != 0 then c
      else compareStructural(bank, bank.atomOf(l1), bank.atomOf(l2))

/** Selects the first negative literal, else the first literal; empty for `□`. Not BG-complete on all-positive
 *  clauses (the else-branch is a heuristic); see [[LiteralSelection]]; use [[CompleteBestLiteralSelector]] when
 *  completeness is required. */
object FirstNegativeSelector extends LiteralSelector:
  def select(bank: TermBank, literals: Array[Literal]): Array[Int] =
    if literals.isEmpty then EmptySelection
    else
      var i = 0
      while i < literals.length do
        if bank.isNegative(literals(i)) then return Array(i)
        i += 1
      Array(0)

/** Vampire's `BestLiteralSelector<Comparator10>` (its selector **1010**): rank the literals by
  * [[compareLiteralQuality]] (Comparator10 minus the colour key) and select the single greatest.
  *
  * This is **not** BG-complete: when a positive literal outweighs every negative one it is selected even though
  * negatives are present, so some refutations are unreachable. For a complete strategy use
  * [[CompleteBestLiteralSelector]] (Vampire's default selector 10); for guaranteed negative selection use
  * [[FirstNegativeSelector]]. */
object BestLiteralSelector extends LiteralSelector:
  def select(bank: TermBank, literals: Array[Literal]): Array[Int] =
    if literals.isEmpty then EmptySelection
    else
      var best = 0
      var i = 1
      while i < literals.length do
        if compareLiteralQuality(bank, literals(i), literals(best)) > 0 then best = i
        i += 1
      Array(best)

/** Vampire's default selector 10. It ranks literals by [[compareLiteralQuality]] and then selects the best
  * negative literal if one is at least as good as some maximal literal, and otherwise every maximal literal,
  * which are the two admissible choices, so it is always complete.
  *
  * Maximality comes from the shared [[Order]], so the selector and the equality inferences agree on it. That
  * also makes this class not thread-safe, since the ordering is not. */
final class CompleteBestLiteralSelector(ordering: Order) extends LiteralSelector:

  def select(bank: TermBank, literals: Array[Literal]): Array[Int] =
    val n: Int = literals.length
    if n == 0 then Array.empty[Int]
    else if n == 1 then Array(0)
    else
      val q: Array[Int] = Array.tabulate(n)(identity) // identity permutation of literal indices; sorted best-first next
      sortByQualityDesc(bank, literals, q)
      val isMax: Array[Boolean] = ordering.maximalFlags(literals)

      var singleSelected: Int = -1
      if bank.isNegative(literals(q(0))) then singleSelected = q(0)
      else
        // Walk the quality order against the (quality-ordered) maximal literals in lockstep. A
        // negative reached before the last maximal is consumed is "competitive" -> select it. If the
        // last maximal is consumed first, no competitive negative exists -> fall through to maximals.
        val maxInQ: Array[Int] = q.filter(idx => isMax(idx))
        var besti: Int = 0
        var nextMax: Int = 0
        var done: Boolean = false
        while !done && besti < n do
          if nextMax < maxInQ.length && maxInQ(nextMax) == q(besti) then
            nextMax += 1
            if nextMax == maxInQ.length then done = true
          if !done then
            besti += 1
            if besti < n && bank.isNegative(literals(q(besti))) then
              singleSelected = q(besti)
              done = true

      if singleSelected >= 0 then Array(singleSelected)
      else
        // all ordering-maximal literals (all positive here), in clause order
        var count: Int = 0
        var i = 0
        while i < n do
          if isMax(i) then count += 1
          i += 1
        val out: Array[Int] = new Array[Int](count)
        var k = 0
        i = 0
        while i < n do
          if isMax(i) then
            out(k) = i
            k += 1
          i += 1
        out

  /** Insertion-sort the index array `q` so the better literal (by [[compareLiteralQuality]]) comes first. */
  private def sortByQualityDesc(bank: TermBank, literals: Array[Literal], q: Array[Int]): Unit =
    var i = 1
    while i < q.length do
      val x: Int = q(i)
      var j = i - 1
      while j >= 0 && compareLiteralQuality(bank, literals(q(j)), literals(x)) < 0 do
        q(j + 1) = q(j)
        j -= 1
      q(j + 1) = x
      i += 1
