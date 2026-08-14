package lisa.automation.superposition

import Core.*

/**
 * Literal-selection strategies (Bachmair-Ganzinger selection) for the DISCOUNT loop, together with
 * the shared Comparator10 quality order they rank by.
 *
 * A [[LiteralSelector]] maps a clause's literals to the indices selected for inference -- **one or
 * many**. Only selected literals are used as resolution / factoring partners: by Bachmair-Ganzinger,
 * selecting a negative literal restricts a clause to that literal, while selecting (maximal) positive
 * literals keeps it complete. Indices are into the literal array as stored, which is never reordered,
 * so they remain valid as parent positions for proof reconstruction. The active selector is held in
 * [[Core.TermBank.selector]] and consulted at clause activation.
 */
trait LiteralSelector:
  def select(bank: TermBank, literals: Array[Literal]): Array[Int]

/** Which [[LiteralSelector]] a strategy uses: a portfolio axis.
 *  - [[Complete]] is BG-complete: it selects a negative literal, else **all** ordering-maximal literals (the
 *    only BG-admissible choices). This is the default and the one to use when completeness matters.
 *  - [[FirstNegative]] is BG-admissible *only* on clauses that have a negative literal (it selects one such
 *    literal). On an all-positive clause it falls back to the first literal in stored (syntactic) order rather
 *    than to all maximal literals, so it is a **heuristic, not refutation-complete in general**. (Every complete
 *    selector in Vampire and E instead uses *all maximal* literals in the no-negative case.)
 *  - [[BestLiteral]] is the incomplete greedy variant (Vampire's 1010): a single best literal, ignoring
 *    maximality: faster on many problems but not refutation-complete.
 *  `FirstNegative`/`BestLiteral` are safe as portfolio slices only because a `Complete` slice runs alongside. */
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

/**
 * Vampire's `Comparator10` quality order on literals, with the `ColoredFirst` key dropped (colours
 * are not modelled here). A **positive** result means `l1` is the *better* (more selectable) literal;
 * in decreasing priority:
 *   1. NegativeEquality -- a negative equality `s ≠ t` is preferred (productive, removed by ER);
 *   2. MaximalSize      -- larger literal weight (more constraining ⇒ fewer, sharper inferences);
 *   3. Negative         -- negative over positive;
 *   4. LexComparator    -- a structural comparison of the atoms, a total tie-break.
 * Shared by [[BestLiteralSelector]] (selector 1010) and [[CompleteBestLiteralSelector]] (selector 10).
 */
def compareLiteralQuality(bank: TermBank, l1: Literal, l2: Literal): Int =
  var c: Int = java.lang.Boolean.compare(isNegativeEquality(bank, l1), isNegativeEquality(bank, l2))
  if c != 0 then c
  else
    c = Integer.compare(bank.literalWeight(l1), bank.literalWeight(l2))
    if c != 0 then c
    else
      c = java.lang.Boolean.compare(bank.isNegative(l1), bank.isNegative(l2))
      if c != 0 then c
      else compareStructural(bank, bank.atomOf(l1), bank.atomOf(l2))

/** Whether `l` is a negative equality literal `s ≠ t` (atom headed by [[Core.EqualitySymbol]], arity 2). */
def isNegativeEquality(bank: TermBank, l: Literal): Boolean =
  if !bank.isNegative(l) then false
  else
    val a: Term = bank.atomOf(l)
    !bank.isVar(a) && bank.headSymbol(a) == EqualitySymbol && bank.arity(a) == 2

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

/**
 * Vampire's `BestLiteralSelector<Comparator10>` (its selector **1010**): rank the literals by
 * [[compareLiteralQuality]] (Comparator10 minus the colour key) and select the single greatest.
 *
 * This is **not** BG-complete: when a positive literal outweighs every negative one it is selected even though
 * negatives are present, so some refutations are unreachable. For a complete strategy use
 * [[CompleteBestLiteralSelector]] (Vampire's default selector 10); for guaranteed negative selection use
 * [[FirstNegativeSelector]].
 */
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

/**
 * Vampire's **default** selector 10, `CompleteBestLiteralSelector<Comparator10>`: the BG-complete
 * best-literal selector. It ranks literals by [[compareLiteralQuality]] (Comparator10 with the colour
 * key dropped) and then enforces completeness using the term ordering [[kbo]]:
 *
 *   - if the best-quality literal is negative, select just it;
 *   - otherwise, scanning in quality order, if a negative literal is at least as good (by quality) as
 *     some ordering-maximal literal, select the best such negative; else select **all** of the
 *     ordering-maximal literals (which are then necessarily all positive).
 *
 * Selecting a single negative literal, or all maximal literals when no negative is selected, are the
 * two Bachmair-Ganzinger-admissible choices, so the selection is always complete -- unlike the
 * incomplete [[BestLiteralSelector]] (selector 1010), which shares the same comparator but always
 * picks just the single best literal.
 *
 * Literal maximality is delegated to the shared [[Order]] (`ordering.maximalFlags`), the
 * equality-aware literal order `≻_L`: for an equality literal it is the multiset extension of the KBO
 * over the equation sides, for the rest the resolution order (atoms by KBO, `¬A ≻ A` on a tie), with
 * equality ranked below non-equality. The selector and the equality inferences therefore share one
 * order (and one KBO).
 *
 * Because the [[Order]]'s [[KBO]] reuses mutable accumulator state, this selector -- like the
 * ordering itself -- is not thread-safe.
 */
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
