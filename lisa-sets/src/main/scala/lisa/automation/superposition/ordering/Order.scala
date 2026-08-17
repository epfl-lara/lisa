package lisa.automation.superposition
package ordering

import Core.*
import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap

/** The ordering the calculus runs on, layered on the term-level [[KBO]]: orientation of equality atoms, the
  * literal order and maximality, and the clause order.
  *
  * Distinct from the syntactic [[Core.compareLiterals]], which is only the canonicalisation sort key and has
  * nothing to do with the KBO. Holds one [[KBO]] and is not thread-safe for the same reason it is not. */
final class Order(val kbo: KBO):
  import Cmp.*

  private val bank: TermBank = kbo.bank

  // --- equality atoms & orientation -----------------------------------------------------------------------

  /** Orientation memo, keyed on the atom's arena offset (a stable unique key for a hash-consed term), with `-1`
    * as the "not computed" sentinel. A verdict is valid only for the KBO parameters it was computed under, and
    * those are fixed for the run: weights when a symbol is interned, precedence by the single call to
    * [[Precedence.assign]], which clears this through [[invalidate]]. */
  private val orientCache: Int2IntOpenHashMap =
    val m = new Int2IntOpenHashMap()
    m.defaultReturnValue(-1)
    m

  /** Drop every memoised orientation. Called by [[Precedence.assign]], the one thing that changes the ordering
    * after terms exist, so that a verdict taken beforehand cannot survive into the search. */
  def invalidate(): Unit = orientCache.clear()

  /** Orient an equality atom: the [[Cmp]] of its two sides under the [[KBO]] (`Gt` = lhs greater). Memoised;
    * see [[orientCache]] for why the memo does not need to watch for parameter changes. */
  def orient(atom: Term): Cmp =
    val cached: Int = orientCache.get(atom.offset)
    if cached >= 0 then Cmp.fromOrdinal(cached)
    else
      val c: Cmp = kbo.compare(bank.arg(atom, 0), bank.arg(atom, 1))
      orientCache.put(atom.offset, c.ordinal)
      c

  // --- literal order ≻_L --------------------------------------------------------------------------------

  /** The literal order, by cases: identical literals are `Eq`; on the same atom the negative literal is
    * greater; a non-equality literal is greater than any equality literal; two non-equality literals compare
    * by their atoms; two equality literals compare as the multisets `{s,t}` when positive and `{s,s,t,t}` when
    * negative, which is what makes a negative equation outrank the positive one on the same terms. Returns
    * `Inc` on genuinely unordered non-ground literals. */
  def compareLit(l1: Literal, l2: Literal): Cmp =
    if l1 == l2 then Eq
    else
      val a1: Term = bank.atomOf(l1)
      val a2: Term = bank.atomOf(l2)
      if a1 == a2 then
        // same atom, necessarily opposite polarity (l1 == l2 was handled above): the negative is greater
        if bank.isPositive(l1) then Lt else Gt
      else
        val e1: Boolean = bank.isEqualityAtom(a1)
        val e2: Boolean = bank.isEqualityAtom(a2)
        if e1 != e2 then (if e1 then Lt else Gt) // equality ranks below non-equality
        else if !e1 then kbo.compare(a1, a2) // both non-equality, distinct atoms (never `Eq`: distinct ⇒ not identical)
        else // both equality (distinct atoms): specialised same-/mixed-polarity comparison of the sides
          val s: Term = bank.arg(a1, 0); val t: Term = bank.arg(a1, 1)
          val u: Term = bank.arg(a2, 0); val v: Term = bank.arg(a2, 1)
          if bank.isPositive(l1) == bank.isPositive(l2) then compareSamePolarity(s, t, u, v)
          else if bank.isPositive(l1) then compareDiffPolarity(s, t, u, v) // l1 positive, l2 negative
          else rev(compareDiffPolarity(u, v, s, t)) //                       l1 negative, l2 positive

  /** Reverse a comparison (`Gt`↔`Lt`; `Eq`/`Inc` unchanged). */
  private def rev(c: Cmp): Cmp = c match
    case Gt => Lt
    case Lt => Gt
    case x  => x

  /** Compare two same-polarity equality literals by their side multisets. Two negatives reduce to this too,
    * since doubling both preserves the order.
    * A specialisation to two elements of the generic multiset extension. */
  private def compareSamePolarity(s: Term, t: Term, u: Term, v: Term): Cmp =
    val csu: Cmp = kbo.compare(s, u)
    if csu == Eq then kbo.compare(t, v) // cancel s,u ⇒ {t} vs {v}
    else
      val csv: Cmp = kbo.compare(s, v)
      if csv == Eq then kbo.compare(t, u) // cancel s,v ⇒ {t} vs {u}
      else
        val ctu: Cmp = kbo.compare(t, u)
        if ctu == Eq then csv // cancel t,u ⇒ {s} vs {v} = csv
        else
          val ctv: Cmp = kbo.compare(t, v)
          if ctv == Eq then csu // cancel t,v ⇒ {s} vs {u} = csu
          else dominate2(csu, csv, ctu, ctv) // nothing cancels: full {s,t} vs {u,v} multiset domination

  /** Compare a positive equality literal against a negative one, whose side multiset is doubled, which is what
    * lets a negative outrank a positive on equal terms. */
  private def compareDiffPolarity(s: Term, t: Term, u: Term, v: Term): Cmp =
    val csu: Cmp = kbo.compare(s, u); val csv: Cmp = kbo.compare(s, v)
    val ctu: Cmp = kbo.compare(t, u); val ctv: Cmp = kbo.compare(t, v)
    if csu == Eq || csv == Eq then singleVsPair(ctu, ctv) //      s cancels a copy ⇒ {t} vs {u,v}
    else if ctu == Eq || ctv == Eq then singleVsPair(csu, csv) // t cancels a copy ⇒ {s} vs {u,v}
    else dominate2(csu, csv, ctu, ctv) // nothing cancels ⇒ {s,t} vs {u,v} domination

  /** Compare a singleton `{x}` against a pair `{u,v}`, given `a = cmp(x,u)`, `b = cmp(x,v)`: `x` must beat
   *  **both** for `Gt`; it is `Lt` as soon as it ties or loses to **either** (`Lt`/`Eq`); otherwise `Inc`. */
  private inline def singleVsPair(a: Cmp, b: Cmp): Cmp =
    if a == Gt && b == Gt then Gt
    else if a == Lt || a == Eq || b == Lt || b == Eq then Lt
    else Inc

  /** Full `{s,t}` vs `{u,v}` multiset domination when nothing cancels, from the four cross-comparisons
   *  (`csu = cmp(s,u)`, `csv = cmp(s,v)`, `ctu = cmp(t,u)`, `ctv = cmp(t,v)`): `Gt` iff each of `u`,`v` is
   *  dominated by some `s`/`t`; symmetric for `Lt`; else `Inc`. */
  private inline def dominate2(csu: Cmp, csv: Cmp, ctu: Cmp, ctv: Cmp): Cmp =
    if (csu == Gt || ctu == Gt) && (csv == Gt || ctv == Gt) then Gt
    else if (csu == Lt || csv == Lt) && (ctu == Lt || ctv == Lt) then Lt
    else Inc

  // --- maximality -----------------------------------------------------------------------------------------

  /** Whether literal `i` is **maximal** in `literals`: no other literal is `≻_L`-greater (`Gt`). `Inc` never demotes. */
  def isMaximal(literals: Array[Literal], i: Int): Boolean =
    var j = 0
    while j < literals.length do
      if j != i && compareLit(literals(j), literals(i)) == Gt then return false
      j += 1
    true

  /** `res(i)`: literal `i` is maximal (no other literal is `≻_L`-greater), via [[isMaximal]] per index. For the
   *  selector, which needs every literal's verdict.*/
  def maximalFlags(literals: Array[Literal]): Array[Boolean] =
    Array.tabulate(literals.length)(isMaximal(literals, _))
