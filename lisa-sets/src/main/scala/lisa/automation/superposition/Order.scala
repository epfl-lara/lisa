package lisa.automation.superposition

import Core.*
import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap

/**
 * The semantic ordering the superposition calculus runs on, layered on the term-level [[KBO]]. It
 * provides, in one place shared by the literal selector and the (Phase-4) equality inferences:
 *
 *   - equality-atom recognition and **orientation** (`orient`/`maximalSide`) -- which side of an
 *     equation is `≻`-greater, hence which side superposition may rewrite from/into;
 *   - the **literal order** `≻_L` (`compareLit`): for an equality literal, the multiset extension of the
 *     KBO over its side multiset `{s,t}` (positive) / `{s,s,t,t}` (negative); for a non-equality literal,
 *     the resolution order (atoms by KBO, `¬A ≻ A` on a tie); and equality literals rank **below** any
 *     non-equality literal (Vampire's `EQ` = lowest level -- no `P(t̄)≈⊤` encoding);
 *   - literal **maximality** (`isMaximal`) and **strict** maximality (`isStrictlyMaximal`);
 *   - the **clause order** `≻_C` (`compareClause`), the multiset extension of `≻_L`.
 *
 * This is entirely distinct from the *syntactic* [[Core.compareLiterals]] / [[Core.compareStructural]]
 * (the canonicalisation sort key), which is unrelated to the (semantic) KBO and is left untouched.
 *
 * Holds one [[KBO]], shared with its callers. Like the KBO (which reuses mutable accumulator state,
 * reset per compare) it is **not thread-safe**; all comparisons are sequential in the single-threaded
 * DISCOUNT loop.
 */
final class Order(val kbo: KBO):
  import Cmp.*

  private val bank: TermBank = kbo.bank

  // --- equality atoms & orientation -----------------------------------------------------------

  /** Whether `atom` is an equality atom `s = t` (headed by [[Core.EqualitySymbol]], arity 2). */
  def isEqualityAtom(atom: Term): Boolean =
    !bank.isVar(atom) && bank.headSymbol(atom) == EqualitySymbol

  /**
   * Orientation memo, keyed on the equality atom's arena [[Core.offset]] (a stable, unique `Int` for a
   * hash-consed term), storing the [[Cmp]] ordinal; `-1` is the "not yet computed" sentinel. Same
   * primitive-int-map shape as the bank's own tables — no boxing. Safe to cache because the KBO
   * weights/precedence are fixed once the problem signature is set.
   * See `PossibleOptimizations.md` for caching orientation on the atom record itself (E/Vampire style).
   */
  private val orientCache: Int2IntOpenHashMap =
    val m = new Int2IntOpenHashMap()
    m.defaultReturnValue(-1)
    m

  /** Orient an equality atom: the [[Cmp]] of its two sides under the [[KBO]] (`Gt` = lhs greater). Memoised. */
  def orient(atom: Term): Cmp =
    val cached: Int = orientCache.get(atom.offset)
    if cached >= 0 then Cmp.fromOrdinal(cached)
    else
      val c: Cmp = kbo.compare(bank.arg(atom, 0), bank.arg(atom, 1))
      orientCache.put(atom.offset, c.ordinal)
      c

  /** The strictly-`≻`-greater side of an equality atom, or `None` when the sides are `Eq`/`Inc`. */
  def maximalSide(atom: Term): Option[Term] =
    orient(atom) match
      case Gt => Some(bank.arg(atom, 0))
      case Lt => Some(bank.arg(atom, 1))
      case _  => None

  // --- literal order ≻_L -----------------------------------------------------------------------

  /**
   * The equality-aware literal order. In decreasing precedence of the case analysis:
   *   - identical literals → `Eq`;
   *   - same atom, opposite polarity → the **negative** literal is greater (`s ≠ t ≻ s = t`);
   *   - equality vs non-equality → the non-equality literal is greater (equality is the lowest level);
   *   - both non-equality (distinct atoms) → compare the atoms by the [[KBO]];
   *   - both equality → multiset extension of the KBO over the side multisets `{s,t}` (positive) /
   *     `{s,s,t,t}` (negative) — the standard Bachmair-Ganzinger encoding, so a negative equality
   *     outranks the positive one on the same terms (the duplicated sides tip the multiset comparison).
   *
   * Returns `Inc` on genuinely unordered non-ground literals. On equality-free literals this coincides
   * with the resolution literal order previously computed inside the selector.
   *
   * The `{s,t}` / `{s,s,t,t}` encoding and the equivalent `{{s},{t}}` / `{{s,t}}` multiset-of-multisets form
   * used by E (Vampire's `Ordering_Equality.cpp` is a third, sign-blind variant) all coincide on ground
   * literals — where completeness is defined — and differ only on rare non-ground positive/negative pairs.
   * We use the doubled form for its directness and its "negative outranks positive" property.
   */
  def compareLit(l1: Literal, l2: Literal): Cmp =
    if l1 == l2 then Eq
    else
      val a1: Term = bank.atomOf(l1)
      val a2: Term = bank.atomOf(l2)
      if a1 == a2 then
        // same atom, necessarily opposite polarity (l1 == l2 was handled above): the negative is greater
        if bank.isPositive(l1) then Lt else Gt
      else
        val e1: Boolean = isEqualityAtom(a1)
        val e2: Boolean = isEqualityAtom(a2)
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

  /**
   * Compare two **same-polarity** equality literals by the 2-element side multisets `{s,t}` vs `{u,v}`.
   * (Negative/negative reduces to this too: doubling both sides is order-preserving.) A two-element
   * specialisation of [[termMultisetCompare]]: since each multiset has size 2, cancelling one
   * common side (by hash-cons identity, i.e. a `kbo` `Eq`) leaves a **singleton-vs-singleton** comparison,
   * so a single `kbo.compare` of the survivors is the whole answer; only when nothing cancels do we run the
   * full 2×2 domination. Computes **at most four** `kbo.compare`s — fewer when a side cancels. `Eq` when the
   * equations coincide (up to symmetry). (Cancellation is order-independent: two equal sides can only both
   * match one target side if the targets themselves coincide, giving equal survivors either way.)
   */
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

  /**
   * Compare a **positive** equality literal `{s,t}` against a **negative** one, whose Bachmair-Ganzinger
   * side multiset is doubled to `{u,u,v,v}` (the doubling is what lets a negative outrank a positive on
   * equal terms). Returns the comparison of the positive against the negative.
   *
   * Because the negative is doubled, cancelling **one** positive side (an `Eq`) still leaves the other of
   * `u`,`v` present, so it reduces to `{survivor} vs {u,v}` — a singleton-vs-pair whose verdict is
   * [[singleVsPair]] (multiplicity is irrelevant for domination). The "negative wins ties" effect and the
   * "both sides cancel ⇒ negative greater" case both fall out of `singleVsPair`'s `Eq ⇒ Lt` rule. Only when
   * nothing cancels is it a genuine `{s,t}` vs `{u,v}` domination (doubling then irrelevant). `Eq` is
   * impossible (a 2- and a 4-element multiset never coincide).
   */
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

  // --- maximality --------------------------------------------------------------------------------

  /** Whether literal `i` is **maximal** in `literals`: no other literal is `≻_L`-greater (`Gt`). `Inc` never demotes. */
  def isMaximal(literals: Array[Literal], i: Int): Boolean =
    var j = 0
    while j < literals.length do
      if j != i && compareLit(literals(j), literals(i)) == Gt then return false
      j += 1
    true

  /** Whether literal `i` is **strictly maximal**: no other literal is `≻_L`-greater-or-equal (`Gt` or `Eq`). */
  def isStrictlyMaximal(literals: Array[Literal], i: Int): Boolean =
    var j = 0
    while j < literals.length do
      if j != i then
        val c: Cmp = compareLit(literals(j), literals(i))
        if c == Gt || c == Eq then return false
      j += 1
    true

  /** `res(i)`: literal `i` is maximal (no other literal is `≻_L`-greater), via [[isMaximal]] per index. For the
   *  selector. `Array.tabulate[Boolean]` is specialised (no boxing), so the hot path is unaffected. */
  def maximalFlags(literals: Array[Literal]): Array[Boolean] =
    Array.tabulate(literals.length)(isMaximal(literals, _))

  // --- clause order ≻_C --------------------------------------------------------------------------

  /**
   * The clause order: multiset extension of `≻_L` over the two clauses' literal multisets. `Gt` if
   * `c1 ≻_C c2`, `Lt` if `c2 ≻_C c1`, `Eq` if the literal multisets are `≻_L`-equal, `Inc` otherwise.
   * Consumed by superposition's premise-comparison gate and demodulation's redundancy check.
   */
  def compareClause(c1: Clause, c2: Clause): Cmp =
    literalMultisetCompare(c1.literals, c2.literals)

  // --- multiset extension helpers ----------------------------------------------------------------

  /**
   * Multiset extension of a strict order over two multisets `m1`, `m2`: cancel elements the two share
   * (`cancels`, an equivalence — hash-cons identity for terms, `≻_L`-`Eq` for literals so a symmetric
   * `s = t` / `t = s` pair cancels, not just syntactically-identical ones), then `m1 >_mul m2` iff every
   * leftover of `m2` is `gt` some leftover of `m1`. Both domination tests can fail → `Inc` (correct for a
   * partial order). Multisets are tiny (literal counts 1–3), so the `forall`/`exists` closures dominate cost.
   */
  private def multisetCompare[A](m1: Array[A], m2: Array[A])(cancels: (A, A) => Boolean)(gt: (A, A) => Boolean): Cmp =
    val used2: Array[Boolean] = new Array[Boolean](m2.length)
    val rem1 = scala.collection.mutable.ArrayBuffer.empty[A]
    var i = 0
    while i < m1.length do
      val x: A = m1(i)
      var matched = false
      var j = 0
      while j < m2.length && !matched do
        if !used2(j) && cancels(x, m2(j)) then { used2(j) = true; matched = true }
        j += 1
      if !matched then rem1 += x
      i += 1
    val rem2 = scala.collection.mutable.ArrayBuffer.empty[A]
    var k = 0
    while k < m2.length do
      if !used2(k) then rem2 += m2(k)
      k += 1
    if rem1.isEmpty && rem2.isEmpty then Eq
    else if rem1.isEmpty then Lt
    else if rem2.isEmpty then Gt
    else if rem2.forall(y => rem1.exists(x => gt(x, y))) then Gt
    else if rem1.forall(x => rem2.exists(y => gt(y, x))) then Lt
    else Inc

  /** Multiset extension of the [[KBO]] on two term multisets: the generic reference the specialised
   *  [[compareSamePolarity]] / [[compareDiffPolarity]] are tested against (those avoid this loop's redundant
   *  comparisons on the duplicated negative sides). Package-visible so the property test can use it. */
  private[superposition] def termMultisetCompare(m1: Array[Term], m2: Array[Term]): Cmp =
    multisetCompare(m1, m2)(_ == _)((x, y) => kbo.compare(x, y) == Gt)

  /** Multiset extension of `≻_L` on two literal multisets — what [[compareClause]] uses. */
  private def literalMultisetCompare(m1: Array[Literal], m2: Array[Literal]): Cmp =
    multisetCompare(m1, m2)((x, y) => compareLit(x, y) == Eq)((x, y) => compareLit(x, y) == Gt)
