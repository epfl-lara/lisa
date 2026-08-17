package lisa.automation.superposition

import Core.*
import lisa.automation.superposition.ordering.*
import lisa.automation.superposition.index.*

/**
 * Reference definitions the tests check the engine against, which the engine itself does not use.
 *
 * Each of these states a definition in its plainest form: the clause order as a multiset extension, strict
 * maximality as "no other literal is greater or equal", the greater side of an equation as an `Option`. The
 * engine computes the same things in specialised or allocation-free ways -- the inference rules branch on the
 * `Cmp` from `Order.orient` rather than unwrapping an `Option`, and `compareSamePolarity`/`compareDiffPolarity`
 * cancel sides by hand instead of running the generic multiset loop. Testing the specialisations against these
 * is the point of having both.
 *
 * They live here rather than in `ordering/Order.scala`, `index/FeatureVector.scala` and
 * `index/Fingerprint.scala`, where they were labelled "test oracle, not engine API" and interleaved with live
 * code. A reader of a production file should not have to work out which half of it runs. Everything below uses
 * only the public API of what it tests, so nothing was weakened to make the move.
 *
 * They are extension methods so that the call sites read as they did: `order.compareClause(c1, c2)`,
 * `perm.vectorOf(bank, c)`.
 */
object Oracles:

  extension (order: Order)

    /** The strictly-`≻`-greater side of an equality atom, or `None` when the sides are `Eq`/`Inc`. The rules
      * read [[Order.orient]] and branch on the `Cmp` instead, rather than allocating an `Option` per query. */
    def maximalSide(atom: Term): Option[Term] =
      val bank: TermBank = order.kbo.bank
      order.orient(atom) match
        case Cmp.Gt => Some(bank.arg(atom, 0))
        case Cmp.Lt => Some(bank.arg(atom, 1))
        case _      => None

    /** Whether literal `i` is **strictly maximal**: no other literal is `≻_L`-greater-or-equal. The engine's
      * selection uses `Order.isMaximal`, the non-strict form, which is on its path. */
    def isStrictlyMaximal(literals: Array[Literal], i: Int): Boolean =
      var j = 0
      while j < literals.length do
        if j != i then
          val c: Cmp = order.compareLit(literals(j), literals(i))
          if c == Cmp.Gt || c == Cmp.Eq then return false
        j += 1
      true

    /** The clause order `≻_C`, the multiset extension of the literal order. The loop never needs it: its
      * conditions compare terms directly. It is the reference for the redundancy criteria that will. */
    def compareClause(c1: Clause, c2: Clause): Cmp =
      multisetCompare(c1.literals, c2.literals)((x, y) => order.compareLit(x, y) == Cmp.Eq)((x, y) =>
        order.compareLit(x, y) == Cmp.Gt)

    /** Multiset extension of the [[KBO]] on two term multisets: the generic reference that `Order`'s
      * specialised two-element equality-literal comparisons are checked against. */
    def termMultisetCompare(m1: Array[Term], m2: Array[Term]): Cmp =
      multisetCompare(m1, m2)(_ == _)((x, y) => order.kbo.compare(x, y) == Cmp.Gt)

  extension (perm: Permutation)

    /** A freshly-allocated copy of `c`'s feature vector. The index fills a reused buffer via
      * `Permutation.fillVector` instead, which is why this convenience is not needed in production. */
    def vectorOf(bank: TermBank, c: Clause): Array[Int] =
      val out = new Array[Int](perm.length)
      perm.fillVector(bank, c, out)
      out

  /** The fingerprint of `t` under `trie`'s scheme, in a fresh array, which is what a test wants in order to
    * compare two of them. The index fills its own reused buffer instead, so the allocating form lives here. */
  def fingerprintOf(bank: TermBank, t: Term, trie: SampleTrie): Array[Int] =
    val fp = new Array[Int](trie.length)
    trie.fingerprintInto(bank, t, fp)
    fp

  /**
   * Multiset extension of a strict order over two multisets `m1`, `m2`: cancel the elements the two share
   * (`cancels`, an equivalence -- hash-cons identity for terms, `≻_L`-`Eq` for literals, so that a symmetric
   * `s = t` / `t = s` pair cancels and not only syntactically identical ones), then `m1 >_mul m2` iff every
   * leftover of `m2` is `gt` some leftover of `m1`. Both domination tests can fail, giving `Inc`, which is
   * correct for a partial order.
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
    if rem1.isEmpty && rem2.isEmpty then Cmp.Eq
    else if rem1.isEmpty then Cmp.Lt
    else if rem2.isEmpty then Cmp.Gt
    else if rem2.forall(y => rem1.exists(x => gt(x, y))) then Cmp.Gt
    else if rem1.forall(x => rem2.exists(y => gt(y, x))) then Cmp.Lt
    else Cmp.Inc
