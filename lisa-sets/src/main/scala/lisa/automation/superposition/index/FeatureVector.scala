package lisa.automation.superposition
package index

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.objects.ObjectOpenHashSet

import Core.*

/** Feature-vector indexing for clause **subsumption**, as in Vampire, Prover9 and E. A clause maps to a vector
  * of monotone features (`c subsumes d ⇒ f(c) ≤ f(d)`), so a subsumer's vector is componentwise `≤` its
  * subsumee's, and the candidates are a `≤`/`≥`-cone descent of a trie keyed by those vectors, which
  * `Subsumption.subsumes` then verifies. [[Permutation]] picks the features; [[FeatureVectorIndex]] is the trie. */
object FeatureVector:
  /** Feature source sentinel: the slot holds the clause's positive-literal count. */
  inline val PosCount = -1

  /** Feature source sentinel: the slot holds the clause's negative-literal count. */
  inline val NegCount = -2

  /** Binary entropy: a symbol present in a fraction `p` of the clauses splits them best at `p = 0.5` (score 1)
   *  and not at all at `p ∈ {0,1}` (score 0). */
  def binaryEntropy(p: Double): Double =
    if p <= 0.0 || p >= 1.0 then 0.0
    else
      val ln2 = 0.6931471805599453
      -(p * math.log(p) + (1.0 - p) * math.log(1.0 - p)) / ln2

/** The chosen features, one per trie level: a literal-count, or a symbol whose occurrences are counted.
  * [[Permutation.build]] puts the most discriminating at the shallow levels, where the descent prunes most, and
  * freezes them for the run. The counts are monotone only because subsumption maps literals injectively (as
  * `Subsumption.matchRec` does): let one literal cover two and a subsumer's count could exceed its subsumee's. */
final class Permutation(val sources: Array[Int], sigSize: Int):
  /** Number of features (vector length / trie depth). */
  val length: Int = sources.length

  // Fast per-slot lookup for the fill walk: symbolSlot(code) = vector index if `code` is a featured symbol, else -1.
  private val symbolSlot: Array[Int] = Array.fill(sigSize)(-1)
  private var posLevel: Int = -1
  private var negLevel: Int = -1
  locally {
    var d = 0
    while d < sources.length do
      sources(d) match
        case FeatureVector.PosCount => posLevel = d
        case FeatureVector.NegCount => negLevel = d
        case s                      => if s >= 0 && s < sigSize then symbolSlot(s) = d
      d += 1
  }

  /** Fill `out` (length [[length]]) with `c`'s feature vector: the polarity slots from the clause's cached
   *  counts, then one walk per literal atom tallying featured symbols. O(clause size); the caller owns `out`. */
  def fillVector(bank: TermBank, c: ClauseBody, out: Array[Int]): Unit =
    java.util.Arrays.fill(out, 0)
    if posLevel >= 0 then out(posLevel) = c.posCount
    if negLevel >= 0 then out(negLevel) = c.negCount
    var i = 0
    while i < c.literals.length do
      countSymbols(bank, bank.atomOf(c.literals(i)), out)
      i += 1

  // Tally `t`'s featured symbols into `out`. Variables count for nothing: that is what keeps the counts monotone.
  private def countSymbols(bank: TermBank, t: Term, out: Array[Int]): Unit =
    if !bank.isVar(t) then
      val code: Int = bank.headSymbol(t).code
      if code < symbolSlot.length && symbolSlot(code) >= 0 then out(symbolSlot(code)) += 1
      val n: Int = bank.arity(t)
      var i = 0
      while i < n do { countSymbols(bank, bank.arg(t, i), out); i += 1 }

object Permutation:
  /** An adaptive permutation from `clauses` (typically the initial set): the two polarity counts, then the
    * up-to `maxLen - 2` symbols of highest presence entropy, most-discriminating first, dropping those present
    * in all or no clauses. `maxLen` bounds the vector length (E caps at 17). */
  def build(bank: TermBank, clauses: Seq[Clause], maxLen: Int = 8): Permutation =
    val sigSize: Int = bank.signature.size
    val total: Int = clauses.size
    val docFreq: Array[Int] = new Array[Int](sigSize) // # clauses containing each symbol (distinct-per-clause)

    if total > 0 then
      val seenAt: Array[Int] = Array.fill(sigSize)(-1) // timestamp mark to collect distinct symbols without re-clearing
      val marked: IntArrayList = new IntArrayList()
      var ci = 0
      val it = clauses.iterator
      while it.hasNext do
        val c = it.next()
        marked.clear()
        var li = 0
        while li < c.literals.length do
          collectDistinct(bank, bank.atomOf(c.literals(li)), seenAt, ci, marked)
          li += 1
        var k = 0
        while k < marked.size do { docFreq(marked.getInt(k)) += 1; k += 1 }
        ci += 1

    // Rank symbols by presence entropy; keep only informative (0 < docFreq < total) ones.
    val scored: Array[(Double, Int)] =
      if total == 0 then Array.empty
      else
        val buf = scala.collection.mutable.ArrayBuffer.empty[(Double, Int)]
        var s = 0
        while s < sigSize do
          val df = docFreq(s)
          if df > 0 && df < total then buf += ((FeatureVector.binaryEntropy(df.toDouble / total), s))
          s += 1
        // sort by score desc, break ties by symbol code asc for determinism
        buf.sortInPlaceBy(t => (-t._1, t._2)).toArray

    val symCount: Int = math.max(0, maxLen - 2)
    val chosen: Array[Int] = scored.iterator.map(_._2).take(symCount).toArray
    val sources: Array[Int] = Array(FeatureVector.PosCount, FeatureVector.NegCount) ++ chosen
    new Permutation(sources, sigSize)

  // Mark `t`'s distinct non-variable symbol codes with timestamp `ci`, pushing newly-seen ones onto `marked`.
  private def collectDistinct(bank: TermBank, t: Term, seenAt: Array[Int], ci: Int, marked: IntArrayList): Unit =
    if !bank.isVar(t) then
      val code: Int = bank.headSymbol(t).code
      if code < seenAt.length && seenAt(code) != ci then { seenAt(code) = ci; marked.add(code) }
      val n: Int = bank.arity(t)
      var i = 0
      while i < n do { collectDistinct(bank, bank.arg(t, i), seenAt, ci, marked); i += 1 }

/** A trie over clauses keyed by their [[Permutation]] feature vectors: a root-to-leaf path spells one vector and
  * its leaf holds every clause carrying it. Children sit in **sorted** parallel arrays so a descent can take a
  * whole value range -- the `≤`-cone for [[forwardCandidates]], the `≥`-cone for [[backwardCandidates]]. */
final class FeatureVectorIndex(bank: TermBank, perm: Permutation):
  private val depth: Int = perm.length
  // One reusable feature-vector buffer for every clause-keyed operation. A retrieval reads it across its whole
  // descent, so a callback re-entering this index would refill it mid-descent and drop candidates -- a missed
  // simplification nothing reports. `descending` makes that a loud failure, as `FingerprintIndex` does for `fpBuf`.
  private val buf: Array[Int] = new Array[Int](depth)
  private var descending: Boolean = false // true while a retrieval descent is live (buf is being read)
  private var _size: Int = 0

  /** Fail loudly if a clause-keyed op is entered during a live retrieval descent (see the `buf` note). */
  private def guardNotDescending(op: String): Unit =
    if descending then
      throw new IllegalStateException(
        s"FeatureVectorIndex.$op during a live retrieval descent: the shared buffer would be refilled and " +
          "candidates dropped. Collect inside the callback and mutate after it returns."
      )

  /** Run `descend` with the guard armed, so a re-entrant clause-keyed op inside a callback throws. */
  private inline def guarded[A](inline descend: => A): A =
    descending = true
    try descend finally descending = false

  private final class Node:
    var keys: Array[Int] = null // internal: sorted child feature-values, used [0, nkids)
    var kids: Array[Node] = null
    var nkids: Int = 0
    var bucket: ObjectOpenHashSet[Clause] = null // leaf (depth reached): the clauses with this vector

  private val root: Node = new Node

  def size: Int = _size

  def insert(c: Clause): Unit =
    guardNotDescending("insert")
    perm.fillVector(bank, c, buf)
    var node: Node = root
    var d = 0
    while d < depth do { node = childForInsert(node, buf(d)); d += 1 }
    if node.bucket == null then node.bucket = new ObjectOpenHashSet[Clause](2)
    if node.bucket.add(c) then _size += 1

  /** Remove `c` (matched by identity/`equals`); returns whether it was present. Prunes emptied nodes. */
  def remove(c: Clause): Boolean =
    guardNotDescending("remove")
    perm.fillVector(bank, c, buf)
    val removed = removeRec(root, 0, c)
    if removed then _size -= 1
    removed

  /** Visit every stored clause whose vector is `≤` the query's componentwise: the candidate subsumers of `q`. */
  def forwardCandidates(q: ClauseBody)(visit: Clause => Unit): Unit =
    guardNotDescending("forwardCandidates")
    perm.fillVector(bank, q, buf)
    guarded(descendLe(root, 0, visitAll(visit)))

  /** Whether **some** candidate subsumer of `q` satisfies `pred`: [[forwardCandidates]] short-circuited, since
    * forward subsumption only asks whether `q` is subsumed at all. Same candidates, same verdict, less work.
    * `pred` carries the visiting retrievals' constraint: it must not query or mutate this index. */
  def existsForwardCandidate(q: ClauseBody)(pred: Clause => Boolean): Boolean =
    guardNotDescending("existsForwardCandidate")
    perm.fillVector(bank, q, buf)
    guarded(descendLe(root, 0, pred))

  /** Visit every stored clause whose vector is `≥` the query's componentwise: the candidate subsumees of `q`. */
  def backwardCandidates(q: ClauseBody)(visit: Clause => Unit): Unit =
    guardNotDescending("backwardCandidates")
    perm.fillVector(bank, q, buf)
    guarded(descendGe(root, 0, visitAll(visit)))

  // --- descents -------------------------------------------------------------------------------------------
  //
  // Both cones are one recursion each, over a `pred` that returns `true` to stop the descent:
  // `existsForwardCandidate` passes its own, the visiting retrievals one that never stops.

  /** `pred` form of a visiting callback: run it on every candidate and never stop. */
  private def visitAll(visit: Clause => Unit): Clause => Boolean = c => { visit(c); false }

  private def descendLe(node: Node, d: Int, pred: Clause => Boolean): Boolean =
    if d == depth then leafExists(node, pred)
    else
      var i = 0
      // children sorted ascending: the prefix with key <= buf(d) is exactly the compatible set at this level
      while i < node.nkids && node.keys(i) <= buf(d) do
        if descendLe(node.kids(i), d + 1, pred) then return true
        i += 1
      false

  private def descendGe(node: Node, d: Int, pred: Clause => Boolean): Boolean =
    if d == depth then leafExists(node, pred)
    else
      var i = lowerBound(node, buf(d)) // first index with key >= buf(d); the suffix from there is compatible
      while i < node.nkids do
        if descendGe(node.kids(i), d + 1, pred) then return true
        i += 1
      false

  private def leafExists(node: Node, pred: Clause => Boolean): Boolean =
    if node.bucket == null then false
    else
      val it = node.bucket.iterator()
      while it.hasNext do
        if pred(it.next()) then return true
      false

  // --- node child management (sorted parallel arrays) -----------------------------------------------------

  /** Find-or-create the child of `node` under `key`, keeping `keys`/`kids` sorted ascending. */
  private def childForInsert(node: Node, key: Int): Node =
    val idx = lowerBound(node, key)
    if idx < node.nkids && node.keys(idx) == key then node.kids(idx)
    else
      ensureCapacity(node, node.nkids + 1)
      System.arraycopy(node.keys, idx, node.keys, idx + 1, node.nkids - idx)
      System.arraycopy(node.kids, idx, node.kids, idx + 1, node.nkids - idx)
      val child = new Node
      node.keys(idx) = key
      node.kids(idx) = child
      node.nkids += 1
      child

  private def indexOf(node: Node, key: Int): Int =
    val idx = lowerBound(node, key)
    if idx < node.nkids && node.keys(idx) == key then idx else -1

  /** First index `i` in `[0, nkids)` with `keys(i) >= key` (binary search); `nkids` if none. */
  private def lowerBound(node: Node, key: Int): Int =
    var lo = 0
    var hi = node.nkids
    while lo < hi do
      val mid = (lo + hi) >>> 1
      if node.keys(mid) < key then lo = mid + 1 else hi = mid
    lo

  private def ensureCapacity(node: Node, n: Int): Unit =
    if node.keys == null then { node.keys = new Array[Int](4); node.kids = new Array[Node](4) }
    else if n > node.keys.length then
      val cap = node.keys.length * 2
      node.keys = java.util.Arrays.copyOf(node.keys, cap)
      node.kids = java.util.Arrays.copyOf(node.kids, cap)

  private def removeChildAt(node: Node, idx: Int): Unit =
    System.arraycopy(node.keys, idx + 1, node.keys, idx, node.nkids - idx - 1)
    System.arraycopy(node.kids, idx + 1, node.kids, idx, node.nkids - idx - 1)
    node.nkids -= 1
    node.kids(node.nkids) = null // release reference

  private def removeRec(node: Node, d: Int, c: Clause): Boolean =
    if d == depth then node.bucket != null && node.bucket.remove(c)
    else
      val idx = indexOf(node, buf(d))
      if idx < 0 then false
      else
        val child = node.kids(idx)
        val removed = removeRec(child, d + 1, c)
        if removed && isEmptyNode(child, d + 1) then removeChildAt(node, idx) // prune the now-empty subtree
        removed

  private def isEmptyNode(node: Node, d: Int): Boolean =
    if d == depth then node.bucket == null || node.bucket.isEmpty else node.nkids == 0
