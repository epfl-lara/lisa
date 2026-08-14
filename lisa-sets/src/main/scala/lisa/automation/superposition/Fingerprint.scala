package lisa.automation.superposition

import scala.collection.mutable
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.objects.ObjectOpenHashSet

import Core.*

/**
 * Fingerprint indexing: the fast, imperfect *candidate filter* for the unification-based inferences
 * (superposition and ordinary resolution). `archive/Phase5.md` has the design notes and
 * `archive/PossibleOptimizations.md` the struct-of-arrays alternative.
 *
 * A term's **fingerprint** is a fixed-length `Int` vector obtained by sampling a fixed set of positions (a
 * position is a path of argument indices; the empty path is the top). At each position we record one feature:
 *   - a **concrete symbol**, given by its code (`>= 0`, unchanged);
 *   - `AnyVar` (a variable sits exactly at the position);
 *   - `BelowVar` (the position is strictly below a variable, so absent now but an instance could grow it);
 *   - `NotInTerm` (the position can never exist: a concrete symbol of too-small arity is in the way).
 * The three specials are negative (`-1/-2/-3`), disjoint from symbol codes, so `feature >= 0` is the O(1)
 * "is a concrete symbol" test the compatibility relation uses (and no `+1` shift is needed).
 *
 * Two terms can unify **only if** their fingerprints are *compatible* at every sampled position
 * ([[unifiable]]); the converse fails (false positives), so a fingerprint match is a filter that must be
 * confirmed by a real unification. Crucially it has **no false negatives**: if two terms genuinely unify,
 * their fingerprints are compatible everywhere, so [[FingerprintIndex.retrieveUnifiable]] never hides a real
 * partner, which is what makes it safe to replace the linear active-set scan.
 */
object Fingerprint:

  /** The position holds a variable. */
  inline val AnyVar = -2

  /** The position is strictly below a variable (does not exist yet, but could in an instance). */
  inline val BelowVar = -3

  /** The position cannot exist in the term or any instance (a concrete symbol of too-small arity blocks it). */
  inline val NotInTerm = -1

  /**
   * E's default **FP7** sampling scheme: the top symbol, its two arguments, and their four grandchildren:
   * `{ε, 0, 1, 0.0, 0.1, 1.0, 1.1}` (argument indices are 0-based). A balanced discrimination/size trade-off.
   */
  val FP7: Array[Array[Int]] = Array(
    Array.empty[Int], // ε (top)
    Array(0), Array(1),
    Array(0, 0), Array(0, 1), Array(1, 0), Array(1, 1)
  )

  /** The prebuilt sample trie for [[FP7]], the default for [[FingerprintIndex]] (built once, shared). */
  val FP7Trie: SampleTrie = new SampleTrie(FP7)

  /** The fingerprint of `t` under `trie`'s scheme (one feature per sampled position). */
  def compute(bank: TermBank, t: Term, trie: SampleTrie): Array[Int] = trie.fingerprint(bank, t)

  /**
   * Whether a query feature `qf` and a stored feature `sf` are compatible for **unification**, i.e. whether
   * two terms with these features at a position could have a common instance there. Symmetric. The relation:
   *   - `qf` a concrete symbol: `sf ∈ { qf, AnyVar, BelowVar }` (a stored var / below-var can unify with it);
   *   - `qf == NotInTerm`: `sf ∈ { NotInTerm, BelowVar }` (both can be absent);
   *   - `qf == AnyVar`: any symbol, `AnyVar`, `BelowVar`, i.e. everything **except** `NotInTerm` (a query variable
   *     forces the position to exist);
   *   - `qf == BelowVar`: compatible with everything (a below-var instance may or may not have the position).
   */
  def unifiable(qf: Int, sf: Int): Boolean =
    if qf >= 0 then sf == qf || sf == AnyVar || sf == BelowVar
    else if qf == NotInTerm then sf == NotInTerm || sf == BelowVar
    else if qf == AnyVar then sf >= 0 || sf == AnyVar || sf == BelowVar
    else true // qf == BelowVar: compatible with any feature

/**
 * A **sampling scheme** compiled to a trie of positions, so a whole fingerprint is computed in a *single*
 * descent of the term rather than one independent top-down walk per position (which re-derefs shared
 * prefixes). Nodes of the trie are the *prefixes* of the sampled positions; each carries the output slot when
 * it is itself a sampled position. [[fingerprint]] walks the term in lock-step with this trie, so every term
 * node under a sampled position is visited exactly once.
 *
 * The descent state is an `Int`-tagged pair `(state: Term, deg: Int)`: `deg == 0` means `state` is a real
 * subterm; `deg == BelowVar`/`NotInTerm` means we have gone below a variable / off the end of a concrete
 * symbol, and `deg` is exactly the feature to emit for this position and every position beneath it. This keeps
 * the walk allocation-free (no `Option`/ADT, no boxing) while respecting the opaque `Term` boundary.
 *
 * '''Precondition:''' the sampled `positions` are pairwise distinct. A repeat gives two output slots one trie
 * node, whose `slot` field keeps only the last, leaving the other slot unwritten and (since [[fingerprintInto]]
 * reuses the caller's buffer) carrying the previous term's feature.
 */
final class SampleTrie(positions: Array[Array[Int]]):

  /** The fingerprint length (number of sampled positions). */
  val length: Int = positions.length

  private final class SNode:
    var slot: Int = -1 //      output index if this prefix is a sampled position, else -1
    val childArgs: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty // child edge labels (argument indices)
    val kids: mutable.ArrayBuffer[SNode] = mutable.ArrayBuffer.empty
    def childForArg(ai: Int): SNode =
      var i = 0
      while i < childArgs.length do { if childArgs(i) == ai then return kids(i); i += 1 }
      val n = new SNode; childArgs += ai; kids += n; n

  private val root: SNode =
    val r = new SNode
    var s = 0
    while s < positions.length do
      val path = positions(s)
      var node = r
      var i = 0
      while i < path.length do { node = node.childForArg(path(i)); i += 1 }
      node.slot = s
      s += 1
    r

  /** Compute `t`'s fingerprint in one lock-step descent (see the class doc), into a freshly allocated array. */
  def fingerprint(bank: TermBank, t: Term): Array[Int] =
    val fp: Array[Int] = new Array[Int](length)
    fingerprintInto(bank, t, fp)
    fp

  /** Compute `t`'s fingerprint into a caller-supplied buffer of length [[length]], so a hot path can reuse one
   *  array across calls instead of allocating. Every slot is overwritten (the walk visits every sampled
   *  position), so a dirty buffer is fine. */
  def fingerprintInto(bank: TermBank, t: Term, out: Array[Int]): Unit =
    walk(root, bank, t, 0, out)

  private def walk(node: SNode, bank: TermBank, state: Term, deg: Int, fp: Array[Int]): Unit =
    val real: Boolean = deg == 0
    val sVar: Boolean = real && bank.isVar(state) // a variable at this position (children go below it)
    if node.slot >= 0 then
      fp(node.slot) = if !real then deg else if sVar then Fingerprint.AnyVar else bank.headSymbol(state).code
    val ar: Int = if real && !sVar then bank.arity(state) else 0
    var i = 0
    while i < node.childArgs.length do
      val ai: Int = node.childArgs(i)
      val child: SNode = node.kids(i)
      if !real then walk(child, bank, state, deg, fp) //                       already degenerate: propagate `deg`
      else if sVar then walk(child, bank, state, Fingerprint.BelowVar, fp) //  descend below a variable
      else if ai >= ar then walk(child, bank, state, Fingerprint.NotInTerm, fp) // no such argument (nor in any instance)
      else walk(child, bank, bank.arg(state, ai), 0, fp) //                    a real child subterm
      i += 1

/**
 * A leaf's entry bucket as a **zero-cost opaque type** directly over an `ObjectOpenHashSet[E]`. Being opaque,
 * a `Bucket[E]` *is* the set at runtime (no wrapper object per leaf), and the four operations dispatch straight
 * to the set (no representation `match`). A hash set gives O(1) `add`/`remove` even for the big buckets shallow
 * variable-headed terms create (every `f(‹var›)` across the active set fingerprints alike). `null` is the empty
 * bucket (the `>: Null` bound keeps it assignable); every operation handles it, and [[Bucket.add]] starts a
 * fresh set from `null` (returned, so callers write `b = b.add(e)`).
 *
 * Two other representations (adaptive array→set, and array-only) benchmarked throughput-equivalent, so this
 * simplest form is kept. See `archive/PossibleOptimizations.md`.
 */
object Buckets:

  opaque type Bucket[E] >: Null <: AnyRef = ObjectOpenHashSet[E]

  object Bucket:
    extension [E](b: Bucket[E])
      /** Add `e`; a `null` receiver starts a fresh set (returned, so the caller reassigns). */
      def add(e: E): Bucket[E] =
        if b == null then { val s = new ObjectOpenHashSet[E](2); s.add(e); s }
        else { b.add(e); b }

      /** Remove one entry equal (`==`) to `e`; returns whether one was found. */
      def remove(e: E): Boolean = b != null && b.remove(e)

      /** Whether an entry equal (`==`) to `e` is present (a `null` receiver is empty). */
      def contains(e: E): Boolean = b != null && b.contains(e)

      def isEmpty: Boolean = b == null || b.isEmpty

      /** Visit every entry (order unspecified). */
      def foreach(visit: E => Unit): Unit =
        if b != null then
          val it = b.iterator()
          while it.hasNext do visit(it.next())

/**
 * A fingerprint trie over terms, generic in the payload `E` (e.g. [[IntoEntry]]/[[FromEntry]]). Each stored
 * term is placed by its fingerprint (`trie.length` levels, one per sampled position); a leaf holds the
 * payloads of all terms sharing that exact fingerprint. Insertion/deletion are `O(depth)`;
 * [[retrieveUnifiable]] descends only the branches compatible with the query fingerprint ([[Fingerprint.unifiable]]),
 * returning a **candidate superset** (no false negatives) that the caller confirms with a real unification.
 *
 * `retrieveUnifiable` pushes candidates through a caller `visit` callback rather than allocating a collection,
 * so the hot query path allocates nothing beyond the (bounded, `depth`-deep) recursion. Removal prunes emptied
 * nodes; the entry to remove is matched by `==` (so payloads with value equality delete by re-derived value).
 * Each leaf's entries live in an opaque [[Buckets.Bucket]] (a hash set), so `add`/`remove` are O(1) even for
 * the big collision buckets shallow variable-headed terms create.
 * The sampling scheme is a shared [[SampleTrie]] (default [[Fingerprint.FP7Trie]]), so two indices cost one trie.
 */
final class FingerprintIndex[E](bank: TermBank, trie: SampleTrie = Fingerprint.FP7Trie):

  private val depth: Int = trie.length
  private val root: Node = new Node
  private var _size: Int = 0

  // One reusable fingerprint buffer shared by every term-keyed operation (insert/remove/retrieveUnifiable). This
  // removes the per-call fingerprint-array allocation on the hot query path (and the amortized one on
  // insert/remove). It is safe only because these operations never nest on a single index: `retrieveUnifiable`
  // reads `fpBuf` throughout its descent (across every `visit` callback), so a callback that re-entered any
  // term-keyed op on the *same* index would refill the buffer mid-descent and silently drop candidates (a false
  // negative ⇒ incompleteness). `descending` (below) enforces this via `guardNotDescending`.
  private val fpBuf: Array[Int] = new Array[Int](depth)
  private var descending: Boolean = false // true while a retrieveUnifiable descent is live (fpBuf is being read)

  /** Fail loudly if a term-keyed op is entered during a live retrieval descent (see the `fpBuf` note). */
  private def guardNotDescending(op: String): Unit =
    if descending then
      throw new IllegalStateException(
        s"FingerprintIndex.$op during a live retrieveUnifiable descent: a retrieval `visit` callback must not " +
          "query or mutate the same index (the shared fingerprint buffer would be corrupted, dropping candidates)."
      )

  /** A trie node: `children` (feature → child) at intermediate levels, an entry `bucket` at leaves. Both lazy
   *  (`children == null` = no children; a `null` `bucket` = no entries, which [[Buckets.Bucket]] treats as empty). */
  private final class Node:
    var children: Int2ObjectOpenHashMap[Node] = null
    var bucket: Buckets.Bucket[E] = null
    def emptyNode: Boolean =
      (children == null || children.isEmpty) && bucket.isEmpty

  /** Number of stored (term, payload) entries. */
  def size: Int = _size
  def isEmpty: Boolean = _size == 0

  /** Drop all entries (reset to empty), so one index can be reused across saturations. */
  def clear(): Unit = { guardNotDescending("clear"); root.children = null; root.bucket = null; _size = 0 }

  /** Insert `entry` under `term`'s fingerprint. */
  def insert(term: Term, entry: E): Unit =
    guardNotDescending("insert")
    trie.fingerprintInto(bank, term, fpBuf)
    var node: Node = root
    var d = 0
    while d < depth do
      if node.children == null then node.children = new Int2ObjectOpenHashMap[Node]()
      var c: Node = node.children.get(fpBuf(d))
      if c == null then { c = new Node; node.children.put(fpBuf(d), c) }
      node = c
      d += 1
    val isNew: Boolean = !node.bucket.contains(entry) // `add` is a no-op on a value-equal duplicate,
    node.bucket = node.bucket.add(entry) //              so count only genuinely new entries
    if isNew then _size += 1

  /** Remove one entry equal (`==`) to `entry` stored under `term`'s fingerprint; returns whether one was
   *  found. Emptied nodes are pruned up the path. */
  def remove(term: Term, entry: E): Boolean =
    guardNotDescending("remove")
    trie.fingerprintInto(bank, term, fpBuf)
    val removed: Boolean = removeRec(root, 0, fpBuf, entry)
    if removed then _size -= 1
    removed

  private def removeRec(node: Node, d: Int, fp: Array[Int], entry: E): Boolean =
    if d == depth then node.bucket.remove(entry) // remove handles a `null` (empty) bucket ⇒ false
    else
      val ch = node.children
      if ch == null then false
      else
        val child = ch.get(fp(d))
        if child == null then false
        else
          val removed = removeRec(child, d + 1, fp, entry)
          if removed && child.emptyNode then ch.remove(fp(d)) // prune the now-empty subtree
          removed

  /** Visit every stored entry whose term is **unification-compatible** with `query` (a candidate superset of
   *  the truly-unifiable ones). Allocation-free on the query path (no intermediate collection). */
  def retrieveUnifiable(query: Term)(visit: E => Unit): Unit =
    guardNotDescending("retrieveUnifiable")
    trie.fingerprintInto(bank, query, fpBuf)
    descending = true
    try descendUnif(root, 0, fpBuf, visit)
    finally descending = false

  private def descendUnif(node: Node, d: Int, qfp: Array[Int], visit: E => Unit): Unit =
    if d == depth then node.bucket.foreach(visit) // foreach handles a `null` (empty) bucket ⇒ no-op
    else
      val ch = node.children
      if ch != null then
        val qf: Int = qfp(d)
        if qf >= 0 then // concrete symbol: only the {qf, AnyVar, BelowVar} branches can unify
          follow(ch, qf, d, qfp, visit)
          follow(ch, Fingerprint.AnyVar, d, qfp, visit)
          follow(ch, Fingerprint.BelowVar, d, qfp, visit)
        else if qf == Fingerprint.NotInTerm then // only {NotInTerm, BelowVar}
          follow(ch, Fingerprint.NotInTerm, d, qfp, visit)
          follow(ch, Fingerprint.BelowVar, d, qfp, visit)
        else // qf is AnyVar (all but NotInTerm) or BelowVar (all children)
          val skipNotInTerm: Boolean = qf == Fingerprint.AnyVar
          val it = ch.int2ObjectEntrySet().fastIterator()
          while it.hasNext do
            val e = it.next()
            if !(skipNotInTerm && e.getIntKey == Fingerprint.NotInTerm) then descendUnif(e.getValue, d + 1, qfp, visit)

  inline private def follow(ch: Int2ObjectOpenHashMap[Node], key: Int, d: Int, qfp: Array[Int], visit: E => Unit): Unit =
    val c = ch.get(key)
    if c != null then descendUnif(c, d + 1, qfp, visit)

/**
 * The into-index payload: a rewritable non-variable subterm at `pos` (a path of argument indices) inside
 * `clause`'s literal `litIndex`, a *target* location for superposition (and backward demodulation). `pos` is
 * the very array passed on to `Superposition.superpose`. Value equality (on `clause.id`, `litIndex`, and the
 * `pos` contents) so an entry can be removed by a re-derived equal value when the clause leaves the active set.
 */
final class IntoEntry(val clause: Clause, val litIndex: Int, val pos: Array[Int]):
  override def equals(o: Any): Boolean = o match
    case e: IntoEntry => clause.id == e.clause.id && litIndex == e.litIndex && java.util.Arrays.equals(pos, e.pos)
    case _ => false
  override def hashCode: Int = (clause.id * 31 + litIndex) * 31 + java.util.Arrays.hashCode(pos)
  override def toString: String = s"IntoEntry(c${clause.id}, lit=$litIndex, pos=${pos.mkString("[", ",", "]")})"

/**
 * The from-index payload: the usable maximal `side` (0/1) of `clause`'s positive equality literal `litIndex`.
 * a *source* equation for superposition. Value equality as [[IntoEntry]].
 */
final class FromEntry(val clause: Clause, val litIndex: Int, val side: Int):
  override def equals(o: Any): Boolean = o match
    case e: FromEntry => clause.id == e.clause.id && litIndex == e.litIndex && side == e.side
    case _ => false
  override def hashCode: Int = (clause.id * 31 + litIndex) * 31 + side
  override def toString: String = s"FromEntry(c${clause.id}, lit=$litIndex, side=$side)"

/**
 * The resolution literal-index payload: a selected non-equality literal `litIndex` of active
 * `clause`, an ordinary-resolution partner. The index is keyed by the literal *atom*, and polarity is carried
 * by *which* of the two per-polarity indices holds the entry (so a query fetches only complementary-polarity
 * candidates); the payload therefore needs only `(clause, litIndex)`. Value equality (on `clause.id`, `litIndex`)
 * so an entry removes by a re-derived equal value when the clause leaves the active set, as [[IntoEntry]]/[[FromEntry]].
 */
final class ResolutionEntry(val clause: Clause, val litIndex: Int):
  override def equals(o: Any): Boolean = o match
    case e: ResolutionEntry => clause.id == e.clause.id && litIndex == e.litIndex
    case _ => false
  override def hashCode: Int = clause.id * 31 + litIndex
  override def toString: String = s"ResolutionEntry(c${clause.id}, lit=$litIndex)"
