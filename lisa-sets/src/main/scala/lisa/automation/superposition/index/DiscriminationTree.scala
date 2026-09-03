package lisa.automation.superposition
package index

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap

import scala.collection.mutable

import Core._

/**
 * A perfect discrimination tree, generic in the payload `E`, answering the generalization query: given a term
 * `u`, which stored keys generalize it. Forward demodulation is the user, with the demodulators' left
 * sides as keys. Keys are stored in flattened preorder, over three kinds of edge:
 *
 *   - a function symbol edge, keyed by symbol code;
 *   - a variable edge, kept distinct by variable number. This is what makes the tree *perfect*: retrieval binds
 *     the stored variable to the query subterm on the trail and checks non-linear consistency with `matchTerm`,
 *     so reaching a leaf is an exact match with the substitution already in place;
 *   - a ground-term edge, keyed by hash-consed term id, since a ground subterm matches `u` only if it is `u`.
 *
 * Each node caches the minimum key weight, so a subtree whose lightest entry outweighs the query is
 * skipped: instantiation can only grow a term.
 *
 * Entries are matched by `==` on removal, as in [[FingerprintIndex]].
 */
final class DiscriminationTree[E](bank: TermBank, trail: Trail):
  private inline val VarMarker = -1 // flattened head of a variable (function symbol codes are >= 0)

  /**
   * One variable of a stored key, in both forms the tree needs: `varNum` identifies the edge, so the two `x`s
   * of `f(x,x)` follow one edge while `f(x,y)` branches, and `varTerm` is that same variable as a term.
   */
  private final class VarEdge(val varNum: Int, val varTerm: Term, val child: Node)

  private final class Node:
    var symChildren: Int2ObjectOpenHashMap[Node] = null //    function symbol code -> child
    var groundChildren: Int2ObjectOpenHashMap[Node] = null // whole ground subterm (by Term id) -> child
    var varChildren: mutable.ArrayBuffer[VarEdge] = null //   one edge per distinct stored variable at this position
    var entries: mutable.ArrayBuffer[E] = null //             leaf: the payloads stored under this exact key
    var minWeight: Int = Int.MaxValue //                      min key weight at/below (a sound lower bound)

  private val root: Node = new Node
  private var _size: Int = 0

  // The query flattened to preorder, in buffers reused across retrievals so a query allocates nothing. The
  // walk over the querry reads them the whole way down.
  private var qTerm: Array[Term] = new Array[Term](16) // the subterm at each preorder position
  private var qHead: Array[Int] = new Array[Int](16) //  its head: function symbol code, or VarMarker
  private var qSkip: Array[Int] = new Array[Int](16) //  index just past this subterm's subtree
  private var qLen: Int = 0
  private var descending: Boolean = false // true while a retrieval descent is live (the buffers are in use)

  /**
   * Fail loudly if the tree is entered during a live retrieval descent.
   */
  private def guardNotDescending(op: String): Unit =
    if descending then
      throw new IllegalStateException(
        s"DiscriminationTree.$op during a live retrieval descent: a `visit` callback must not query or " +
          "mutate the same tree (the shared flatten buffers would be overwritten, and the descent would " +
          "then report rules that do not generalize the query). Collect inside the callback and act after " +
          "it returns."
      )

  /**
   * Run `body` with the guard armed, so a re-entrant operation inside a callback throws.
   */
  private inline def guarded[A](inline body: => A): A =
    descending = true
    try body
    finally descending = false

  inline def size: Int = _size
  def isEmpty: Boolean = _size == 0

  // --- insertion ------------------------------------------------------------------------------------------

  def insert(key: Term, entry: E): Unit =
    guardNotDescending("insert")
    val w = bank.weight(key)
    if w < root.minWeight then root.minWeight = w
    val leaf = insertRec(root, key, w)
    if leaf.entries == null then leaf.entries = mutable.ArrayBuffer.empty
    leaf.entries += entry
    _size += 1

  // Consume `t`'s flattened form starting at `node`'s edge for `t`, returning the node just past `t`.
  private def insertRec(node: Node, t: Term, w: Int): Node =
    if bank.isGround(t) then
      // whole ground subterm ⇒ one edge keyed by its Term id; matches only an identical query subterm (no recursion)
      if node.groundChildren == null then node.groundChildren = new Int2ObjectOpenHashMap[Node]()
      val key = t.offset
      var c = node.groundChildren.get(key)
      if c == null then { c = new Node; node.groundChildren.put(key, c) }
      if w < c.minWeight then c.minWeight = w
      c
    else
      val child: Node =
        if bank.isVar(t) then
          val vn = bank.varNum(t).num
          var e = findVarEdge(node, vn)
          if e == null then
            if node.varChildren == null then node.varChildren = mutable.ArrayBuffer.empty
            e = new VarEdge(vn, t, new Node)
            node.varChildren += e
          e.child
        else
          if node.symChildren == null then node.symChildren = new Int2ObjectOpenHashMap[Node]()
          val code = bank.headSymbol(t).code
          var c = node.symChildren.get(code)
          if c == null then { c = new Node; node.symChildren.put(code, c) }
          c
      if w < child.minWeight then child.minWeight = w
      var cur = child
      if !bank.isVar(t) then // a symbol edge (non-ground): consume the args (a variable has none)
        val n = bank.arity(t)
        var i = 0
        while i < n do { cur = insertRec(cur, bank.arg(t, i), w); i += 1 }
      cur

  private def findVarEdge(node: Node, vn: Int): VarEdge =
    val es = node.varChildren
    if es == null then null
    else
      var k = 0
      while k < es.length do { if es(k).varNum == vn then return es(k); k += 1 }
      null

  // --- retrieval (generalizations) ------------------------------------------------------------------------

  /**
   * Visit each entry whose key generalizes `query`, with the matcher live on the trail, the key's variables
   *  in scope 0 and the query in scope 1. Exact, so no verification is needed. `visit` returns `true` to stop
   *  the descent, which this then returns. The trail is restored on return.
   */
  def retrieveGeneralizations(query: Term)(visit: E => Boolean): Boolean =
    guardNotDescending("retrieveGeneralizations")
    qLen = 0
    flatten(query)
    guarded(descend(root, 0, bank.weight(query), visit))

  private def flatten(t: Term): Unit =
    val idx = qLen
    if idx >= qTerm.length then
      val n2 = qTerm.length * 2
      qTerm = asArrayTerm(java.util.Arrays.copyOf(asArrayInt(qTerm), n2))
      qHead = java.util.Arrays.copyOf(qHead, n2)
      qSkip = java.util.Arrays.copyOf(qSkip, n2)
    qTerm(idx) = t
    qHead(idx) = if bank.isVar(t) then VarMarker else bank.headSymbol(t).code
    qLen += 1
    if !bank.isVar(t) then
      val n = bank.arity(t)
      var i = 0
      while i < n do { flatten(bank.arg(t, i)); i += 1 }
    qSkip(idx) = qLen

  private def descend(node: Node, i: Int, qw: Int, visit: E => Boolean): Boolean =
    if node.minWeight > qw then false // size prune: no key below is light enough to match `query`
    else if i == qLen then
      val es = node.entries
      if es != null then
        var k = 0
        // One bracket per entry: a leaf can hold several, visited under the same substitution. Without this a
        // `visit` that binds would leave those bindings in place for the next entry, which would then be
        // matched under a substitution it never agreed to. `save` is a counter read and `restore` a no-op
        // when nothing was bound, which is the common case.
        while k < es.length do
          val saved = trail.save()
          val stop = visit(es(k))
          trail.restore(saved)
          if stop then return true
          k += 1
      false
    else
      // ground edge: the query subterm at i is exactly a stored ground term? (O(1) id lookup, skips its subtree)
      if node.groundChildren != null then
        val gc = node.groundChildren.get(qTerm(i).offset)
        if gc != null && descend(gc, qSkip(i), qw, visit) then return true
      // symbol edge: follow the query subterm's head (args continue at i+1)
      val h = qHead(i)
      if h >= 0 && node.symChildren != null then
        val c = node.symChildren.get(h)
        if c != null && descend(c, i + 1, qw, visit) then return true
      // variable edges: bind each stored variable to the whole subterm `u`
      val es = node.varChildren
      if es != null then
        val u = qTerm(i)
        val next = qSkip(i)
        var k = 0
        while k < es.length do
          val e = es(k)
          val saved = trail.save()
          val stop = trail.matchTerm(e.varTerm, 0, u, 1) && descend(e.child, next, qw, visit)
          trail.restore(saved)
          if stop then return true
          k += 1
      false

  // --- removal --------------------------------------------------------------------------------------------

  /**
   * Remove `entry` from under `key`'s path, matching by `==`, and prune emptied nodes. Returns whether one
   *  was found. `minWeight` is intentionally left stale (sound; see the class doc).
   */
  def remove(key: Term, entry: E): Boolean =
    guardNotDescending("remove")
    qLen = 0
    flatten(key)
    val removed = removeRec(root, 0, entry)
    if removed then _size -= 1
    removed

  // The mirror of `descend` over the flattened key, following the single edge each position takes instead of
  // every compatible one. Each child emptied by the removal is pruned as the recursion unwinds.
  private def removeRec(node: Node, i: Int, entry: E): Boolean =
    if i == qLen then removeEntry(node, entry)
    else
      val t: Term = qTerm(i)
      if bank.isGround(t) then // one edge for the whole ground subterm, so continue past its flattened subtree
        val key: Int = t.offset
        val c: Node = if node.groundChildren == null then null else node.groundChildren.get(key)
        if c == null then false
        else
          val removed = removeRec(c, qSkip(i), entry)
          if removed && isEmptyNode(c) then node.groundChildren.remove(key)
          removed
      else if qHead(i) == VarMarker then
        val e: VarEdge = findVarEdge(node, bank.varNum(t).num)
        if e == null then false
        else
          val removed = removeRec(e.child, qSkip(i), entry)
          if removed && isEmptyNode(e.child) then removeVarEdge(node, e.varNum)
          removed
      else
        val code: Int = qHead(i)
        val c: Node = if node.symChildren == null then null else node.symChildren.get(code)
        if c == null then false
        else
          val removed = removeRec(c, i + 1, entry) // a symbol edge is followed by its arguments
          if removed && isEmptyNode(c) then node.symChildren.remove(code)
          removed

  /**
   * Drop one entry `== entry` from `node`'s leaf list; whether there was one.
   */
  private def removeEntry(node: Node, entry: E): Boolean =
    val es = node.entries
    if es == null then false
    else
      var k = 0
      while k < es.length do
        if es(k) == entry then { es.remove(k); return true }
        k += 1
      false

  private def removeVarEdge(node: Node, vn: Int): Unit =
    val es = node.varChildren
    if es != null then
      var k = 0
      while k < es.length do { if es(k).varNum == vn then { es.remove(k); return }; k += 1 }

  private def isEmptyNode(nd: Node): Boolean =
    (nd.entries == null || nd.entries.isEmpty) &&
      (nd.symChildren == null || nd.symChildren.isEmpty) &&
      (nd.groundChildren == null || nd.groundChildren.isEmpty) &&
      (nd.varChildren == null || nd.varChildren.isEmpty)
