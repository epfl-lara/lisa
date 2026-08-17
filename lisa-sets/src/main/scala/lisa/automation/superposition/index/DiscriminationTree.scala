package lisa.automation.superposition
package index

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import scala.collection.mutable

import Core.*

/**
 * A perfect discrimination tree, generic in the payload `E`, answering the generalization query: given a term
 * `u`, which stored keys generalize it. Forward demodulation is the one user, with the demodulators' left
 * sides as keys. Keys are stored in flattened preorder, which reparses unambiguously since arities are fixed,
 * over three kinds of edge:
 *
 *   - a function symbol edge, keyed by symbol code;
 *   - a variable edge, kept distinct by variable number. This is what makes the tree *perfect*: retrieval binds
 *     the stored variable to the query subterm on the trail and checks non-linear consistency with `matchTerm`,
 *     so reaching a leaf is an exact match with the substitution already in place;
 *   - a ground-term edge, keyed by hash-consed term id, since a ground subterm matches `u` only if it is `u`.
 *
 * Each node caches the minimum key weight beneath it, so a subtree whose lightest entry outweighs the query is
 * skipped: matching can only grow a term. The bound is not recomputed on removal, so it may go stale low, which
 * prunes less rather than wrongly, and it assumes no symbol weighs less than [[Core.VariableWeight]].
 *
 * Entries are matched by `==` on removal, as in [[FingerprintIndex]].
 */
final class DiscriminationTree[E](bank: TermBank, trail: Trail):
  private inline val VarMarker = -1 // flattened head of a variable (function symbol codes are >= 0)
  // path-step edge kinds (for removal + pruning)
  private inline val KGround = 0
  private inline val KVar = 1
  private inline val KSym = 2

  /** A variable edge: the stored key's variable (its number keys the edge; the term drives the trail bind). */
  private final class VarEdge(val varNum: Int, val varTerm: Term, val child: Node)

  private final class Node:
    var symChildren: Int2ObjectOpenHashMap[Node] = null //    function symbol code -> child
    var groundChildren: Int2ObjectOpenHashMap[Node] = null // whole ground subterm (by Term id) -> child
    var varChildren: mutable.ArrayBuffer[VarEdge] = null //   one edge per distinct stored variable at this position
    var entries: mutable.ArrayBuffer[E] = null //             leaf: the payloads stored under this exact key
    var minWeight: Int = Int.MaxValue //                      min key weight at/below (a sound lower bound)

  private final class PathStep(val parent: Node, val kind: Int, val key: Int) // one edge on a removal path

  private val root: Node = new Node
  private var _size: Int = 0

  // Reused flatten buffers, read throughout a descent and across every `visit` callback, so an operation that
  // re-entered the tree from inside a callback would refill them mid-descent. Unlike the other two indices,
  // where that costs a dropped candidate, here it is unsound: `qLen` would be reset to the inner query's
  // length, the outer descent would reach a leaf having consumed only a prefix of its own query, and `visit`
  // would be handed entries whose key does not generalize it, with a partial substitution live on the trail.
  // `descending` turns that into a loud failure, as in [[FingerprintIndex]] and [[FeatureVectorIndex]].
  private var qTerm: Array[Term] = new Array[Term](16) // the subterm at each preorder position
  private var qHead: Array[Int] = new Array[Int](16) //  its head: function symbol code, or VarMarker
  private var qSkip: Array[Int] = new Array[Int](16) //  index just past this subterm's subtree
  private var qLen: Int = 0
  private var descending: Boolean = false // true while a retrieval descent is live (the buffers are in use)

  /** Fail loudly if the tree is entered during a live retrieval descent (see the buffer note above). */
  private def guardNotDescending(op: String): Unit =
    if descending then
      throw new IllegalStateException(
        s"DiscriminationTree.$op during a live retrieval descent: a `visit` callback must not query or " +
          "mutate the same tree (the shared flatten buffers would be overwritten, and the descent would " +
          "then report rules that do not generalize the query). Collect inside the callback and act after " +
          "it returns."
      )

  /** Run `body` with the guard armed, so a re-entrant operation inside a callback throws. */
  private inline def guarded[A](inline body: => A): A =
    descending = true
    try body finally descending = false

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

  /** Visit each entry whose key generalizes `query`, with the matcher live on the trail, the key's variables
   *  in scope 0 and the query in scope 1. Exact, so no verification is needed. `visit` returns `true` to stop
   *  the descent, which this then returns. The trail is restored on return.
   *
   *  `visit` may read the trail, which is the point, but must not re-enter this tree, since the flatten
   *  buffers are shared across the descent; that is enforced by a throw. The caller must hold no live scope-1
   *  bindings on entry, which `matchTerm` asserts. */
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

  /** Remove `entry` from under `key`'s path, matching by `==`, and prune emptied nodes. Returns whether one
   *  was found. `minWeight` is intentionally left stale (sound; see the class doc). */
  def remove(key: Term, entry: E): Boolean =
    guardNotDescending("remove")
    val steps = mutable.ArrayBuffer.empty[PathStep]
    val leaf = locate(root, key, steps)
    if leaf == null || leaf.entries == null then return false
    var k = 0
    var found = false
    while !found && k < leaf.entries.length do
      if leaf.entries(k) == entry then { leaf.entries.remove(k); found = true } else k += 1
    if !found then return false
    _size -= 1
    // prune emptied nodes bottom-up, stopping at the first non-empty ancestor
    var lvl = steps.length
    var cur = leaf
    var pruning = true
    while pruning && lvl > 0 do
      if isEmptyNode(cur) then
        val step = steps(lvl - 1)
        step.kind match
          case KGround => step.parent.groundChildren.remove(step.key)
          case KVar    => removeVarEdge(step.parent, step.key)
          case _       => step.parent.symChildren.remove(step.key)
        cur = step.parent
        lvl -= 1
      else pruning = false
    true

  // Navigate `t`'s existing edges from `node`, appending each traversed edge to `steps`; return the node just past
  // `t`, or `null` if any edge is missing.
  private def locate(node: Node, t: Term, steps: mutable.ArrayBuffer[PathStep]): Node =
    if bank.isGround(t) then
      val key = t.offset
      val c = if node.groundChildren == null then null else node.groundChildren.get(key)
      if c == null then null else { steps += new PathStep(node, KGround, key); c }
    else if bank.isVar(t) then
      val vn = bank.varNum(t).num
      val e = findVarEdge(node, vn)
      if e == null then null else { steps += new PathStep(node, KVar, vn); e.child }
    else
      val code = bank.headSymbol(t).code
      val c = if node.symChildren == null then null else node.symChildren.get(code)
      if c == null then null
      else
        steps += new PathStep(node, KSym, code)
        var cur = c
        val n = bank.arity(t)
        var i = 0
        while i < n && cur != null do { cur = locate(cur, bank.arg(t, i), steps); i += 1 }
        cur

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
