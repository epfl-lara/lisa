package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import scala.collection.mutable

import Core.*
import Demodulation.Rule

/**
 * A **perfect discrimination tree** over demodulator LHSs, for the *forward demodulation* retrieval query:
 * given a concrete subterm `u` of the clause being normal-formed, find the active demodulators
 * whose LHS **generalizes** `u` (`∃σ. lσ = u` — one-sided matching, not unification). It replaces `normalForm`'s
 * inner "try every rule against this subterm" scan with a single tree descent.
 * `archive/Phase5DemodulationResearch.md` surveys how E and Vampire index this query and why a *perfect* tree
 * was chosen over a non-perfect one.
 *
 * The LHSs are stored in **flattened left-to-right preorder** (fixed arities ⇒ the symbol string reparses
 * unambiguously, no end-markers), with three kinds of edge:
 *   - a **function symbol** edge (keyed by `f_code`);
 *   - a **variable** edge, kept distinct by variable number — the *perfect* part: during retrieval it **binds** its
 *     stored variable to the current query subterm on the [[Trail]] (scope 0, where the rewrite reads σ), checking
 *     non-linear consistency via `matchTerm`, so a reached leaf is an exact match with σ in place — **no verify**;
 *   - a **ground-term** edge (the fast path): a *whole ground subterm* of an LHS collapses to one edge keyed by its
 *     (hash-consed) `Term` id. Since a ground `l`-subterm matches `u` iff `u` *is* it, this is an O(1) id-equality
 *     check that skips walking the subterm symbol-by-symbol (E's `CHECK_GROUND_TERM`; cheap here because the
 *     [[TermBank]] perfectly shares terms).
 *
 * **Size pruning.** Each node caches `minWeight`, the minimum LHS weight at/below it. Matching only grows a term
 * (`weight(l) ≤ weight(lσ) = weight(u)`), so a subtree whose lightest LHS is heavier than the query is skipped with
 * one integer comparison. Kept as a sound lower bound (not recomputed on removal, so it may become stale-low, which
 * only ever prunes *less* — never a false negative). Its `weight(l) ≤ weight(lσ)` step assumes no symbol weighs
 * less than [[Core.VariableWeight]] (true of both [[Core.WeightScheme]]s, where constants weigh at least 1); a
 * zero-weight constant scheme would make the prune drop real matches.
 */
final class DiscriminationTree(bank: TermBank, trail: Trail):
  private inline val VarMarker = -1 // flattened head of a variable (function symbol codes are >= 0)
  // path-step edge kinds (for removal + pruning)
  private inline val KGround = 0
  private inline val KVar = 1
  private inline val KSym = 2

  /** A variable edge: the stored LHS variable (its number keys the edge; the term drives the trail bind). */
  private final class VarEdge(val varNum: Int, val varTerm: Term, val child: Node)

  private final class Node:
    var symChildren: Int2ObjectOpenHashMap[Node] = null //    function symbol code -> child
    var groundChildren: Int2ObjectOpenHashMap[Node] = null // whole ground subterm (by Term id) -> child
    var varChildren: mutable.ArrayBuffer[VarEdge] = null //   one edge per distinct stored variable at this position
    var rules: mutable.ArrayBuffer[Rule] = null //            leaf: demodulators with this exact LHS
    var minWeight: Int = Int.MaxValue //                      min LHS weight at/below (a sound lower bound)

  private final class PathStep(val parent: Node, val kind: Int, val key: Int) // one edge on a removal path

  private val root: Node = new Node
  private var _size: Int = 0

  // Reused flatten buffers (grown on demand). They are read throughout a descent, across every `visit`
  // callback, so an operation that re-entered the tree from inside a callback would refill them mid-descent.
  // Unlike the other two indices, where that costs a dropped candidate, here it is **unsound**: `qLen` would
  // be reset to the inner query's length, the outer descent would hit `i == qLen` at a node reached by
  // consuming only a prefix of its own query, and `visit` would be handed rules whose LHS does not generalize
  // that query — with a partial σ live on the trail. `descending` turns that into a loud failure, as in
  // [[FingerprintIndex]] and [[FeatureVectorIndex]].
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
  def clear(): Unit =
    guardNotDescending("clear")
    root.symChildren = null; root.groundChildren = null; root.varChildren = null; root.rules = null
    root.minWeight = Int.MaxValue; _size = 0

  // --- insertion ------------------------------------------------------------------------------------

  /** Insert a demodulator under its LHS's flattened path. */
  def insert(rule: Rule): Unit =
    guardNotDescending("insert")
    val w = bank.weight(rule.lhs)
    if w < root.minWeight then root.minWeight = w
    val leaf = insertRec(root, rule.lhs, w)
    if leaf.rules == null then leaf.rules = mutable.ArrayBuffer.empty
    leaf.rules += rule
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

  // --- retrieval (generalizations) ------------------------------------------------------------------

  /** Visit each active demodulator whose LHS generalizes `query`, with the matcher σ **live on the trail**
   *  (scope 0 = rule vars, scope 1 = query). Exact — no false positives. `visit` returns `true` to stop the
   *  descent early (e.g. once a rewrite has fired); [[retrieveGeneralizations]] then returns `true`. The trail is
   *  restored to its entry state on return.
   *
   *  ==Contract on `visit`==
   *  It may *read* the trail (that is the point — σ is live), but it must not
   *   - re-enter this tree (`insert`/`remove`/`clear`/`retrieveGeneralizations`): the flatten buffers are
   *     shared across the whole descent. Enforced — it throws.
   *   - leave bindings behind: each call is bracketed by `save`/`restore`, so a stray binding cannot leak
   *     into the *next* rule at the same leaf, but relying on that is not the intent.
   *
   *  The caller must also hold no live scope-1 bindings on entry — `matchTerm` asserts it. */
  def retrieveGeneralizations(query: Term)(visit: Rule => Boolean): Boolean =
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

  private def descend(node: Node, i: Int, qw: Int, visit: Rule => Boolean): Boolean =
    if node.minWeight > qw then false // size prune: no LHS below is light enough to match `query`
    else if i == qLen then
      val rs = node.rules
      if rs != null then
        var k = 0
        // One bracket per rule: a leaf can hold several (two unit equalities sharing an LHS, say), and they
        // are visited under the *same* σ. Without this, a `visit` that binds — a nested `matchTerm` or
        // `unify` — would leave those bindings in place for the next rule, which would then be matched under
        // a substitution it never agreed to. `save` is a counter read and `restore` a no-op when nothing was
        // bound, which is the common case.
        while k < rs.length do
          val saved = trail.save()
          val stop = visit(rs(k))
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

  // --- removal --------------------------------------------------------------------------------------

  /** Remove the demodulator identified by `(source.id, side)` under `rule.lhs`'s path; prune emptied nodes.
   *  Returns whether one was found. `minWeight` is intentionally left stale (sound; see the class doc). */
  def remove(rule: Rule): Boolean =
    guardNotDescending("remove")
    val steps = mutable.ArrayBuffer.empty[PathStep]
    val leaf = locate(root, rule.lhs, steps)
    if leaf == null || leaf.rules == null then return false
    var k = 0
    var found = false
    while !found && k < leaf.rules.length do
      val r = leaf.rules(k)
      if r.source.id == rule.source.id && r.side == rule.side then { leaf.rules.remove(k); found = true } else k += 1
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
    (nd.rules == null || nd.rules.isEmpty) &&
      (nd.symChildren == null || nd.symChildren.isEmpty) &&
      (nd.groundChildren == null || nd.groundChildren.isEmpty) &&
      (nd.varChildren == null || nd.varChildren.isEmpty)
