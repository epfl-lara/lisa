package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import scala.collection.mutable

import Core.*

/**
 * The DISCOUNT (given-clause) saturation loop for Phase-1 ordered resolution + factoring.
 *
 * Two clause stores: a `passive` (unprocessed) set, kept in two lazy-deletion priority queues so the
 * next given clause can be picked by an age/weight ratio; and an `active` (processed) set scanned
 * linearly for inferences (term indexing is Phase 4). Each iteration selects a given clause, computes
 * its selected literals, moves it into active, generates all resolvents against the active set and all
 * factors of itself, and inserts the (canonicalised, non-tautological) survivors back into passive. It
 * stops at the empty clause `□` (refutation) or when the passive set empties (saturation); `maxGiven`
 * bounds the work otherwise.
 *
 * Phase-2 simplification adds θ-**subsumption** (via [[Subsumption.subsumes]]) and **unit deletion** (the
 * unit case of subsumption resolution, via [[Subsumption.unitDeletionResolvent]]), both against the active
 * set only (passive-redundant clauses are caught lazily when selected). One combined scan per direction:
 * *forward* (in [[forwardSimplify]]) discards or shrinks a new/just-selected clause; *backward* (in
 * [[backwardSimplify]]) deletes or shrinks active clauses, run before the given joins active. Subsumption
 * deletion needs no reconstruction (a deleted clause never enters `□`'s [[Justification]] DAG), and a
 * unit-deletion result is an ordinary resolvent (`Inference.resolve`), so it reconstructs with no new
 * machinery either. Demodulation and term indexing are still Phases 3 and 4. On a refutation the loop
 * returns the empty clause, whose DAG later feeds reconstruction.
 */
object Discount:
  enum Result:
    case Refutation(empty: Clause)
    case Saturated
    case Unknown

final class Discount(
    bank: TermBank,
    trail: Trail,
    ageRatio: Int = 1,
    weightRatio: Int = 1,
    factorAfterCheck: Boolean = false,
    forwardSubsumption: Boolean = true,
    backwardSubsumption: Boolean = true,
    forwardUnitDeletion: Boolean = true,
    backwardUnitDeletion: Boolean = true,
    // Off by default: with no term indexing (Phase 4), forward-simplifying every *generated* clause costs
    // an O(|active|) scan per clause and is empirically a net loss -- the mandatory selection-time pass
    // still catches every redundant clause before it activates. Revisit once indexing makes it cheap.
    // (seed-42 ablation: gen=67 refuted vs nogen=71, strictly more, no regressions. See Benchmarks.md.)
    // Governs forward subsumption *and* forward unit deletion at the generation point.
    forwardSimplifyAtGeneration: Boolean = false):
  import Discount.Result

  // Simplification counters (observability / benchmarks); reset at the start of each `saturate`.
  var forwardSubsumed: Int = 0
  var backwardSubsumed: Int = 0
  var forwardUnitDeleted: Int = 0
  var backwardUnitDeleted: Int = 0

  // Passive set: two views over the same clauses, with lazy deletion -- a clause selected via one
  // stays a stale entry in the other, skipped on pop. Age is just a FIFO queue: clauses are enqueued
  // in strictly increasing `id` order (ids are monotonic and each insertion is a fresh clause), so
  // dequeuing from the front already yields the oldest. Weight needs a real min-heap on (weight, id).
  private val byAge: mutable.Queue[Clause] = mutable.Queue.empty
  // Reversed for a min-heap (PriorityQueue is a max-heap): the lighter clause -- ties broken by the
  // smaller id, i.e. the older -- has the highest priority. A direct Int comparison, so no Tuple2 is
  // allocated (and no Int boxing) per heap comparison.
  private val byWeightOrder: Ordering[Clause] = (a, b) =>
    val w = Integer.compare(b.weight, a.weight)
    if w != 0 then w else Integer.compare(b.id, a.id)
  private val byWeight: mutable.PriorityQueue[Clause] = new mutable.PriorityQueue[Clause]()(using byWeightOrder)
  private val livePassive: IntOpenHashSet = new IntOpenHashSet() // ids still in passive
  private var balance: Int = 0 // age/weight alternation, Vampire-style

  // Active (processed) set, scanned linearly (indexing is Phase 4).
  private val active: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty

  // Ordering used only for the (optional) post-unification σ-maximality check on factors.
  private lazy val kbo: KBO = new KBO(bank)

  /**
   * Saturate `initial` (plus everything derived from it). Returns [[Result.Refutation]] with the empty
   * clause if `□` is derived, [[Result.Saturated]] if the passive set empties without one, or
   * [[Result.Unknown]] if the `maxGiven` given-clause budget or the `maxMillis` wall-clock budget is
   * reached first. The time budget is checked once per given clause (cheap), so the loop stops cleanly
   * rather than relying on the caller to abandon a runaway thread.
   */
  def saturate(initial: Seq[Clause], maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue): Result =
    byAge.clear(); byWeight.clear(); livePassive.clear(); active.clear(); balance = 0
    forwardSubsumed = 0; backwardSubsumed = 0; forwardUnitDeleted = 0; backwardUnitDeleted = 0
    val it = initial.iterator
    while it.hasNext do
      addPassive(it.next()) match
        case Some(empty) => return Result.Refutation(empty)
        case None => ()
    val checkTime: Boolean = maxMillis != Long.MaxValue
    val deadline: Long = if checkTime then System.nanoTime() + maxMillis * 1000000L else 0L
    var givenCount = 0
    while !livePassive.isEmpty && givenCount < maxGiven && (!checkTime || System.nanoTime() < deadline) do
      val gc = popGiven()
      // forward simplify the given against active: it may have been subsumed (skip) or shrunk by unit
      // deletion (process the shorter clause) by clauses that became active while it sat in passive.
      // A skip is not counted as a processed given (count activations only).
      (if forwardSubsumption || forwardUnitDeletion then forwardSimplify(gc) else Some(gc)) match
        case None => () // subsumed at selection: drop it
        case Some(g) =>
          if g.isEmpty then return Result.Refutation(g) // unit deletion closed the clause
          else
            givenCount += 1
            activate(g) match
              case Some(empty) => return Result.Refutation(empty)
              case None => ()
    if livePassive.isEmpty then Result.Saturated else Result.Unknown

  /** Canonicalise `c` and add it to passive; returns the empty clause if `c` is (or simplifies to) `□`.
   *  When [[forwardSimplifyAtGeneration]] is on, `c` is forward-simplified against active first (after the
   *  `□` check, so a derived empty clause is never lost): subsumed ⇒ discarded, shrunk ⇒ the shorter clause
   *  is enqueued. Off by default -- the given is forward-simplified at selection regardless. */
  private def addPassive(c: Clause): Option[Clause] =
    Inference.canonicalize(bank, c) match
      case None => None // tautology: discard
      case Some(cc0) =>
        if cc0.isEmpty then Some(cc0)
        else
          val simplified: Option[Clause] =
            if forwardSimplifyAtGeneration && (forwardSubsumption || forwardUnitDeletion) then forwardSimplify(cc0)
            else Some(cc0)
          simplified match
            case None => None // subsumed by an active clause: discard
            case Some(cc) =>
              if cc.isEmpty then Some(cc) // unit deletion closed it
              else
                byAge.enqueue(cc)
                byWeight.enqueue(cc)
                livePassive.add(cc.id)
                None

  /** Pick the next given clause by the age/weight ratio, removing it from passive: scan the chosen
   *  queue, skipping stale (already-selected) entries. A live clause is guaranteed when the passive set
   *  is non-empty (the caller checks `livePassive`), since every passive clause sits in both queues.
   *  The scan is inlined per queue rather than factored into a by-name helper, so no thunk is allocated
   *  per call. */
  private def popGiven(): Clause =
    if balance > 0 || (balance == 0 && ageRatio <= weightRatio) then
      balance -= ageRatio
      while byWeight.nonEmpty do
        val c: Clause = byWeight.dequeue()
        if takeLive(c) then return c
    else
      balance += weightRatio
      while byAge.nonEmpty do
        val c: Clause = byAge.dequeue()
        if takeLive(c) then return c
    throw new IllegalStateException("popGiven called on an empty passive set")

  /** If `c` is still live (in passive), mark it not-live and return `true`; if stale, return `false`. */
  private def takeLive(c: Clause): Boolean =
    if livePassive.contains(c.id) then { livePassive.remove(c.id); true }
    else false

  /** Move `gc` into active and generate all resolvents (against active) and factors (of itself).
   *  Backward simplification first deletes/shrinks active clauses using `gc` -- run before `gc` joins
   *  active (so it never simplifies itself) and before generation (so deleted clauses produce no
   *  inferences). A backward unit deletion that closes a clause to `□` is returned as a refutation. */
  private def activate(gc: Clause): Option[Clause] =
    val gSel: Array[Int] = gc.select(bank)
    if backwardSubsumption || backwardUnitDeletion then
      backwardSimplify(gc) match
        case Some(empty) => return Some(empty)
        case None => ()
    active += gc
    // resolution: gc's selected literals against each active clause's selected literals
    var ai = 0
    while ai < active.length do
      val a: Clause = active(ai)
      val aSel: Array[Int] = a.select(bank)
      var gi = 0
      while gi < gSel.length do
        var aj = 0
        while aj < aSel.length do
          Inference.resolve(bank, trail, gc, gSel(gi), a, aSel(aj)) match
            case Some(r) =>
              addPassive(r) match
                case Some(empty) => return Some(empty)
                case None => ()
            case None => ()
          aj += 1
        gi += 1
      ai += 1
    // factoring: each unordered pair of distinct selected, positive, non-equality literals, once
    // (positive factoring only; equalities get equality-factoring in Phase 3). A literal that unifies
    // with a selected (maximal) one is itself maximal, hence also selected, so pairing within the
    // selected set loses nothing. If `factorAfterCheck`, drop a factor whose kept literal is no longer
    // (KBO-)maximal under the unifier.
    var gi2 = 0
    while gi2 < gSel.length do
      val i: Int = gSel(gi2)
      if bank.isPositive(gc.literals(i)) && !isEquality(gc.literals(i)) then
        var gj = gi2 + 1
        while gj < gSel.length do
          val j: Int = gSel(gj)
          if !isEquality(gc.literals(j)) then
            Inference.factor(bank, trail, gc, i, j) match
              case Some(f) =>
                if !factorAfterCheck || keptMaximal(f, if i < j then i else i - 1) then
                  addPassive(f) match
                    case Some(empty) => return Some(empty)
                    case None => ()
              case None => ()
          gj += 1
      gi2 += 1
    None

  /** Forward simplify `m` against the active set in one scan (active only -- DISCOUNT does not
   *  forward-check passive): if some active clause subsumes `m`, return `None` (discard it); otherwise
   *  apply unit deletions by active units, returning the (possibly shrunk) clause -- `Some(□)` if a unit
   *  deletion closed it. A single pass: after a shrink the scan continues with the shorter clause, and any
   *  residual redundancy is caught when that clause is later selected. */
  private def forwardSimplify(m0: Clause): Option[Clause] =
    var m: Clause = m0
    var i = 0
    while i < active.length do
      val c: Clause = active(i)
      if forwardSubsumption && Subsumption.subsumes(bank, trail, c, m) then
        forwardSubsumed += 1
        return None // subsumed: discard `m`
      if forwardUnitDeletion && c.size == 1 then
        Subsumption.unitDeletionResolvent(bank, trail, c, m) match
          case Some(r) =>
            forwardUnitDeleted += 1
            val cr: Clause = Inference.canonicalize(bank, r).getOrElse(r)
            if cr.isEmpty then return Some(cr) // unit conflict closed the clause
            m = cr // continue the scan with the shrunk clause
          case None => ()
      i += 1
    Some(m)

  /** Backward simplify the active set using `gc` in one scan (`gc` not yet in active): delete each
   *  active clause `gc` subsumes, and shrink each that `gc` unit-deletes a literal from (the shrunk clause
   *  is re-added through [[addPassive]] after the scan, to avoid mutating `active` mid-iteration). Removal
   *  is swap-with-last + truncate (O(1)); `active` is unordered, so reordering is harmless, and the
   *  swapped-in element is re-checked by *not* advancing the index. Returns `Some(□)` if a backward unit
   *  deletion closes a clause. Deletion needs no reconstruction; a shrunk clause is an ordinary resolvent. */
  private def backwardSimplify(gc: Clause): Option[Clause] =
    val gcUnit: Boolean = gc.size == 1
    var shrunk: mutable.ArrayBuffer[Clause] = null // re-added after the scan (lazily allocated)
    var i = 0
    while i < active.length do
      val m: Clause = active(i)
      var removed = false
      if backwardSubsumption && Subsumption.subsumes(bank, trail, gc, m) then
        backwardSubsumed += 1
        removed = true
      else if backwardUnitDeletion && gcUnit then
        Subsumption.unitDeletionResolvent(bank, trail, gc, m) match
          case Some(r) =>
            backwardUnitDeleted += 1
            if shrunk == null then shrunk = mutable.ArrayBuffer.empty
            shrunk += r
            removed = true
          case None => ()
      if removed then
        active(i) = active(active.length - 1)
        active.remove(active.length - 1)
      else i += 1
    if shrunk != null then
      var k = 0
      while k < shrunk.length do
        addPassive(shrunk(k)) match
          case Some(empty) => return Some(empty)
          case None => ()
        k += 1
    None

  /** Whether `lit`'s atom is an equality `s = t` (factoring skips these; equality factoring is Phase 3). */
  private def isEquality(lit: Literal): Boolean =
    bank.headSymbol(bank.atomOf(lit)) == EqualitySymbol

  /** σ-maximality after-check: in the (already σ-applied) factor `f`, the kept literal must be maximal --
   *  no other literal's atom is strictly KBO-greater than it. (Maximal, not strictly: the merged literal
   *  may have an equal twin.) */
  private def keptMaximal(f: Clause, keptIdx: Int): Boolean =
    val keptAtom: Term = bank.atomOf(f.literals(keptIdx))
    var k = 0
    while k < f.literals.length do
      if k != keptIdx && kbo.compare(bank.atomOf(f.literals(k)), keptAtom) == Cmp.Gt then return false
      k += 1
    true
