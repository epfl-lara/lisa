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
 * No simplification (subsumption / demodulation) and no term indexing yet -- Phases 2 and 4. On a
 * refutation the loop returns the empty clause, whose [[Justification]] DAG later feeds reconstruction.
 */
object Discount:
  enum Result:
    case Refutation(empty: Clause)
    case Saturated
    case Unknown

final class Discount(bank: TermBank, trail: Trail, ageRatio: Int = 1, weightRatio: Int = 1):
  import Discount.Result

  // Passive set: two min-heaps over the same clauses (age = id; weight = (weight, id)), with lazy
  // deletion -- a clause selected via one heap stays a stale entry in the other, skipped on pop.
  private val byAge: mutable.PriorityQueue[Clause] =
    new mutable.PriorityQueue[Clause]()(using Ordering.by[Clause, Int](_.id).reverse)
  private val byWeight: mutable.PriorityQueue[Clause] =
    new mutable.PriorityQueue[Clause]()(using Ordering.by[Clause, (Int, Int)](c => (c.weight, c.id)).reverse)
  private val livePassive: IntOpenHashSet = new IntOpenHashSet() // ids still in passive
  private var balance: Int = 0 // age/weight alternation, Vampire-style

  // Active (processed) set, scanned linearly (indexing is Phase 4).
  private val active: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty

  /**
   * Saturate `initial` (plus everything derived from it). Returns [[Result.Refutation]] with the empty
   * clause if `□` is derived, [[Result.Saturated]] if the passive set empties without one, or
   * [[Result.Unknown]] if `maxGiven` given-clause activations are reached first.
   */
  def saturate(initial: Seq[Clause], maxGiven: Int = Int.MaxValue): Result =
    byAge.clear(); byWeight.clear(); livePassive.clear(); active.clear(); balance = 0
    val it = initial.iterator
    while it.hasNext do
      addPassive(it.next()) match
        case Some(empty) => return Result.Refutation(empty)
        case None => ()
    var givenCount = 0
    while !livePassive.isEmpty && givenCount < maxGiven do
      popGiven() match
        case None => return Result.Saturated // no live clause left (shouldn't happen here)
        case Some(gc) =>
          givenCount += 1
          activate(gc) match
            case Some(empty) => return Result.Refutation(empty)
            case None => ()
    if livePassive.isEmpty then Result.Saturated else Result.Unknown

  /** Canonicalise `c` and add it to passive; returns the empty clause if `c` canonicalises to `□`. */
  private def addPassive(c: Clause): Option[Clause] =
    Inference.canonicalize(bank, c) match
      case None => None // tautology: discard
      case Some(cc) =>
        if cc.isEmpty then Some(cc)
        else
          byAge.enqueue(cc)
          byWeight.enqueue(cc)
          livePassive.add(cc.id)
          None

  /** Pick the next given clause by the age/weight ratio, removing it from passive. */
  private def popGiven(): Option[Clause] =
    if livePassive.isEmpty then None
    else if balance > 0 || (balance == 0 && ageRatio <= weightRatio) then
      balance -= ageRatio
      popLive(byWeight)
    else
      balance += weightRatio
      popLive(byAge)

  /** Dequeue from `pq`, skipping stale (already-selected) entries; mark the result not-live. */
  private def popLive(pq: mutable.PriorityQueue[Clause]): Option[Clause] =
    while pq.nonEmpty do
      val c: Clause = pq.dequeue()
      if livePassive.contains(c.id) then
        livePassive.remove(c.id)
        return Some(c)
    None

  /** Move `gc` into active and generate all resolvents (against active) and factors (of itself). */
  private def activate(gc: Clause): Option[Clause] =
    val gSel: Array[Int] = gc.select(bank)
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
    // factoring: gc's selected literal against every other literal of gc (factor rejects mismatches)
    var gi2 = 0
    while gi2 < gSel.length do
      val i: Int = gSel(gi2)
      var j = 0
      while j < gc.literals.length do
        if j != i then
          Inference.factor(bank, trail, gc, i, j) match
            case Some(f) =>
              addPassive(f) match
                case Some(empty) => return Some(empty)
                case None => ()
            case None => ()
        j += 1
      gi2 += 1
    None
