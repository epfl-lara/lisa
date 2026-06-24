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

final class Discount(bank: TermBank, trail: Trail, ageRatio: Int = 1, weightRatio: Int = 1, factorAfterCheck: Boolean = false):
  import Discount.Result

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
      val gc = popGiven()
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
