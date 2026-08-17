package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import scala.collection.mutable

import Core.*

/** The unprocessed clauses, held in two queues over the same clauses: one by age, one by weight. [[pop]]
  * alternates between them in the ratio [[SearchOptions.ageRatio]] to [[SearchOptions.weightRatio]], an age
  * share of at least one being what keeps selection fair and the loop refutation-complete.
  *
  * Deletion is lazy: a clause popped from one queue stays in the other as a stale entry and is skipped when
  * reached, so `live` is the authority on membership and a pop dequeues until it finds a live clause.
  *
  * The age queue is a plain FIFO, ids being monotonic and every insertion fresh, so its front is already the
  * oldest. The weight queue needs a heap, and `mutable.PriorityQueue` is a max-heap, so its ordering is
  * reversed to bring out the lightest clause, ties broken by the smaller id. */
final class PassiveSet(opts: SearchOptions):
  import opts.{ageRatio, weightRatio, nonGoalWeightCoefficient}

  /** The weight-queue key: the raw clause weight, penalised by [[SearchOptions.nonGoalWeightCoefficient]]
    * unless the clause is derived from the goal (Vampire's `nongoal_weight_coefficient`). Weights are small,
    * so the product never overflows. */
  private def selectionWeight(c: Clause): Int = if c.isGoal then c.weight else c.weight * nonGoalWeightCoefficient

  private val byAge: mutable.Queue[Clause] = mutable.Queue.empty
  private val byWeightOrder: Ordering[Clause] = (a, b) =>
    val w = Integer.compare(selectionWeight(b), selectionWeight(a))
    if w != 0 then w else Integer.compare(b.id, a.id)
  private val byWeight: mutable.PriorityQueue[Clause] = new mutable.PriorityQueue[Clause]()(using byWeightOrder)
  private val live: IntOpenHashSet = new IntOpenHashSet() // ids still in passive
  private var balance: Int = 0 // age/weight alternation

  private var _peakSize: Int = 0
  private var _totalEnqueued: Int = 0

  /** Max live size reached over this saturation. */
  def peakSize: Int = _peakSize

  /** Total clauses ever enqueued over this saturation. */
  def totalEnqueued: Int = _totalEnqueued

  def isEmpty: Boolean = live.isEmpty
  def nonEmpty: Boolean = !live.isEmpty

  /** Add `c` to both queues. The caller is responsible for canonicalising/simplifying it first. */
  def enqueue(c: Clause): Unit =
    byAge.enqueue(c)
    byWeight.enqueue(c)
    live.add(c.id)
    _totalEnqueued += 1
    val n = live.size()
    if n > _peakSize then _peakSize = n

  /** Pick and remove the next given clause by the age/weight ratio: scan the chosen queue, skipping stale
    * (already-selected) entries. A live clause is guaranteed when the set is non-empty, since every passive
    * clause sits in *both* queues. The scan is inlined per queue rather than factored into a by-name helper,
    * so no thunk is allocated per call. */
  def pop(): Clause =
    if balance > 0 || (balance == 0 && ageRatio <= weightRatio) then
      balance -= ageRatio
      while byWeight.nonEmpty do
        val c: Clause = byWeight.dequeue()
        if take(c) then return c
    else
      balance += weightRatio
      while byAge.nonEmpty do
        val c: Clause = byAge.dequeue()
        if take(c) then return c
    throw new IllegalStateException("PassiveSet.pop called on an empty passive set")

  /** If `c` is still live, mark it not-live and return `true`; if stale, return `false`. */
  private def take(c: Clause): Boolean =
    if live.contains(c.id) then { live.remove(c.id); true }
    else false
