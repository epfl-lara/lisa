package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import scala.collection.mutable

import Core.*

/**
 * The **passive** (unprocessed) clause set of the DISCOUNT loop, and the age/weight policy that decides which
 * of its clauses becomes the next given.
 *
 * Two views over the same clauses, with **lazy deletion**: a clause popped via one queue stays behind as a
 * stale entry in the other and is skipped when reached. `livePassive` is the authority on membership, so a
 * pop is "dequeue until a live one turns up".
 *
 *   - **age** is just a FIFO queue. Clauses are enqueued in strictly increasing `id` order (ids are monotonic
 *     and every insertion is a freshly built clause), so the front is already the oldest and no heap is needed.
 *   - **weight** needs a real min-heap on `(weight, id)`. `mutable.PriorityQueue` is a *max*-heap, so the
 *     ordering is reversed: the lighter clause, with ties broken by the smaller id, i.e. the older, comes out
 *     first. The comparison is on raw `Int`s, so no `Tuple2` is allocated and no `Int` boxed per heap step.
 *
 * `balance` alternates between the two Vampire-style, in the ratio [[SearchOptions.ageRatio]] :
 * [[SearchOptions.weightRatio]]. An age slice of at least 1 is what makes clause selection *fair*, and hence
 * the loop refutation-complete: no clause can be starved forever by an endless supply of lighter ones.
 */
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

  /** Max live size reached since the last [[clear]]. */
  def peakSize: Int = _peakSize

  /** Total clauses ever enqueued since the last [[clear]]. */
  def totalEnqueued: Int = _totalEnqueued

  def isEmpty: Boolean = live.isEmpty
  def nonEmpty: Boolean = !live.isEmpty

  /** Drop everything, for reuse across saturations. */
  def clear(): Unit =
    byAge.clear(); byWeight.clear(); live.clear(); balance = 0
    _peakSize = 0; _totalEnqueued = 0

  /** Add `c` to both queues. The caller is responsible for canonicalising/simplifying it first. */
  def enqueue(c: Clause): Unit =
    require(!c.isQuery, "PassiveSet.enqueue: a query clause is a throwaway index key with a shared sentinel " +
      "id; `live` is keyed by id, so enqueuing one would make every query clause look already-selected")
    byAge.enqueue(c)
    byWeight.enqueue(c)
    live.add(c.id)
    _totalEnqueued += 1
    val n = live.size()
    if n > _peakSize then _peakSize = n

  /**
   * Pick and remove the next given clause by the age/weight ratio: scan the chosen queue, skipping stale
   * (already-selected) entries. A live clause is guaranteed when the set is non-empty, since every passive
   * clause sits in *both* queues. The scan is inlined per queue rather than factored into a by-name helper,
   * so no thunk is allocated per call.
   */
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
