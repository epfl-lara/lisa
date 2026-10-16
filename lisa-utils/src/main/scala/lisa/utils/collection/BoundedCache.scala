package lisa.utils.collection

import scala.annotation.tailrec
import scala.collection.mutable

/** Keep bounded memoized values. Confine each cache to one thread. */
sealed trait BoundedCache[K, V]:
  /** Return the cached value without refreshing its retention order. */
  def get(key: K): Option[V]

  /** Insert or replace a value, evicting entries when needed. */
  def put(key: K, value: V): Unit

  /** Remove a value without counting it as a capacity eviction. */
  def remove(key: K): Option[V]

  /** Release all entries and reset the eviction counter. */
  def clear(): Unit

  /** Count retained entries. */
  def size: Int

  /** Count capacity evictions since construction or the last clear. */
  def evictions: Long

  /** Reuse a value or cache a successful computation. Allow recursive cache use. */
  final def getOrElseUpdate(key: K)(compute: => V): V =
    get(key) match
      case Some(value) => value
      case None =>
        val value = compute
        put(key, value)
        value

object BoundedCache:
  /** Evict the oldest insertion when capacity is exceeded; disable retention at zero. */
  def fifo[K, V](capacity: Int): BoundedCache[K, V] = new Fifo(capacity)

  /**
   * Fill generations cyclically and clear the oldest on rotation. Search newest first.
   * Bound each generation separately; disable retention at zero capacity.
   * Keep hits and replacements in their original generation without promotion.
   */
  def generational[K, V](capacityPerGeneration: Int, generations: Int = 2): BoundedCache[K, V] =
    new Generational(capacityPerGeneration, generations)

  private final class Fifo[K, V](capacity: Int) extends BoundedCache[K, V]:
    require(capacity >= 0, "Cache capacity must be non-negative.")
    private val entries = mutable.LinkedHashMap.empty[K, V]
    private var removed = 0L

    def get(key: K): Option[V] = entries.get(key)
    def put(key: K, value: V): Unit =
      if capacity > 0 then
        entries(key) = value
        if entries.size > capacity then
          entries.remove(entries.head._1)
          removed += 1
    def remove(key: K): Option[V] = entries.remove(key)
    def size: Int = entries.size
    def evictions: Long = removed
    def clear(): Unit =
      entries.clear()
      removed = 0L

  private final class Generational[K, V](capacity: Int, count: Int) extends BoundedCache[K, V]:
    require(capacity >= 0, "Generation capacity must be non-negative.")
    require(count > 0, "A cache must have at least one generation.")
    require(capacity.toLong * count <= Int.MaxValue, "Total cache capacity must fit in an Int.")
    private val generations = Vector.fill(count)(mutable.HashMap.empty[K, V])
    private var current = 0
    private var retained = 0
    private var removed = 0L

    private def previous(index: Int): Int = if index == 0 then count - 1 else index - 1

    @tailrec private def lookup(key: K, index: Int, remaining: Int): Option[V] =
      if remaining == 0 then None
      else generations(index).get(key) match
        case found @ Some(_) => found
        case None => lookup(key, previous(index), remaining - 1)

    def get(key: K): Option[V] = lookup(key, current, count)

    def put(key: K, value: V): Unit =
      if capacity > 0 then
        // Replace in place so a key belongs to exactly one generation.
        var index = current
        var searched = 0
        while searched < count && !generations(index).contains(key) do
          index = previous(index)
          searched += 1
        if searched < count then generations(index)(key) = value
        else
          if generations(current).size == capacity then
            current = (current + 1) % count
            val expired = generations(current).size
            generations(current).clear()
            retained -= expired
            removed += expired
          generations(current)(key) = value
          retained += 1

    def remove(key: K): Option[V] =
      var index = current
      var searched = 0
      while searched < count do
        generations(index).remove(key) match
          case found @ Some(_) =>
            retained -= 1
            return found
          case None =>
            index = previous(index)
            searched += 1
      None

    def size: Int = retained
    def evictions: Long = removed
    def clear(): Unit =
      generations.foreach(_.clear())
      current = 0
      retained = 0
      removed = 0L
