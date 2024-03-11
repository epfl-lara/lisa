package lisa.utils.memoization

case class MemoizationStats(hits: Int, miss: Int, faulted: Int):
    def withHit = MemoizationStats(hits + 1, miss, faulted)
    def withMiss = MemoizationStats(hits, miss + 1, faulted)
    def withFault = MemoizationStats(hits, miss, faulted + 1)

case object InfiniteRecursionDetectedException extends Exception

class Memoized[From, To](fun: From => To) extends Function[From, To]:
  private val visited = scala.collection.mutable.HashSet.empty[From]
  private val memory = scala.collection.mutable.HashMap.empty[From, To]
  private var stats = MemoizationStats(0, 0, 0)

  protected def handleFault(): To =
    throw InfiniteRecursionDetectedException

  def apply(v: From): To = 
    val stored = memory.get(v)
    val seen = visited.contains(v)
    if stored.isEmpty then
      // compute
      visited.add(v)
      if seen then
          stats = stats.withFault
          handleFault()
      else
          stats = stats.withMiss
          memory.update(v, fun(v))
    else
      stats = stats.withHit
    memory(v)

class MemoizedWithDefault[From, To](fun: From => To, default: To) extends Memoized[From, To](fun):
  override def handleFault(): To = default

def memoized[A, B](f: A => B): A => B = Memoized(f)
def memoized[A, B](f: A => B, default: B): A => B = MemoizedWithDefault(f, default)
