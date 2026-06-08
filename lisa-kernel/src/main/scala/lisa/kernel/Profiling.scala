package lisa.kernel

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.LongAdder
import scala.jdk.CollectionConverters._

object Profiling {
  private final class Entry {
    val nanos = new LongAdder()
    val count = new LongAdder()
  }

  val enabled: Boolean =
    sys.props.get("lisa.profile").exists(v => v.nonEmpty && v != "0" && v != "false") ||
      sys.env.get("LISA_PROFILE").exists(v => v.nonEmpty && v != "0" && v != "false")

  private val entries = new ConcurrentHashMap[String, Entry]()

  if (enabled) {
    sys.addShutdownHook {
      println(report())
    }
  }

  @inline def time[A](name: String)(body: => A): A =
    if (!enabled) body
    else {
      val start = System.nanoTime()
      try body
      finally add(name, System.nanoTime() - start)
    }

  def add(name: String, nanos: Long): Unit = {
    val e = entries.computeIfAbsent(name, _ => new Entry())
    e.nanos.add(nanos)
    e.count.increment()
  }

  def count(name: String, n: Long = 1): Unit = {
    if (enabled) {
      val e = entries.computeIfAbsent(name, _ => new Entry())
      e.count.add(n)
    }
  }

  private def defaultLimit: Int =
    sys.props.get("lisa.profile.limit")
      .orElse(sys.env.get("LISA_PROFILE_LIMIT"))
      .flatMap(_.toIntOption)
      .getOrElse(80)

  def report(limit: Int = defaultLimit): String = {
    val rows = entries.asScala.iterator
      .map { case (name, e) =>
        val count = e.count.sum()
        val nanos = e.nanos.sum()
        (name, count, nanos)
      }
      .toSeq
      .sortBy(-_._3)
      .take(limit)

    val body = rows.map { case (name, count, nanos) =>
      val ms = nanos / 1000000.0
      val avgUs = if (count == 0) 0.0 else nanos / count / 1000.0
      f"$ms%10.2f ms  $count%9d  $avgUs%10.2f us  $name"
    }

    val countOnly = entries.asScala.iterator
      .map { case (name, e) => (name, e.count.sum(), e.nanos.sum()) }
      .filter { case (_, count, nanos) => count > 0 && nanos == 0 }
      .toSeq
      .sortBy(-_._2)
      .take(30)
      .map { case (name, count, _) => f"count-only            $count%9d              $name" }

    ("LISA profile: total ms | count | avg us | name" +: (body ++ countOnly)).mkString(System.lineSeparator())
  }
}
