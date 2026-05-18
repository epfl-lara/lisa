package lisa.maths.SetTheory.Types.ADTv2.support

final case class Time private (nanos: Long) {
  def -(other: Time): Time = Time(nanos - other.nanos)

  def millis: Long = nanos / 1000000L
  def seconds: Double = nanos / 1000000000.0

  override def toString: String = {
    val millis = nanos / 1000000L
    val seconds = millis / 1000L
    val remainingMillis = millis % 1000L
    s"${seconds}.${remainingMillis.toString.reverse.padTo(3, '0').reverse} s"
  }
}

object Time {
  private val counts = scala.collection.mutable.LinkedHashMap.empty[String, Int]
  private val totals = scala.collection.mutable.LinkedHashMap.empty[String, Long]
  private val totalsSquared = scala.collection.mutable.LinkedHashMap.empty[String, Double]
  private var resetTime = get()

  def get(): Time = Time(System.nanoTime())

  def register(label: String, elapsed: Time): Unit = {
    counts.update(label, counts.getOrElse(label, 0) + 1)
    totals.update(label, totals.getOrElse(label, 0L) + elapsed.nanos)
    val nanos = elapsed.nanos.toDouble
    totalsSquared.update(label, totalsSquared.getOrElse(label, 0.0) + nanos * nanos)
  }

  def measure[A](label: String)(body: => A): A = {
    val start = get()
    val result = body
    val end = get()
    register(label, end - start)
    result
  }

  def printSummary(): Unit = {
    println("===== ADTv2 timing summary =====")
    totals.toSeq.sortBy(_._1).foreach { (label, totalNanos) =>
      val total = Time(totalNanos)
      val n = counts(label)
      val mean = Time(totalNanos / n)
      val variance = math.max(0.0, (totalsSquared(label) / n) - math.pow(totalNanos.toDouble / n, 2))
      val stddev = Time(math.sqrt(variance).toLong)

      if (total.millis > 900L) {
        println(s"$total ($n calls, mean: $mean, stddev: $stddev)\t - $label")
      }
    }
    println("")
    // println(s"Measured total (overlapping): ${Time(totals.values.sum)}")
    println(s"Real time: ${get() - resetTime}")
  }

  def reset(): Unit = {
    totals.clear()
    counts.clear()
    totalsSquared.clear()
    resetTime = get()
  }
}
