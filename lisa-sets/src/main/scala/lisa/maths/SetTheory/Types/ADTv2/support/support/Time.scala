package lisa.maths.SetTheory.Types.ADTv2.support

final case class Time private (nanos: Long) {
  def -(other: Time): Time = Time(nanos - other.nanos)

  def millis: Long = nanos / 1000000L
  def seconds: Double = nanos / 1000000000.0

  override def toString: String = {
    val millis = nanos / 1000000L
    val seconds = millis / 1000L
    val remainingMillis = millis % 1000L
    s"${seconds}.${remainingMillis.toString.reverse.padTo(3, '0').reverse}s"
  }
}

object Time {
  private val counts = scala.collection.mutable.LinkedHashMap.empty[String, Int]
  private val totals = scala.collection.mutable.LinkedHashMap.empty[String, Long]
  private val totalsSquared = scala.collection.mutable.LinkedHashMap.empty[String, Double]
  private val maxes = scala.collection.mutable.LinkedHashMap.empty[String, Long]
  private var resetTime = get()
  private var lastTime = get()
  private var active = true

  def get(): Time = Time(System.nanoTime())

  def register(label: String, elapsed: Time): Unit = {
    counts.update(label, counts.getOrElse(label, 0) + 1)
    totals.update(label, totals.getOrElse(label, 0L) + elapsed.nanos)
    maxes.update(label, math.max(maxes.getOrElse(label, 0L), elapsed.nanos))
    val nanos = elapsed.nanos.toDouble
    totalsSquared.update(label, totalsSquared.getOrElse(label, 0.0) + nanos * nanos)
  }

  def measure[A](label: String, is_active: Boolean = false)(body: => A): A = {
    // active = false
    val start = get()
    val result = body
    val end = get()
    // active = true
    if (active){
      register(label, end - start)
      if (is_active) log(s"Measured $label: ${end - start}")
    }
    result
  }

  def measureNow[A](label: String)(body: => A): A = {
    val start = get()
    val result = body
    val end = get()
    log(s"Measured $label: ${end - start}")
    result
  }

  def log(message: String): Unit = {
    if (active) {
      val t = get()
      println(s"[${t - resetTime} | ${t - lastTime}] $message")
      lastTime = t
    }
  }

  private def round(x: Double, decimals: Int): Double = {
    val factor = math.pow(10, decimals)
    math.round(x * factor) / factor
  }

  def printSummary(): Unit = {
    println("===== ADTv2 timing summary =====")

    // Build the rows as column tuples, then render them as an aligned table.
    val header = Seq("Total", "Calls", "Mean", "Max", "Stddev", "Label")
    val rows = totals.toSeq.sortBy(_._2).flatMap { (label, totalNanos) =>
      val total = Time(totalNanos)
      val n = counts(label)
      val mean = Time(totalNanos / n)
      val max = Time(maxes(label))
      val variance = math.max(0.0, (totalsSquared(label) / n) - math.pow(totalNanos.toDouble / n, 2))
      val stddevInPercent = round((math.sqrt(variance) * n * 100.0) / totalNanos, 2)

      if (total.millis > 900L) {
        Some(Seq(total.toString, n.toString, mean.toString, max.toString, s"$stddevInPercent%", label))
      } else {
        None
      }
    }

    if (rows.nonEmpty) {
      val widths = (header +: rows).transpose.map(_.map(_.length).max)
      def renderRow(cols: Seq[String]): String =
        cols.zip(widths).map((s, w) => s.padTo(w, ' ')).mkString("| ", " | ", " |")
      val separator = widths.map(w => "-" * (w + 2)).mkString("|", "|", "|")

      println(renderRow(header))
      println(separator)
      rows.foreach(cols => println(renderRow(cols)))
    }

    println("")
    // println(s"Measured total (overlapping): ${Time(totals.values.sum)}")
    println(s"Real time: ${get() - resetTime}")
  }

  def reset(): Unit = {
    totals.clear()
    counts.clear()
    totalsSquared.clear()
    maxes.clear()
    resetTime = get()
    lastTime = get()
  }
}
