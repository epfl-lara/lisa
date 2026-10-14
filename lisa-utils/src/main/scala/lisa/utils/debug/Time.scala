package lisa.utils.debug

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

  // A node aggregates every (dynamic) occurrence of `label` reached through the
  // same parent path. `measure` pushes/pops; `register` adds a leaf to the
  // current top. This assumes measurements are not interleaved across threads.
  private final class Node(val label: String) {
    var totalNanos: Long = 0L
    var count: Int = 0
    var maxNanos: Long = 0L
    var totalSquaredNanos: Double = 0.0
    val children = scala.collection.mutable.LinkedHashMap.empty[String, Node]
    def record(elapsed: Long): Unit = {
      totalNanos += elapsed
      count += 1
      maxNanos = math.max(maxNanos, elapsed)
      totalSquaredNanos += elapsed.toDouble * elapsed.toDouble
    }
    def childTotal: Long = children.values.foldLeft(0L)(_ + _.totalNanos)
    def stddevPercent: Double =
      if (count <= 1 || totalNanos <= 0) 0.0
      else {
        val mean = totalNanos.toDouble / count
        val variance = math.max(0.0, totalSquaredNanos / count - mean * mean)
        math.sqrt(variance) * 100.0 / mean
      }
  }
  private val rootNode = new Node("<root>")
  private var stack: List[Node] = List(rootNode)

  inline def get(): Time = Time(System.nanoTime())

  private def accumulateFlat(label: String, elapsedNanos: Long): Unit = {
    counts.update(label, counts.getOrElse(label, 0) + 1)
    totals.update(label, totals.getOrElse(label, 0L) + elapsedNanos)
    maxes.update(label, math.max(maxes.getOrElse(label, 0L), elapsedNanos))
    val nanos = elapsedNanos.toDouble
    totalsSquared.update(label, totalsSquared.getOrElse(label, 0.0) + nanos * nanos)
  }

  def register(label: String, elapsed: Time, is_logged: Boolean = false): Unit = {
    accumulateFlat(label, elapsed.nanos)
    val node = stack.head.children.getOrElseUpdate(label, new Node(label))
    node.record(elapsed.nanos)
    if (is_logged) log(s"Register $label: $elapsed")
  }
  def register(label: String, content: String, elapsed: Time): Unit = {
    register(label, elapsed)
    log(s"Register $label: $elapsed with $content")
  }

  def measure[A](label: String, is_logged: Boolean = false, treeOnly: Boolean = false)(body: => A): A = {
    val node = stack.head.children.getOrElseUpdate(label, new Node(label))
    stack = node :: stack
    val start = get()
    try body
    finally {
      val elapsed = get().nanos - start.nanos
      stack = stack.tail
      node.record(elapsed)
      if (!treeOnly) accumulateFlat(label, elapsed)
      if (is_logged) log(s"Measured $label: ${Time(elapsed)}")
    }
  }
  def measure[A](label: String, content: String, treeOnly: Boolean)(body: => A): A = {
    val node = stack.head.children.getOrElseUpdate(label, new Node(label))
    stack = node :: stack
    val start = get()
    try body
    finally {
      val elapsed = get().nanos - start.nanos
      stack = stack.tail
      node.record(elapsed)
      if (!treeOnly) accumulateFlat(label, elapsed)
      log(s"Measured $label: ${Time(elapsed)} with $content")
    }
  }
  def measureTreeOnly[A](label: String, is_logged: Boolean = false)(body: => A): A =
    measure(label, is_logged, treeOnly = true)(body)

  def measure[A](label: String, content: String)(body: => A): A =
    measure(label, content, treeOnly = false)(body)

  def log(message: String): Unit = {
    val t = get()
    println(s"[${t - resetTime} | ${t - lastTime}] $message")
    lastTime = t
  }

  private def round(x: Double, decimals: Int): Double = {
    val factor = math.pow(10, decimals)
    math.round(x * factor) / factor
  }

  def printSummary(minMillis: Long = 900L): Unit = {
    println("===== Timing summary =====")

    val header = Seq("Total", "Calls", "Mean", "Max", "Stddev", "Label")
    val rows = totals.toSeq.sortBy(_._2).flatMap { (label, totalNanos) =>
      val total = Time(totalNanos)
      val n = counts(label)
      val mean = Time(totalNanos / n)
      val max = Time(maxes(label))
      val variance = math.max(0.0, (totalsSquared(label) / n) - math.pow(totalNanos.toDouble / n, 2))
      val stddevInPercent = round((math.sqrt(variance) * n * 100.0) / totalNanos, 2)

      if (total.millis > minMillis) {
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
    println(s"Real time: ${get() - resetTime}")
  }

  def printTree(
      maxDepth: Int = 100,
      minMillis: Long = 200L,
      minPercent: Double = 0.0,
      selfAsChild: Boolean = false,
      showSelf: Boolean = false,
      showMax: Boolean = false,
      showStddev: Boolean = true,
      showCalls: Boolean = true,
      showRoot: Boolean = true,
      blacklist: Seq[String] = Seq.empty,
      whitelist: Seq[String] = Seq.empty
  ): Unit = {
    println("===== Timing tree =====")
    val rootTotal = rootNode.childTotal
    val threshold = minMillis * 1000000L
    val blackset = blacklist.toSet
    val whiteset = whitelist.toSet

    val realNanos = get().nanos - resetTime.nanos
    val displayRoot = new Node("<root>")
    displayRoot.totalNanos = realNanos
    displayRoot.count = 1
    displayRoot.children ++= rootNode.children

    def keep(node: Node, parentTotal: Long): Boolean =
      node.totalNanos >= threshold && (node.totalNanos * 100.0 >= minPercent * parentTotal)

    def selfLeaf(node: Node): Node = {
      val n = new Node("(self)")
      n.record(node.totalNanos - node.childTotal)
      n
    }

    val lines = scala.collection.mutable.ArrayBuffer.empty[(String, Node, Long)]
    def collect(node: Node, prefix: String, isLast: Boolean, depth: Int, parentTotal: Long, inWhite: Boolean): Unit = {
      if (blackset.contains(node.label)) return
      if (depth > maxDepth || !keep(node, parentTotal)) return
      val nowInWhite = inWhite || whiteset.contains(node.label)
      val show = whiteset.isEmpty || nowInWhite
      val realChildren = node.children.values.toSeq
      val withSelf =
        if (selfAsChild && realChildren.nonEmpty) realChildren :+ selfLeaf(node)
        else realChildren
      val visible = withSelf.filter(keep(_, node.totalNanos)).sortBy(-_.totalNanos)
      if (show) {
        val connector = if (node eq displayRoot) "" else if (isLast) "└─ " else "├─ "
        lines += ((prefix + connector + node.label, node, parentTotal))
        val childPrefix = if (node eq displayRoot) prefix else prefix + (if (isLast) "   " else "│  ")
        visible.zipWithIndex.foreach { (c, i) =>
          collect(c, childPrefix, i == visible.size - 1, depth + 1, node.totalNanos, nowInWhite)
        }
      } else {
        visible.zipWithIndex.foreach { (c, i) =>
          collect(c, prefix, i == visible.size - 1, depth, node.totalNanos, nowInWhite)
        }
      }
    }
    if (showRoot) {
      collect(displayRoot, "", isLast = true, depth = 0, parentTotal = realNanos, inWhite = false)
    } else {
      val top = rootNode.children.values.toSeq.filter(keep(_, rootTotal)).sortBy(-_.totalNanos)
      top.zipWithIndex.foreach { (c, i) => collect(c, "", i == top.size - 1, 0, rootTotal, inWhite = false) }
    }

    if (lines.isEmpty) { println("(no measurements)"); return }

    final case class Col(header: String, width: Int, value: (Node, Long) => String)
    val cols = scala.collection.mutable.ArrayBuffer[Col](
      Col("Total", 8, (n, _) => Time(n.totalNanos).toString),
      Col("%", 6, (n, p) => f"${if (p > 0) n.totalNanos * 100.0 / p else 100.0}%5.1f%%")
    )
    if (showSelf) cols += Col("Self", 9, (n, _) => Time(n.totalNanos - n.childTotal).toString)
    if (showMax) cols += Col("Max", 9, (n, _) => Time(n.maxNanos).toString)
    if (showStddev) cols += Col("Stddev", 6, (n, _) => f"${n.stddevPercent}%5.1f%%")
    if (showCalls) cols += Col("Calls", 5, (n, _) => f"${n.count}%d")

    def cell(s: String, w: Int): String = s.reverse.padTo(w, ' ').reverse
    println(cols.map(c => cell(c.header, c.width)).mkString("| ", " | ", " | Label"))
    println(cols.map(c => "-" * (c.width + 2)).mkString("|", "|", "|----"))
    lines.foreach { (label, node, parentTotal) =>
      val cells = cols.map(c => cell(c.value(node, parentTotal), c.width))
      println(cells.mkString("| ", " | ", s" | $label"))
    }
    println("")
  }

  def reset(): Unit = {
    totals.clear()
    counts.clear()
    totalsSquared.clear()
    maxes.clear()
    rootNode.children.clear()
    stack = List(rootNode)
    resetTime = get()
    lastTime = get()
  }
}
