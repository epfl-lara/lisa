package lisa.hol

import java.lang.management.ManagementFactory
import java.nio.file.{Files, Path, StandardOpenOption}
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** Measure importer work without retaining terms or proof objects. */
object ImportStatistics:
  final case class Sample(cpuNanos: Long, allocatedBytes: Long, gcMillis: Long):
    def -(previous: Sample): Sample = Sample(
      if cpuNanos < 0 || previous.cpuNanos < 0 then -1 else cpuNanos - previous.cpuNanos,
      if allocatedBytes < 0 || previous.allocatedBytes < 0 then -1 else allocatedBytes - previous.allocatedBytes,
      gcMillis - previous.gcMillis
    )

  private val thread = ManagementFactory.getThreadMXBean
  private val allocation = thread match
    case bean: com.sun.management.ThreadMXBean if bean.isThreadAllocatedMemorySupported =>
      if !bean.isThreadAllocatedMemoryEnabled then bean.setThreadAllocatedMemoryEnabled(true)
      Some(bean)
    case _ => None
  if thread.isCurrentThreadCpuTimeSupported && !thread.isThreadCpuTimeEnabled then thread.setThreadCpuTimeEnabled(true)
  private val collectors = ManagementFactory.getGarbageCollectorMXBeans.asScala.toVector

  /** Sample main-thread CPU/allocation and process-wide collection time; use -1 when unsupported. */
  def sample(): Sample = Sample(cpu(), allocated(), collectors.map(_.getCollectionTime.max(0L)).sum)
  private def cpu(): Long = if thread.isCurrentThreadCpuTimeSupported then thread.getCurrentThreadCpuTime else -1L
  private def allocated(): Long = allocation.fold(-1L)(_.getThreadAllocatedBytes(Thread.currentThread().getId))

  private[hol] final case class Cost(count: Long, exceptions: Long, wallNanos: Long, cpuNanos: Long, bytes: Long, maxNanos: Long, maxStep: Long,
      maxBytes: Long, maxAllocationStep: Long)

/** Collect optional exclusive rule/phase costs; subtract nested work rather than counting it twice. */
private[hol] final class ImportStatistics(output: Option[Path] = None) extends AutoCloseable:
  import ImportStatistics.*

  private val writer = output.map: path =>
    val out = Files.newBufferedWriter(path, StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE)
    out.write("theorem_id,theorem,phase,count,exceptions,wall_ns,cpu_ns,allocated_bytes,max_wall_ns,max_step,max_allocated_bytes,max_allocation_step\n")
    out
  private val totals = mutable.Map.empty[String, Cost]
  private final class Frame:
    var wall = 0L
    var cpu = 0L
    var bytes = 0L
  private var stack = List.empty[Frame]

  /** Measure a phase only when detailed output was requested; retain failure costs too. */
  def measure[A](phase: String, step: Long)(body: => A): A =
    if writer.isEmpty then body
    else
      val frame = new Frame
      stack = frame :: stack
      val start = System.nanoTime()
      val startCpu = cpu()
      val startBytes = allocated()
      var failed = true
      try
        val result = body
        failed = false
        result
      finally
        val wall = System.nanoTime() - start
        val endCpu = cpu()
        val endBytes = allocated()
        val cpuTime = if startCpu < 0 || endCpu < 0 then -1L else endCpu - startCpu
        val bytes = if startBytes < 0 || endBytes < 0 then -1L else endBytes - startBytes
        stack = stack.tail
        stack.headOption.foreach: parent =>
          parent.wall += wall
          parent.cpu += cpuTime
          parent.bytes += bytes
        val exclusive = wall - frame.wall
        val old = totals.getOrElse(phase, Cost(0, 0, 0, 0, 0, 0, -1, -1, -1))
        val exclusiveBytes = if bytes < 0 then -1 else bytes - frame.bytes
        totals(phase) = Cost(
          old.count + 1, old.exceptions + (if failed then 1 else 0), old.wallNanos + exclusive,
          if cpuTime < 0 then -1 else old.cpuNanos + cpuTime - frame.cpu,
          if bytes < 0 then -1 else old.bytes + bytes - frame.bytes,
          old.maxNanos.max(exclusive), if exclusive > old.maxNanos then step else old.maxStep,
          old.maxBytes.max(exclusiveBytes), if exclusiveBytes > old.maxBytes then step else old.maxAllocationStep
        )

  /** Flush one theorem's costs, including failed attempts, and release its counters. */
  def finish(id: Long, name: String): Unit =
    require(stack.isEmpty)
    writer.foreach: out =>
      val quoted = "\"" + name.replace("\"", "\"\"") + "\""
      totals.toSeq.sortBy(_._1).foreach: (phase, cost) =>
        out.write(s"$id,$quoted,$phase,${cost.count},${cost.exceptions},${cost.wallNanos},${cost.cpuNanos},${cost.bytes},${cost.maxNanos},${cost.maxStep},${cost.maxBytes},${cost.maxAllocationStep}\n")
      out.flush()
    totals.clear()

  /** Close the optional CSV output. */
  def close(): Unit = closeAll(writer.toList)
