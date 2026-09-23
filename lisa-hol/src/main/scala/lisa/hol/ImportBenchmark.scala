package lisa.hol

/** Runs a bounded HOL import without the diagnostic heap dump in `importMain`. */
object ImportBenchmark:
  def main(args: Array[String]): Unit =
    require(args.length == 2 || args.length == 3, "Usage: ImportBenchmark <export-prefix> <theorem-count> [start-index]")
    val startAt = args.lift(2).fold(0)(_.toInt)
    Import.importFromPrefix(args(0), args(1).toInt, failFast = true, startAt = startAt)
