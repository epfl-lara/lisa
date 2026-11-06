package lisa.hol

/** Run a bounded import, including the dependencies of any skipped names. */
object ImportBenchmark:
  def main(args: Array[String]): Unit =
    require(args.length == 2 || args.length == 3, "Usage: ImportBenchmark <export-prefix> <theorem-count> [start-index]")
    val startAt = args.lift(2).fold(0)(_.toInt)
    Import.importFromPrefix(args(0), args(1).toInt, startAt = startAt)
