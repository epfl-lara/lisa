package lisa.hol

import java.nio.file.Path

/** Read import settings once on first use; supply properties before initializing this object. */
object Config:
  // Proof retention and dependency preprocessing.

  /** Set the ordinary step capacity per generation; use zero for unbounded retention. */
  val stepCacheCapacity: Int = sys.props.get("lisa.hol.stepCache").fold(750000)(_.toInt)

  /** Set the number of cache generations; use zero for FIFO eviction. */
  val stepCacheGenerations: Int = sys.props.get("lisa.hol.stepCache.generations").fold(2)(_.toInt)

  /** Select shared dependencies by default; disable to retain no extra lemmas. */
  val precomputeLemmas: Boolean = sys.props.get("lisa.hol.precomputeLemmas").fold(true)(_.toBoolean)

  // HOL-to-Lisa conversion caches. Zero disables retention.

  val typeCacheCapacity: Int = sys.props.get("lisa.hol.typeCache").fold(4096)(_.toInt)
  val constantCacheCapacity: Int = sys.props.get("lisa.hol.constantCache").fold(4096)(_.toInt)

  // Profiling and replay accounting.

  /** Track distinct reconstructed IDs to distinguish new work from eviction replay. */
  val reconstructionStats: Boolean = sys.props.get("lisa.hol.reconstructionStats").exists(_.toBoolean)

  /** Write per-theorem rule costs; prefer the property over the environment fallback. */
  val statisticsPath: Option[Path] = sys.props.get("lisa.hol.stats").orElse(sys.env.get("LISA_HOL_STATS")).map(Path.of(_))

  /** Write individual step costs and sequent shapes when a path is supplied. */
  val stepStatisticsPath: Option[Path] = sys.props.get("lisa.hol.steps").map(Path.of(_))

  /** Omit step-profile records below this allocation threshold in bytes. */
  val stepStatisticsMinBytes: Long = sys.props.get("lisa.hol.steps.minBytes").fold(0L)(_.toLong)

  /** Start step profiling at this named theorem's proof ID, not its ordinal in the names file. */
  val stepStatisticsFromTheorem: Long = sys.props.get("lisa.hol.steps.fromTheorem").fold(0L)(_.toLong)

  /** Select comma-separated HOL rule names for individual step profiling. */
  val stepStatisticsRules: Set[String] =
    sys.props.get("lisa.hol.steps.rules").fold(StepStatistics.rules)(_.split(",").iterator.map(_.trim).filter(_.nonEmpty).toSet)
