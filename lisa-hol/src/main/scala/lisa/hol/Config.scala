package lisa.hol

import java.nio.file.Path

/** Read proof-retention settings once; supply properties before initializing this object. */
object Config:
  /** Keep ordinary steps local to each named proof unless another mode is requested. */
  val proofCacheMode: String = sys.props.getOrElse("lisa.hol.proofCache", "local")

  /** Select shared dependencies by default; disable to retain no extra lemmas. */
  val precomputeLemmas: Boolean = sys.props.get("lisa.hol.precomputeLemmas").fold(true)(_.toBoolean)

  /** Read selected IDs from a sidecar in the explicit filtered-cache mode. */
  val lemmaPath: Option[Path] = sys.props.get("lisa.hol.lemmas").map(Path.of(_))
