package lisa.maths.SetTheory.Types.ADTv2.backends

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ADTSpec

/** Backend capability interface to adapt different LISA versions. */
trait Backend {
  type ADTHandle
  type TheoremHandle

  def defineADT(spec: ADTSpec): ADTHandle

  def theorem(name: String, statementRepr: String): TheoremHandle
}
