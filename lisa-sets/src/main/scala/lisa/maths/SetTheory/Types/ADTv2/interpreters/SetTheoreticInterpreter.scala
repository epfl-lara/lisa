package lisa.maths.SetTheory.Types.ADTv2.interpreters

import lisa.maths.SetTheory.Types.ADTv2.backends.Backend
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ADTSpec

/** Set-theoretic interpreter for ADT v2 specs. */
object SetTheoreticInterpreter {

  final case class Result(adt: Any)

  def interpret(spec: ADTSpec, backend: Backend): Result = {
    val handle = backend.defineADT(spec)
    Result(handle)
  }
}
