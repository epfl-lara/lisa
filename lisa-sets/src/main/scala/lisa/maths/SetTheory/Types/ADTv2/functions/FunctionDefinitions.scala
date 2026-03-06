package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.FunctionSpec

/** Entry points for defining functions over ADT v2 values. */
object FunctionDefinitions {

  final case class DefinedFunction(name: String)

  def define(spec: FunctionSpec): DefinedFunction =
    DefinedFunction(spec.name)
}
