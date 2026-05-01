package lisa.maths.SetTheory.Types.ADTv2.basics

import lisa.maths.SetTheory.Types.ADTv2.API
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

object Void {

  val void = API.defineAST(
    name = "void",
    typeVars = Seq.empty,
    constructors = Seq.empty
  )
}