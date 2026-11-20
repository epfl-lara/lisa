package lisa.maths.SetTheory.Types.ADT.support

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.TypingHelpers.FunctionalClass
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional

/**
 * Retains the named typing theorem alongside the proof used by the typechecker.
 */
abstract class TypedADTConstant[S: Sort](id: Identifier, typ: FunctionalClass, val intro: Theorem) extends TypedConstantFunctional[S](id, typ, intro.thm)
