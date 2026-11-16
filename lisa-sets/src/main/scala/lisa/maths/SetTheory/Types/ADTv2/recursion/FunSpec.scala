package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.FunSpecBase
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution

class FunSpec(
    functionName: String,
    typeVariablesSeq: Seq[Variable[Ind]],
    adt: SemanticADT,
    argType: Expr[Ind],
    val typeSubstitutions: Seq[TypeSubstitution],
    val selfPlaceholder: Variable[Ind],
    patternMatching: PatternSystem,
    returnType: Expr[Ind]
) extends FunSpecBase(functionName, typeVariablesSeq, adt, argType, patternMatching, returnType) {

  // The candidate the defining predicate is stated about is exactly the
  // self-reference: both denote the function being defined. With this choice
  // `bodyFor(pattern, placeholder) == pattern.body`.
  override val placeholder: Variable[Ind] = selfPlaceholder

  validateParameters()

  protected def bodyFor(pattern: Pattern, fVar: Expr[Ind]): Expr[Ind] =
    pattern.body.substitute(selfPlaceholder := fVar)

  def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    adt.height.predicateAt(typeSubstitutions)(hh)

  val heightFun: Expr[Ind] =
    specializeTerm(adt.height.function, typeSubstitutions)

  val heightFunValid: THM = adt.height.validAt(typeSubstitutions)

  val heightZero = adt.height.zeroAt(typeSubstitutions)
}
