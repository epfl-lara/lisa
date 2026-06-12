package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.height.HeightADT
import lisa.maths.SetTheory.Types.ADTv2.height.HeightConstructorData
import lisa.maths.SetTheory.Types.ADTv2.height.HeightConstructors
import lisa.maths.SetTheory.Types.ADTv2.height.HeightStageConstructorData
import lisa.maths.SetTheory.Types.ADTv2.height.HeightStageSet
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTHeight[N <: Arity]
    extends SyntacticADTInjectivity[N] {
  this: SyntacticADT[N] =>

  protected val heightConstructorData = constructors.map(c =>
    HeightConstructorData(
      variables = c.variables2,
      signature = c.signature2,
      term = c.term2
    )
  )

  protected val heightStageConstructorData = constructors.map(c =>
    HeightStageConstructorData(
      variables = c.variables2,
      signature = c.signature2,
      subterm = c.subterm2,
      tagTerm = c.tagTerm
    )
  )

  protected val heightTHY = Time.measure("ADT HeightADT")(HeightADT[N](
    name,
    typeVariablesSeq,
    isConstructor
  ))

  protected val heightStageSet = Time.measure("ADT HeightStageSet")(HeightStageSet[N](
    heightTHY, 
    heightStageConstructorData, 
    isConstructor
  ))

  protected val heightConstructorsTHY = Time.measure("ADT HeightConstructors")(HeightConstructors[N](
    heightTHY,
    heightConstructorData,
    heightStageSet,
    isConstructor
  ))

  def isHeight(h: Expr[Ind]): Expr[Prop] = heightTHY.isHeight(h)
  val heightExists = heightConstructorsTHY.heightExists
  val heightUniqueness = heightConstructorsTHY.heightUniqueness
  val heightExistsOne = heightConstructorsTHY.heightExistsOne

  private val heightVar = variable[Ind](s"${name}/height") 
  private val definedClassFunction = UniqueDefinedSymbol(
    name = s"${name}/heightFun",
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = heightVar,
    definitionAt = isHeight
  )(heightExistsOne)

  def polymorphicHeight(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)
  def heightAt(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)
  val height: Expr[Ind] = definedClassFunction.term
  val heightValid = definedClassFunction.definitionFact
  val heightZero = heightTHY.heightZero
  val heightMonotonic = heightConstructorsTHY.heightMonotonic
  val heightMembershipMonotonic = heightConstructorsTHY.heightMembershipMonotonic
  val heightSuccessorInclusion = heightConstructorsTHY.heightSuccessorInclusion
  val heightSuccessorWeak = heightConstructorsTHY.heightSuccessorWeak
  val heightSuccessorStrong = heightConstructorsTHY.heightSuccessorStrong
}
