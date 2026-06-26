package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.height.HeightADT
import lisa.maths.SetTheory.Types.ADTv2.height.HeightConstructorData
import lisa.maths.SetTheory.Types.ADTv2.height.HeightConstructors
import lisa.maths.SetTheory.Types.ADTv2.height.HeightStageSet
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.UniqueDefinedSymbol
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTBase[N <: Arity] {
  this: SyntacticADT[N] =>

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] = lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  protected def sourceLine: sourcecode.Line
  protected def sourceFile: sourcecode.File

  def constructorVarsInDomain(
      c: SyntacticConstructor,
      s: Expr[Ind]
  ): Expr[Prop] = wellTypedFormula(c.signature)(s)

  def isConstructor(
      c: SyntacticConstructor,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables2, wellTypedFormula(c.signature2)(s) /\ (x === c.term2))

  def isConstructor(x: Expr[Ind], s: Expr[Ind]): Expr[Prop] =
    seqOr(constructors.map(c => isConstructor(c, x, s)))

  val isConstructor: Expr[Ind >>: Ind >>: Prop] = λ(x, λ(s, isConstructor(x, s)))

  def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    isConstructor(y, s) \/ in(y, s)

  protected val heightConstructorData = constructors.map(c =>
    HeightConstructorData(
      variables = c.variables2,
      signature = c.signature2,
      subterm = c.subterm2,
      tagTerm = c.tagTerm
    )
  )

  protected val heightTHY = 
    HeightADT[N](name, typeVariablesSeq, isConstructor)
  private val heightStageSet = 
    HeightStageSet[N](heightTHY, heightConstructorData, isConstructor)
  protected val heightConstructorsTHY = 
    HeightConstructors[N](heightTHY, heightConstructorData, heightStageSet, isConstructor)


  def isHeight(h: Expr[Ind]): Expr[Prop] = heightTHY.isHeight(h)
  val heightExists = heightStageSet.heightExists
  val heightUniqueness = heightConstructorsTHY.heightUniqueness
  val heightExistsOne = heightConstructorsTHY.heightExistsOne
  val heightZero = heightTHY.heightZero
  val heightMonotonic = heightConstructorsTHY.heightMonotonic
  val heightMembershipMonotonic = heightConstructorsTHY.heightMembershipMonotonic
  val heightSuccessorInclusion = heightConstructorsTHY.heightSuccessorInclusion
  val heightSuccessorWeak = heightConstructorsTHY.heightSuccessorWeak
  val heightSuccessorStrong = heightConstructorsTHY.heightSuccessorStrong

  private val heightVar = variable[Ind](s"${name}/height")
  private val definedClassFunction = UniqueDefinedSymbol(
    name = s"${name}/heightFun",
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = heightVar,
    definitionAt = isHeight
  )(heightExistsOne)

  def heightAt(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)
  val height: Expr[Ind] = definedClassFunction.term
  val heightValid = definedClassFunction.definitionFact

}
