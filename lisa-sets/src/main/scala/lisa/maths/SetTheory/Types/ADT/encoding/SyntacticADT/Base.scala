package lisa.maths.SetTheory.Types.ADT.encoding

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.height.HeightADT
import lisa.maths.SetTheory.Types.ADT.height.HeightConstructorData
import lisa.maths.SetTheory.Types.ADT.height.HeightConstructors
import lisa.maths.SetTheory.Types.ADT.height.HeightStageSet
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.semantics.DefinedSymbol

private[encoding] trait SyntacticADTBase {
  this: SyntacticADT =>

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] = lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  protected def sourceLine: sourcecode.Line
  protected def sourceFile: sourcecode.File

  private val predicateSubject = Variable[Ind](freshId(typeVariablesSeq ++ constructors.flatMap(_.variables2), "constructorSubject"))
  private val predicateDomain = Variable[Ind](freshId(typeVariablesSeq ++ constructors.flatMap(_.variables2) :+ predicateSubject, "constructorDomain"))
  private val constructorPredicates = constructors.map(c => c -> existsSeq(c.variables2, wellTypedFormula(c.signature2)(predicateDomain) /\ (predicateSubject === c.term2))).toMap

  def constructorVarsInDomain(
      c: SyntacticConstructor,
      s: Expr[Ind]
  ): Expr[Prop] = wellTypedFormula(c.signature)(s)

  /**
   * Describes a constructor instance without capturing the supplied subject or domain.
   */
  def isConstructor(
      c: SyntacticConstructor,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    constructorPredicates(c).substitute(predicateSubject := x, predicateDomain := s)

  def isConstructor(x: Expr[Ind], s: Expr[Ind]): Expr[Prop] =
    seqOr(constructors.map(c => isConstructor(c, x, s)))

  val isConstructor: Expr[Ind >>: Ind >>: Prop] = λ(predicateSubject, λ(predicateDomain, isConstructor(predicateSubject, predicateDomain)))

  def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    isConstructor(y, s) \/ (y ∈ s)

  protected val heightConstructorData = constructors.map(c =>
    HeightConstructorData(
      variables = c.variables2,
      signature = c.signature2,
      subterm = c.subterm2,
      tagTerm = c.tagTerm
    )
  )

  protected val heightTHY =
    HeightADT(name, typeVariablesSeq, isConstructor)
  private val heightStageSet =
    HeightStageSet(name, typeVariablesSeq, heightTHY, heightConstructorData, isConstructor)
  protected val heightConstructorsTHY =
    HeightConstructors(heightTHY, heightConstructorData, heightStageSet, isConstructor)

  def isHeight(h: Expr[Ind]): Expr[Prop] = heightTHY.isHeight(h)
  val heightExists = heightStageSet.heightExists
  val heightUniqueness = heightConstructorsTHY.heightUniqueness
  lazy val heightExistsOne = heightConstructorsTHY.heightExistsOne
  val heightZero = heightTHY.heightZero
  val heightMonotonic = heightConstructorsTHY.heightMonotonic
  val heightMembershipMonotonic = heightConstructorsTHY.heightMembershipMonotonic
  val heightSuccessorInclusion = heightConstructorsTHY.heightSuccessorInclusion
  val heightSuccessorWeak = heightConstructorsTHY.heightSuccessorWeak
  val heightSuccessorStrong = heightConstructorsTHY.heightSuccessorStrong

  private val definedClassFunction = new DefinedSymbol(
    name = s"${name}/heightFun",
    parametersSeq = typeVariablesSeq,
    body = heightStageSet.height
  )

  def heightAt(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)
  val height: Expr[Ind] = definedClassFunction.term
  val heightValid = Lemma.generated(isHeight(height)) {
    have(thesis) by Congruence.from(heightStageSet.heightValid, definedClassFunction.definition)
  }

}
