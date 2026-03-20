package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.KernelHelpers.lambda
import lisa.utils.KernelHelpers.lambda

private[encoding] trait SyntacticADTBase[N <: Arity] {
  this: SyntacticADT[N] =>

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] = lisa.maths
    .SetTheory.Functions.Predef.app(f)(x)

  protected def sourceLine: sourcecode.Line

  protected def sourceFile: sourcecode.File

  /**
   *  Formula describing whether the variables of a constructor belongs to their
   *  respective domain or s when they are self-referencing.
   */
  private[encoding] def constructorVarsInDomain(
      c: SyntacticConstructor,
      s: Expr[Ind]
  ): Expr[Prop] = wellTypedFormula(c.signature)(s)

  /** Formula describing whether an element x is an instance of a specific constructor. */
  private[encoding] def isConstructor(
      c: SyntacticConstructor,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables2, wellTypedFormula(c.signature2)(s) /\ (x === c.term2))

  /**
   *  Formula describing whether an element x is an instance of one of this ADT's
   *  constructors.
   */
  private[encoding] def isConstructor(x: Expr[Ind], s: Expr[Ind]): Expr[Prop] = 
    seqOr(constructors.map(c => isConstructor(c, x, s)))

  /** Predicate encoding the introduction function. */
  private[encoding] def isInIntroductionFunctionImage(s: Expr[Ind])(
      y: Expr[Ind]
  ): Expr[Prop] = isConstructor(y, s) \/ in(y, s)

  /** Predicate encoding the extended introduction function. */
  private[encoding] def isInExtendedIntroductionFunctionImage(f: Expr[Ind])(
      x: Expr[Ind]
  ): Expr[Prop] = !(f === ∅) /\ isInIntroductionFunctionImage(unionRange(f))(x)


  /** Logical predicate symbol for height-function characterization. */
  private[encoding] val isHeight = 
    DEF(using name=s"${name}IsHeightFunction")(λ(h, 
    functional(h) /\
    (relationDomain(h) === N) /\ forall(
      n,
      in(n, N) ==> forall(
        x,
        in(x, app(h, n)) <=>
          isInExtendedIntroductionFunctionImage(restrictedFunction(h, n))(x)
      )
    )
  ))

}
