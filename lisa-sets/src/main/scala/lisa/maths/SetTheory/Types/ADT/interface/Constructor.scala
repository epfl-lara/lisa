package lisa.maths.SetTheory.Types.ADT.interface

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.generalTheorem
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.introAppTheorem
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.wellTypedSet
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.FunctionalClass
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional

final class Constructor[S](using val line: sourcecode.Line, val file: sourcecode.File, sort: Sort[S])(
    val semantic: SemanticConstructor,
    val adt: ADT[S]
) extends TypedConstantFunctional[S](
      semantic.id,
      FunctionalClass(
        List.fill(semantic.typeVariablesSeq.size)(None),
        semantic.typeVariablesSeq.toList,
        semantic.typ
      ),
      Constructor.typingJustification(semantic)
    ) {

  printAs(args => renderAppliedSymbol(semantic.fullName, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.fullName
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val term: Expr[Ind] = termAt(typeVariablesSeq)

  /**
   * Typing of the fully applied constructor, closed over the ADT's type variables.
   * Instantiate at type arguments with `of`, e.g. `cons.intro of nat`.
   *
   * This is the very theorem handed to [[TypedConstantFunctional]] as the symbol's
   * typing justification, reused rather than proved a second time. `Typecheck` relies
   * on that justification being universally closed, so the two must not drift apart.
   */
  lazy val intro: THM = justif.asInstanceOf[THM]

  /**
   * The curried form of [[intro]]. A genuinely derived statement, so it is proved once
   * over the type variables rather than closed over them; instantiate with
   * `of (A := nat)`.
   */
  lazy val introApp: THM = introAppTheorem(
    displayName = name,
    baseTheorem = semantic.intro,
    headTerm = termAt(typeVariablesSeq),
    headType = semantic.typ,
    assumptions = wellTypedSet(semantic.semanticSignature),
    typingArgs = semantic.semanticSignature,
    conclusion = semantic.appliedTerm :: adt.term
  )

  /**
   * Two instances of this constructor are equal exactly when their arguments are.
   * Instantiate with `of`.
   */
  lazy val injectivity: THM =
    generalTheorem(name, typeVariablesSeq, "injectivity", semantic.injectivity)

  /**
   * Applies exactly the declared type arguments and returns the set-theoretic constructor.
   */
  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] =
    require(args.size == typeVariablesSeq.size, s"Constructor $name expects ${typeVariablesSeq.size} type argument(s), got ${args.size}.")
    (this #@@ args).asInstanceOf[Expr[Ind]]

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)

  def specialize(args: Expr[Ind]*): SpecializedConstructor[S] =
    new SpecializedConstructor[S](this, args)
}

object Constructor {
  private def typingJustification(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(semantic: SemanticConstructor): THM =
    generalTheorem(semantic.fullName, semantic.typeVariablesSeq, "introduction", semantic.intro)
}
