package lisa.maths.SetTheory.Types.ADT.PatternMatching

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.interface.Constructor
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.appSeq

/**
 * A resolved constructor pattern with its specialized types and value binders.
 */
private[ADT] sealed trait PatternNode {

  /**
   * The set containing values matched by this node.
   */
  def typ: Expr[Ind]

  /**
   * The constructor expression represented by this node.
   */
  def term: Expr[Ind]

  /**
   * The value binders and their types, in occurrence order.
   */
  def typingSignature: Seq[(Variable[Ind], Expr[Ind])]

  /**
   * The value binders, in occurrence order.
   */
  final def binders: Seq[Variable[Ind]] = typingSignature.map(_._1)

  /**
   * Renames value binders while preserving rigid type arguments and binder types.
   */
  def renameBinders(renaming: Map[Variable[Ind], Variable[Ind]]): PatternNode
}

/**
 * The two forms of resolved patterns.
 */
private[ADT] object PatternNode {

  /**
   * A value binder with its expected type.
   */
  final case class Bind private[PatternMatching] (variable: Variable[Ind], typ: Expr[Ind]) extends PatternNode {

    /**
     * The expression bound at this position.
     */
    def term: Expr[Ind] = variable

    /**
     * This binder and its expected type.
     */
    def typingSignature: Seq[(Variable[Ind], Expr[Ind])] = Seq(variable -> typ)

    /**
     * Renames this value binder without substituting in its type.
     */
    def renameBinders(renaming: Map[Variable[Ind], Variable[Ind]]): Bind =
      copy(variable = renaming.getOrElse(variable, variable))
  }

  /**
   * A constructor application with its explicit type arguments and resolved children.
   */
  final case class Construct private[PatternMatching] (
      constructor: Constructor[?],
      typeArguments: Seq[Expr[Ind]],
      arguments: List[PatternNode]
  ) extends PatternNode {

    /**
     * The specialized datatype returned by the constructor.
     */
    lazy val typ: Expr[Ind] = constructor.adt.termAt(typeArguments)

    /**
     * The constructor applied to its type arguments and child expressions.
     */
    lazy val term: Expr[Ind] = appSeq(constructor.semantic.term(typeArguments))(arguments.map(_.term))

    /**
     * All child binders and their types, from left to right.
     */
    lazy val typingSignature: Seq[(Variable[Ind], Expr[Ind])] = arguments.flatMap(_.typingSignature)

    /**
     * Renames child value binders while preserving the constructor's type arguments.
     */
    def renameBinders(renaming: Map[Variable[Ind], Variable[Ind]]): Construct =
      copy(arguments = arguments.map(_.renameBinders(renaming)))
  }
}
