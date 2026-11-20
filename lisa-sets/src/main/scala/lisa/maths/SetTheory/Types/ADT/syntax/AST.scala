package lisa.maths.SetTheory.Types.ADT.syntax

/**
 * Core syntax for ADT v2. Kept backend-agnostic on purpose.
 */
object AST {

  sealed trait ConstructorArg

  /**
   * A regular argument with a type, e.g. "head: A" in cons:(A, self) .
   */
  // final case class RegularArg(tpe: TypeExpr) extends ConstructorArg {
  //   override def toString: String = tpe.toString
  // }
  final case class TypeArg(name: String) extends ConstructorArg {
    override def toString: String = name
  }

  /**
   * A recursive reference to the ADT being defined, e.g. "self" in cons:(A, self) .
   */
  case object SelfRef extends ConstructorArg {
    override def toString: String = "self"
  }

}
