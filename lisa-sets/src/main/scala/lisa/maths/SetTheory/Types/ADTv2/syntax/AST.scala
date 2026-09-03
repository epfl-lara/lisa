package lisa.maths.SetTheory.Types.ADTv2.syntax

/**
 * Core syntax for ADT v2. Kept backend-agnostic on purpose.
 */
object AST {

  sealed trait TypeExpr

  /**
   * Simple type reference, e.g. "A" or "nat".
   */
  final case class TypeRef(name: String) extends TypeExpr {
    override def toString: String = name
  }

  /**
   * Type application, e.g. "List[A]".
   */
  final case class TypeApply(name: String, args: Seq[TypeExpr]) extends TypeExpr {
    override def toString: String = s"$name[${args.mkString(", ")}]"
  }

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

  final case class ConstructorSpec(name: String, args: Seq[ConstructorArg]) {
    override def toString: String =
      if (args.isEmpty) name else s"$name(${args.mkString(", ")})"

    def arity(): Int = args.size

  }

  final case class ADTSpec(
      name: String,
      typeParameters: Seq[String],
      constructors: Seq[ConstructorSpec]
  ) {
    override def toString: String = {
      val params =
        if (typeParameters.isEmpty) "" else s"[${typeParameters.mkString(", ")}]"
      val ctors = constructors.mkString(" | ")
      s"$name$params = $ctors"
    }
  }

  final case class FunctionCaseSpec(
      constructorName: String,
      binders: Seq[String],
      bodyRepr: String
  )

  final case class FunctionSpec(
      name: String,
      adtName: String,
      returnType: TypeExpr,
      cases: Seq[FunctionCaseSpec]
  )
}
