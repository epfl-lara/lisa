package lisa.maths.SetTheory.Types.ADTv2.syntax

/** Core syntax for ADT v2. Kept backend-agnostic on purpose. */
object AST {

  sealed trait TypeExpr
  final case class TypeRef(name: String) extends TypeExpr
  final case class TypeApply(name: String, args: Seq[TypeExpr]) extends TypeExpr

  sealed trait ConstructorArg
  final case class Ground(tpe: TypeExpr) extends ConstructorArg
  case object SelfRef extends ConstructorArg

  final case class ConstructorSpec(name: String, args: Seq[ConstructorArg])

  final case class ADTSpec(
      name: String,
      typeParameters: Seq[String],
      constructors: Seq[ConstructorSpec]
  )

  final case class FunctionCaseSpec(constructorName: String, binders: Seq[String], bodyRepr: String)

  final case class FunctionSpec(
      name: String,
      adtName: String,
      returnType: TypeExpr,
      cases: Seq[FunctionCaseSpec]
  )
}
