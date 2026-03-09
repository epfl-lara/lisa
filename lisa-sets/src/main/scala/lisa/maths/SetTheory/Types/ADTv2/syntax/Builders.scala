package lisa.maths.SetTheory.Types.ADTv2.syntax

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*

/** Small construction helpers for AST nodes. */
object Builders {

  def adt(name: String, typeParameters: Seq[String], constructors: Seq[ConstructorSpec]): ADTSpec =
    ADTSpec(name, typeParameters, constructors)

  def constructor(name: String, args: ConstructorArg*): ConstructorSpec =
    ConstructorSpec(name, args)

  def typ(name: String): TypeExpr = TypeRef(name)

  def self: ConstructorArg = SelfRef

  def arg(tpe: TypeExpr): ConstructorArg = RegularArg(tpe)
}
