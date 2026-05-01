package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

def defineAST[N <: Arity](
  name: String,
  typeVars: Seq[String],
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
) = {

  // TODO: verify that args name are not in the form x and x2 (reserved)
  // TODO: verify that their is no other reserved name (CF Variables.scala)
  def validateArgName(argName: String): Unit =
    val reserved_names = Set("n", "m", "h")
    require(
      !reserved_names.contains(argName),
      s"Constructor argument name '$argName' is reserved; choose another name"
    )

  def resolveArgType(argType: String): ConstructorArg =
    if argType == name then SelfRef
    else if typeVars.contains(argType) then TypeArg(argType)
    else
      require(
        typeVars.contains(argType),
        s"Constructor argument type '$argType' must be one of ${typeVars.mkString(", ")} or '$name'"
      )
      TypeArg(argType)

  val constructorsName = constructors.map(_._1)
  val constructorsArgs = constructors.map { case (_, args) => 
    args.map { case (argName, argType) => 
      validateArgName(argName)
      argType match
        case s: String => (argName, resolveArgType(s))
        // case s: String => (argName, RegularArg(TypeRef(s)))
        // case t: TypeExpr => (argName, RegularArg(t))
        case c: ConstructorArg => (argName, c)
    }
  }

  val constructorsSyntactic = constructorsArgs.map ( args =>
    SyntacticConstructor(
      args.map(arg => arg._2),
      args.map(arg => Variable[Ind](arg._1)),
      args.map(arg => Variable[Ind](s"${arg._1}2"))
    )
  )
  val adtSyntactic = SyntacticADT[N](
    name, 
    constructorsSyntactic, 
    typeVars.map(Variable[Ind](_))
  )

  val constructorsSemantic = constructorsSyntactic.zip(constructorsName).map { 
    case (ctor, name) =>
      SemanticConstructor[N](
        name,
        ctor,
        adtSyntactic
      )
  }
  val adtSemantic = SemanticADT[N](adtSyntactic, constructorsSemantic)

  val constructorsFinal = constructorsSemantic.map(Constructor[N](_))

  new ADT[N](adtSemantic, constructorsFinal)
}