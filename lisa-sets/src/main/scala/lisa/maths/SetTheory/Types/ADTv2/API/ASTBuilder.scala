package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

def defineAST[N <: Arity](
  name: String,
  typeVars: Seq[String],
  constructors: Seq[
    (String, Seq[(String, String | TypeExpr | ConstructorArg)])
  ]
) = {

  val constructorsName = constructors.map(_._1)
  val constructorsArgs = constructors.map { case (_, args) => 
    args.map { case (argName, argType) => 
      argType match
        case s: String => (argName, RegularArg(TypeRef(s)))
        case t: TypeExpr => (argName, RegularArg(t))
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