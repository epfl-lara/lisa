package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.{ConstructorSpec, ADTSpec, ConstructorArg}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

def defineAST[N <: Arity](
  name: String,
  typeVars: Seq[String],
  constructors: Seq[
    (String, Seq[(String, ConstructorArg)])
  ]
) = {

  // constructors = Seq(name, Seq((argName, argType)))

  val constructorsName = constructors.map(_._1)
  val constructorsSpec = constructors.map { case (ctorName, args) =>
    ConstructorSpec(ctorName, args.map(arg => arg._2))
  }
  val adtSpec = ADTSpec(name, typeVars, constructorsSpec)


  val constructorsSyntactic = constructors.map { case (ctorName, args) =>
    SyntacticConstructor(
      args.map(arg => arg._2),
      args.map(arg => Variable[Ind](arg._1)),
      args.map(arg => Variable[Ind](s"${arg._1}2"))
    )
  }
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