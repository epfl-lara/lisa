package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*


def adt(name: String, typeParameters: Seq[String], constructors: Seq[ConstructorSpec]): ADTSpec =
  ADTSpec(name, typeParameters, constructors)

def constructor(name: String, args: (String | TypeExpr | ConstructorArg)*): ConstructorSpec =
  ConstructorSpec(name, args.map(constrArg(_)))

def constrArg(e : String | TypeExpr | ConstructorArg): ConstructorArg = e match
  case s: String => RegularArg(TypeRef(s))
  case t: TypeExpr => RegularArg(t)
  case c: ConstructorArg => c
