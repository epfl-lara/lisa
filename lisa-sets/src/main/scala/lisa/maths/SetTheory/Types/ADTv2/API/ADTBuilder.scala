package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._

/**
 * `S` is the sort of the declared symbol: `Ind` for a monomorphic ADT, and one arrow
 * per type variable, so `list` is an `ADT[Ind >>: Ind]`. Each `adt` overload below
 * writes its own sort down, and the sort evidence comes from LISA's own `Sort`
 * derivation rather than anything computed here.
 */
private def ADTBuilder[S](using Sort[S])(
    name: String,
    typeVars: Seq[String],
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[S] = {

  require(
    typeVars.distinct.size == typeVars.size,
    s"ADT $name has duplicate type variables: ${typeVars.mkString(", ")}."
  )

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
        case c: ConstructorArg => (argName, c)
    }
  }

  // Tags are the constructor's position in this declaration, so they stay small and
  // independent of what else has been declared elsewhere in the program.
  val constructorsSyntactic = constructorsArgs.zipWithIndex.map((args, index) =>
    SyntacticConstructor(
      args.map(arg => arg._2),
      args.map(arg => Variable[Ind](arg._1)),
      args.map(arg => Variable[Ind](s"${arg._1}2")),
      tag = index,
      owner = name
    )
  )

  val adtSyntactic = SyntacticADT(
    name,
    constructorsSyntactic,
    typeVars.map(Variable[Ind](_))
  )

  val constructorsSemantic = constructorsSyntactic.zip(constructorsName).map { case (ctor, name) =>
    SemanticConstructor(
      name,
      ctor,
      adtSyntactic
    )
  }

  new ADT[S](SemanticADT(adtSyntactic, constructorsSemantic))
}

def adt(
    name: String,
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[Ind] =
  ADTBuilder[Ind](name, Seq.empty, constructors)

def adt(
    name: String,
    typeVars: String,
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[Ind >>: Ind] =
  ADTBuilder[Ind >>: Ind](name, Seq(typeVars), constructors)

def adt(
    name: String,
    typeVars: (String, String),
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[Ind >>: Ind >>: Ind] =
  ADTBuilder[Ind >>: Ind >>: Ind](name, Seq(typeVars._1, typeVars._2), constructors)

def adt(
    name: String,
    typeVars: (String, String, String),
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[Ind >>: Ind >>: Ind >>: Ind] =
  ADTBuilder[Ind >>: Ind >>: Ind >>: Ind](name, Seq(typeVars._1, typeVars._2, typeVars._3), constructors)

def adt(
    name: String,
    typeVars: (String, String, String, String),
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[Ind >>: Ind >>: Ind >>: Ind >>: Ind] =
  ADTBuilder[Ind >>: Ind >>: Ind >>: Ind >>: Ind](name, Seq(typeVars._1, typeVars._2, typeVars._3, typeVars._4), constructors)

def adt(
    name: String,
    typeVars: (String, String, String, String, String),
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind] =
  ADTBuilder[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind](
    name,
    Seq(typeVars._1, typeVars._2, typeVars._3, typeVars._4, typeVars._5),
    constructors
  )
