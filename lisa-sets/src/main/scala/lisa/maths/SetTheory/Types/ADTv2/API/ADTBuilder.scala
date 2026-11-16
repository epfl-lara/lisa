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
  require(name.trim.nonEmpty, "An ADT must have a nonempty name.")
  require(typeVars.forall(_.trim.nonEmpty), s"ADT $name has an empty type variable name.")
  require(
    typeVars.distinct.size == typeVars.size,
    s"ADT $name has duplicate type variables: ${typeVars.mkString(", ")}."
  )

  // TODO: verify that their is no other reserved name (CF Variables.scala)
  def validateArgName(argName: String): Unit =
    val reserved_names = Set("n", "m", "h")
    require(
      !reserved_names.contains(argName),
      s"Constructor argument name '$argName' is reserved; choose another name"
    )

  val constructorsName = constructors.map(_._1)
  require(constructorsName.forall(_.trim.nonEmpty), s"ADT $name has an empty constructor name.")
  require(constructorsName.distinct.size == constructorsName.size, s"ADT $name has duplicate constructor names.")
  val constructorsArgs = constructors.map { case (constructorName, args) =>
    val owner = s"Constructor $name/$constructorName"
    require(args.map(_._1).distinct.size == args.size, s"$owner has duplicate argument names.")
    args.map { case (argName, argType) =>
      require(argName.trim.nonEmpty, s"$owner has an empty argument name.")
      validateArgName(argName)
      val resolved = argType match
        case s: String => if s == name then SelfRef else TypeArg(s)
        case c: ConstructorArg => c
      resolved match
        case TypeArg(parameter) =>
          require(typeVars.contains(parameter), s"$owner argument '$argName' refers to undeclared type parameter '$parameter'.")
        case SelfRef => ()
      (argName, resolved)
    }
  }

  // Tags are the constructor's position in this declaration, so they stay small and
  // independent of what else has been declared elsewhere in the program.
  val typeVariables = typeVars.map(Variable[Ind](_))
  val constructorsSyntactic = constructorsArgs.zipWithIndex.map { (args, index) =>
    val variables = args.foldLeft(Vector.empty[Variable[Ind]]) { case (acc, (argName, _)) =>
      acc :+ Variable[Ind](freshId(typeVariables ++ acc, argName))
    }
    val variables2 = args.foldLeft(Vector.empty[Variable[Ind]]) { case (acc, (argName, _)) =>
      acc :+ Variable[Ind](freshId(typeVariables ++ variables ++ acc, s"${argName}2"))
    }
    SyntacticConstructor(
      args.map(arg => arg._2),
      variables,
      variables2,
      tag = index,
      owner = name
    )
  }

  val adtSyntactic = SyntacticADT(
    name,
    constructorsSyntactic,
    typeVariables
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
