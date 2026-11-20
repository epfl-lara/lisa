package lisa.maths.SetTheory.Types.ADT.API

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.encoding._
import lisa.maths.SetTheory.Types.ADT.interface.ADT
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.typeExprToTerm
import lisa.maths.SetTheory.Types.ADT.syntax.AST._

/**
 * `S` is the sort of the declared symbol: `Ind` for a monomorphic ADT, and one arrow
 * per type variable, so `list` is an `ADT[Ind >>: Ind]`. Each `adt` overload below
 * writes its own sort down, and the sort evidence comes from LISA's own `Sort`
 * derivation rather than anything computed here.
 */
private[ADT] def ADTBuilder[S](using
    (S) is Sort
)(
    name: String,
    typeVars: Seq[String],
    constructors: Seq[
      (String, Seq[(String, String | ConstructorArg)])
    ]
): ADT[S] = {
  new ADT[S](buildSemanticADT(name, typeVars, constructors))
}

/**
 * Validates a declaration and builds its semantics before creating its public ADT instance.
 */
private[ADT] def buildSemanticADT(
    name: String,
    typeVars: Seq[String],
    constructors: Seq[(String, Seq[(String, String | ConstructorArg)])]
): SemanticADT = {
  require(name.trim.nonEmpty, "An ADT must have a nonempty name.")
  require(typeVars.forall(_.trim.nonEmpty), s"ADT $name has an empty type variable name.")
  require(
    typeVars.distinct.size == typeVars.size,
    s"ADT $name has duplicate type variables: ${typeVars.mkString(", ")}."
  )

  val declaredTypeNames = typeVars.toSet

  val constructorNames = constructors.map(_._1)
  require(constructorNames.forall(_.trim.nonEmpty), s"ADT $name has an empty constructor name.")
  require(constructorNames.distinct.size == constructorNames.size, s"ADT $name has duplicate constructor names.")
  val constructorArguments = constructors.map { case (constructorName, args) =>
    val owner = s"Constructor $name/$constructorName"
    require(args.map(_._1).distinct.size == args.size, s"$owner has duplicate argument names.")
    args.map { case (argName, argType) =>
      require(argName.trim.nonEmpty, s"$owner has an empty argument name.")
      val resolved = argType match
        case s: String => if s == name then SelfRef else TypeArg(s)
        case c: ConstructorArg => c
      resolved match
        case TypeArg(parameter) =>
          require(declaredTypeNames.contains(parameter), s"$owner argument '$argName' refers to undeclared type parameter '$parameter'.")
        case SelfRef => ()
      (argName, resolved)
    }
  }

  // Tags are the constructor's position in this declaration, so they stay small and
  // independent of what else has been declared elsewhere in the program.
  val typeVariables = typeVars.map(typeExprToTerm)
  val syntacticConstructors = constructorArguments.zipWithIndex.map { (args, index) =>
    val variables = args.foldLeft(Vector.empty[Variable[Ind]]) { case (acc, (argName, _)) =>
      val declared = typeExprToTerm(argName)
      val forbidden = typeVariables ++ acc
      acc :+ (if forbidden.contains(declared) then declared.freshRename(forbidden) else declared)
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

  val syntacticADT = SyntacticADT(
    name,
    syntacticConstructors,
    typeVariables
  )

  val semanticConstructors = syntacticConstructors.zip(constructorNames).map { case (constructor, constructorName) =>
    SemanticConstructor(
      constructorName,
      constructor,
      syntacticADT
    )
  }

  SemanticADT(syntacticADT, semanticConstructors)
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
