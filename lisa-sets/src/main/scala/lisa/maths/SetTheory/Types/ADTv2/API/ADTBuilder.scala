package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.ADTv2.support.{**, Time, toSeq}

private def ADTBuilder[N <: Arity](
  name: String,
  typeVars: Seq[String],
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
)(using ValueOf[N]) = {
  val t0 = Time.get()

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

  val constructorsSyntactic = constructorsArgs.map(args =>
    SyntacticConstructor(
      args.map(arg => arg._2),
      args.map(arg => Variable[Ind](arg._1)),
      args.map(arg => Variable[Ind](s"${arg._1}2"))
    )
  )
  val t1 = Time.get()
  val adtSyntactic = SyntacticADT[N](
    name,
    constructorsSyntactic,
    **.fromSeq[Variable[Ind], N](typeVars.map(Variable[Ind](_)))
  )
  val t2 = Time.get()

  val constructorsSemantic = constructorsSyntactic.zip(constructorsName).map {
    case (ctor, name) =>
      SemanticConstructor[N](
        name,
        ctor,
        adtSyntactic
      )
  }
  val t3 = Time.get()
  val adtSemantic = SemanticADT[N](adtSyntactic, constructorsSemantic)
  val t4 = Time.get()

  val res = new ADT[N](adtSemantic)
  // val t5 = Time.get()
  // val consSyn = t1 - t0
  // val adtSyn = t2 - t1
  // val consSem = t3 - t2
  // val adtSem = t4 - t3
  // val buildADT = t5 - t4
  // println(s"Building ADT $name took ${t5 - t0} (consSyn: $consSyn, adtSyn: $adtSyn, consSem: $consSem, adtSem: $adtSem, buildADT: $buildADT)")
  res
}

def adt[N <: Arity](
  name: String,
  typeVars: String ** N,
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
)(using ValueOf[N]) : ADT[N] =
  ADTBuilder[N](name, typeVars.toSeq, constructors)

def adt(
  name: String,
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[0] =
  ADTBuilder[0](name, Seq.empty, constructors)

def adt(
  name: String,
  typeVars: Unit,
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[0] =
  ADTBuilder[0](name, Seq.empty, constructors)

def adt(
  name: String,
  typeVars: String,
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[1] =
  ADTBuilder[1](name, Seq(typeVars), constructors)

def adt(
  name: String,
  typeVars: (String, String),
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[2] =
  ADTBuilder[2](name, Seq(typeVars._1, typeVars._2), constructors)

def adt(
  name: String,
  typeVars: (String, String, String),
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[3] =
  ADTBuilder[3](name, Seq(typeVars._1, typeVars._2, typeVars._3), constructors)

def adt(
  name: String,
  typeVars: (String, String, String, String),
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[4] =
  ADTBuilder[4](name, Seq(typeVars._1, typeVars._2, typeVars._3, typeVars._4), constructors)

def adt(
  name: String,
  typeVars: (String, String, String, String, String),
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[5] =
  ADTBuilder[5](
    name,
    Seq(typeVars._1, typeVars._2, typeVars._3, typeVars._4, typeVars._5),
    constructors
  )

def adt(
  name: String,
  typeVars: Seq[String],
  constructors: Seq[
    (String, Seq[(String, String | ConstructorArg)])
  ]
): ADT[?] =
  val typeVarsSeq = typeVars.toSeq
  typeVarsSeq.size match
    case 0 => ADTBuilder[0](name, typeVarsSeq, constructors)
    case 1 => ADTBuilder[1](name, typeVarsSeq, constructors)
    case 2 => ADTBuilder[2](name, typeVarsSeq, constructors)
    case 3 => ADTBuilder[3](name, typeVarsSeq, constructors)
    case 4 => ADTBuilder[4](name, typeVarsSeq, constructors)
    case 5 => ADTBuilder[5](name, typeVarsSeq, constructors)
    case n =>
      throw new IllegalArgumentException(
        s"ADT $name has unsupported arity $n. Supported arities: 0 to 5."
      )
