package lisa.maths.SetTheory.Types.ADTv2.library

import lisa.maths.SetTheory.Types.ADTv2._
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

private val maxGeneratedTypeArity = 5

private def requireSupportedTypeArity(typeArity: Int): Unit =
  require(
    0 <= typeArity && typeArity <= maxGeneratedTypeArity,
    s"Generated debug ADTs only support type arities 0 to $maxGeneratedTypeArity, got $typeArity."
  )

private def typeVarName(index: Int): String =
  ('A'.toInt + index).toChar.toString

/**
 * Generates type variable names `A`, `B`, ... up to the current supported ADT arity.
 */
def genTypeVars(typeArity: Int): Seq[String] =
  requireSupportedTypeArity(typeArity)
  (0 until typeArity).map(typeVarName)

/**
 * Generates constructor arguments `x1: param`, ..., `xn: param`.
 */
def genConstructorArgs(argCount: Int, param: String): Seq[(String, String)] =
  require(argCount >= 0, s"Constructor arity must be non-negative, got $argCount.")
  (1 to argCount).map(index => s"x$index" -> param)

/**
 * Generates `constructorCount` constructors, each with `argCount` arguments of type `param`.
 */
def genConstructors(
    constructorCount: Int,
    argCount: Int,
    param: String,
    prefix: String = "cons"
): Seq[(String, Seq[(String, String)])] =
  require(constructorCount >= 0, s"Constructor count must be non-negative, got $constructorCount.")
  val args = genConstructorArgs(argCount, param)
  (1 to constructorCount).map(index => s"$prefix$index" -> args)

/**
 * Generates an ADT with several regular constructors and one optional recursive constructor.
 */
def genDebugADT(
    name: String,
    typeArity: Int,
    constructorCount: Int,
    argCount: Int,
    recursive: Boolean = false
): ADT[?] =
  val typeVars = genTypeVars(typeArity)
  val argType = typeVars.headOption.getOrElse(name)
  val regularConstructors = genConstructors(constructorCount, argCount, argType, s"${name}Cons")
  val constructors =
    if recursive then
      regularConstructors :+ (
        s"${name}Rec" ->
          (genConstructorArgs(argCount, argType) :+ ("tail" -> SelfRef))
      )
    else regularConstructors
  adt(name = name, typeVars = typeVars, constructors = constructors)

val nType = 2
val nConstructors = 10
val nArgs = 2

val debugTypeHeavy = genDebugADT(
  name = "debugTypeHeavy",
  typeArity = nType,
  constructorCount = 1,
  argCount = 1
)

val debugConstructorHeavy = genDebugADT(
  name = "debugConstructorHeavy",
  typeArity = 1,
  constructorCount = nConstructors,
  argCount = 1
)

val debugArgumentHeavy = genDebugADT(
  name = "debugArgumentHeavy",
  typeArity = 1,
  constructorCount = 1,
  argCount = nArgs
)

val debugRecursive = genDebugADT(
  name = "debugRecursive",
  typeArity = 1,
  constructorCount = 2,
  argCount = 3,
  recursive = true
)

object Debug:
  export lisa.maths.SetTheory.Types.ADTv2.library.{genTypeVars, genConstructorArgs, genConstructors, genDebugADT, debugTypeHeavy, debugConstructorHeavy, debugArgumentHeavy, debugRecursive}
