package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Minimal type-level wrapper for recursive ADT functions without generated lemmas.
 */
class RecFunction[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
    private val semantic: SemanticRecFunction[N],
    private val adt: ADT[N]
) {

  val name: String = semantic.fullName
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
  val argType: Expr[Ind] = semantic.argType
  val returnType: Expr[Ind] = semantic.returnType
  val term: Expr[Ind] = semantic.term

  /** Sequence view of type variables used for specialization helpers. */
  private val typeVariablesSeq: Seq[Variable[Ind]] = typeVariables.toSeq

  infix def *(arg: Expr[Ind]): Expr[Ind] = term * arg
  def at(arg: Expr[Ind]): Expr[Ind] = term * arg

  /**
   *  Instantiate the polymorphic type parameters of this recursive function.
   *
   *  Empty arguments keep schematic type variables.
   */
  def apply(args: Expr[Ind]*): Expr[Ind] = {
    require(
      args.size == typeVariablesSeq.size || args.isEmpty,
      s"Function $name expects ${typeVariablesSeq.size} type argument(s), got ${args.size}."
    )
    if args.isEmpty then term
    else {
      val substitutions = typeVariablesSeq.zip(args).map((v, a) => v := a)
      term.substitute(substitutions*)
    }
  }

  /** Backward-compatible alias for polymorphic specialization. */
  def of(args: Expr[Ind]*): Expr[Ind] = apply(args*)

  override def toString: String = s"$name[${typeVariablesSeq.mkString(", ")}]: $argType -> $returnType"

  val intro: THM = THM(
    semantic.intro.statement,
    s"${name}/introduction",
    line.value,
    file.value,
    Theorem
  )(have(semantic.intro))

  val elim: Map[Constructor[N], THM] = adt.constructors.map(c =>
    (
      c,
      THM(
        semantic.shortDefinition(c.semantic).statement,
        s"${name}/elimination: ${c.name} case",
        line.value,
        file.value,
        Theorem
      )(have(semantic.shortDefinition(c.semantic)))
    )
  ).toMap

  val shortDefinition: Map[Constructor[N], THM] = elim

  val caseDefinitions: Map[Constructor[N], (Seq[Variable[Ind]], Expr[Ind])] =
    adt.constructors.map(c => c -> semantic.caseDefinitions(c.semantic)).toMap
}

object RecFunction {
  def selfReferenceName(functionName: String): String = s"${functionName}RecSelf"

  def selfPlaceholder(functionName: String): Variable[Ind] =
    Variable[Ind](selfReferenceName(functionName))
}
