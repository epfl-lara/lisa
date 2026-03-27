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
  val returnType: Expr[Ind] = semantic.returnType
  val term: Expr[Ind] = semantic.term

  infix def *(arg: Expr[Ind]): Expr[Ind] = term * arg
  def apply(arg: Expr[Ind]): Expr[Ind] = term * arg

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
