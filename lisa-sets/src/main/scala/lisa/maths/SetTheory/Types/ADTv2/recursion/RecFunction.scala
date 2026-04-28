package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Thin public wrapper over the layered recursion proof architecture.
 *
 * Provides the same external API as the old monolithic class while
 * delegating all proof work to:
 *
 *   [[FunSpec]]        — specification (no proofs)
 *   [[Witness]]     — witness construction                (Layer 2)
 *   [[Existence]]   — ∃f, Def(f) without circularity      (Layer 3)
 *   [[Uniqueness]]  — ∃!f, Def(f) + term + case equations (Layer 4)
 *
 * This class itself contains no proofs: it only wires the layers together
 * and re-exports the public members needed by [[RecFunction]] and by
 * [[API.FunctionBuilder.recFun2]].
 */
class RecFunction[N <: Arity](
    val name: String,
    adt: ADT[N],
    selfPlaceholder: Variable[Ind],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    val returnType: Expr[Ind]
)(using line: sourcecode.Line, file: sourcecode.File) {


  // ── Layer 1: spec ─────────────────────────────────────────────────────────

  private val spec = FunSpec[N](
    functionName = name,
    adt = adt.semantic,
    selfPlaceholder = selfPlaceholder,
    rawCases = cases,
    returnType = returnType
  )

  // ── Layer 2: witness ──────────────────────────────────────────────────────

  private val witness: Witness[N] = new Witness[N](spec)

  // ── Layer 3: existence ────────────────────────────────────────────────────

  private val approx     = new Approx[N](spec, witness)
  private val approxProp = new ApproxProp[N](spec, witness, approx)
  private val existence  = new Existence[N](spec, witness, approx, approxProp)

  // ── Layer 4: uniqueness + class term ──────────────────────────────────────

  private val uniqueness = new Uniqueness[N](spec, existence)

  // ── Public fields re-exported from FunSpec ────────────────────────────────

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = spec.typeVariablesSeq
  val typeArity: N = spec.typeArity
  var argType: Expr[Ind] = spec.argType
  val typ: Expr[Ind] = spec.typ

  // ── Public fields re-exported from Uniqueness ──────────────────────────

  val id: Identifier = uniqueness.id

  /** The class-level function term (= ε(f, Def(f))). */
  val term: Expr[Ind] = uniqueness.term

  /** Case bodies with selfPlaceholder substituted by [[term]]. */
  val caseDefinitions: Map[Constructor[N], (Seq[Variable[Ind]], Expr[Ind])] =
    adt.constructors.map(c => c -> uniqueness.caseDefinitions(c.semantic)).toMap

  /** One case equation per constructor: WT(c(x̄)) ⊢ term(c(x̄)) = body_c[term]. */
  val shortDefinition: Map[SemanticConstructor[N], THM] = uniqueness.shortDefinition

  /** Typing introduction: term :: A→T. */
  // val intro: THM = uniqueness.intro

  // ── ????  ────────────────────────────────────────────────────────────────

  infix def *(arg: Expr[Ind]): Expr[Ind] = term * arg
  override def toString: String = 
    s"$name[${typeVariablesSeq.mkString(", ")}]: $argType -> $returnType"

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

  val introduction: THM = THM(
    uniqueness.intro.statement,
    s"${name}/introduction",
    line.value,
    file.value,
    Theorem
  )(have(uniqueness.intro))

  val elimination: Map[Constructor[N], THM] = adt.constructors.map(c =>
    (
      c,
      THM(
        uniqueness.shortDefinition(c.semantic).statement,
        s"${name}/elimination: ${c.name} case",
        line.value,
        file.value,
        Theorem
      )(have(uniqueness.shortDefinition(c.semantic)))
    )
  ).toMap


  val intro = introduction
  val elim = elimination


  // ── Debug helpers (retained for test / exploration code) ─────────────────

  val debug_uniqueness: THM = uniqueness.uniqueness
  val debug_existence: Existence[N] = existence
  val debug_classDefinitionFact: THM = uniqueness.classDefinitionFact
}

object RecFunction {
  def selfReferenceName(functionName: String): String = s"${functionName}RecSelf"

  def selfPlaceholder(functionName: String): Variable[Ind] =
    Variable[Ind](selfReferenceName(functionName))
}