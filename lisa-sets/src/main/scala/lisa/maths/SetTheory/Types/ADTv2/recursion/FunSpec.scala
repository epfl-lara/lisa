package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.TypingHelpers.*

/**
 * Pure specification of a recursive ADT function.
 *
 * Stores the ADT, return type, and raw case bodies with [[selfPlaceholder]] free
 * (i.e. bodies are NOT yet substituted with any concrete function term).
 *
 * No proofs live here.  All proof obligations are discharged in the layers above.
 *
 * Layers that depend on this class:
 *   - [[Witness]]    (Layer 2)
 *   - [[Existence]]  (Layer 3)
 *   - [[RecFunSemantics]] (Layer 4)
 */
class FunSpec[N <: Arity](
    val functionName: String,
    val adt: SemanticADT[N],
    val selfPlaceholder: Variable[Ind],
    val rawCases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    val returnType: Expr[Ind]
) {
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity
  val argType: Expr[Ind] = adt.term
  val typ: Expr[Ind] = argType ->: returnType

  /**
   * Def(fVar) ≡ (fVar ∈ A→T) ∧ ∧_c ∀x̄. WT(c(x̄)) ⟹ fVar(c(x̄)) = body_c[fVar]
   *
   * The [[selfPlaceholder]] in raw case bodies is replaced by [[fVar]].
   */
  def untypedDefinition(fVar: Expr[Ind]): Expr[Prop] =
    (fVar :: typ) /\ simplify(seqAnd(rawCases.map((c, caseDef) =>
      val (vars, body) = caseDef
      val bodyWithSelf = body.substitute(selfPlaceholder := fVar)
      forallSeq(
        vars,
        wellTypedFormula(c.semanticSignature(vars)) ==> (fVar * c.appliedTerm(vars) === bodyWithSelf)
      )
    )))
}
