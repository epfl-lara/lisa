package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

private[ADTv2] abstract class FunSpecBase[N <: Arity](
    val functionName: String,
    val adt: SemanticADT[N],
    val argType: Expr[Ind],
    val patternMatching: PatternSystem[N],
    val returnType: Expr[Ind]
) {
  val cases: Seq[Pattern[N]] = patternMatching.patterns
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typ: Expr[Ind] = argType ->: returnType
  val typeArity: N = adt.typeArity

  protected def bodyFor(pattern: Pattern[N], fVar: Expr[Ind]): Expr[Ind]

  /**
   * Placeholder variable the defining predicate is stated about. The canonical
   * [[definitionFormula]] is a closed formula over this variable; concrete
   * candidates are obtained by substituting it (see [[definitionAt]]).
   */
  val placeholder: Variable[Ind]

  def typeConstraint(fVar: Expr[Ind]): Expr[Prop] =
    fVar :: typ

  def patternConstraint(pattern: Pattern[N], fVar: Expr[Ind]): Expr[Prop] =
    forallSeq(
      pattern.binders,
      pattern.branchPremise ==> (fVar * pattern.inputTerm === bodyFor(pattern, fVar))
    )

  def equationConstraint(fVar: Expr[Ind]): Expr[Prop] =
    simplify(seqAnd(cases.map(pattern => patternConstraint(pattern, fVar))))

  /**
   * The defining predicate, stated about [[placeholder]]. A single canonical
   * formula value (lazy to avoid the subclass initialization-order trap), so the
   * proofs fold/unfold the *same* syntactic object rather than rebuilding it.
   */
  lazy val definitionFormula: Expr[Prop] =
    typeConstraint(placeholder) /\ equationConstraint(placeholder)

  /** The defining predicate specialized to the candidate `fVar`. */
  def definitionAt(fVar: Expr[Ind]): Expr[Prop] =
    definitionFormula.substitute(placeholder := fVar)
}