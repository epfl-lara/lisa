package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._

private[ADTv2] abstract class FunSpecBase(
    val functionName: String,
    val typeVariablesSeq: Seq[Variable[Ind]],
    val adt: SemanticADT,
    val argType: Expr[Ind],
    val patternMatching: PatternSystem,
    val returnType: Expr[Ind]
) {
  val cases: Seq[Pattern] = patternMatching.patterns
  val typ: Expr[Ind] = argType ->: returnType

  protected def bodyFor(pattern: Pattern, fVar: Expr[Ind]): Expr[Ind]

  /**
   * Placeholder variable the defining predicate is stated about. The canonical
   * [[definitionFormula]] is a closed formula over this variable; concrete
   * candidates are obtained by substituting it (see [[definitionAt]]).
   */
  val placeholder: Variable[Ind]

  /** Checks parameter scope before constructing any function definitions or proofs. */
  protected def validateParameters(): Unit = {
    require(typeVariablesSeq.distinct.size == typeVariablesSeq.size, s"Function $functionName has duplicate parameters.")
    val parameters = typeVariablesSeq.toSet
    cases.foreach { pattern =>
      val shadowed = pattern.binders.filter(v => parameters.contains(v) || v == placeholder)
      require(shadowed.isEmpty, s"Function $functionName: pattern ${pattern.name} shadows a parameter or recursive self-reference: ${shadowed.mkString(", ")}.")
    }
    val branchVariables = cases.flatMap { pattern =>
      (pattern.typingFormula.freeVars ++ pattern.branchCondition.freeVars ++ pattern.inputTerm.freeVars ++ pattern.body.freeVars) -- pattern.binders
    }
    val undeclared = (typ.freeVars ++ branchVariables) -- parameters - placeholder
    require(undeclared.isEmpty, s"Function $functionName has undeclared free variables: ${undeclared.toSeq.map(_.toString).sorted.mkString(", ")}.")
  }

  def typeConstraint(fVar: Expr[Ind]): Expr[Prop] =
    fVar :: typ

  // TODO ??? : move this to be a Pattern method (be careful with bodyFor ownership)
  def patternConstraint(pattern: Pattern, fVar: Expr[Ind]): Expr[Prop] =
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
