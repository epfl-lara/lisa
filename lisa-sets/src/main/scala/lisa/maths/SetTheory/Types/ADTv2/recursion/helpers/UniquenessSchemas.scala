package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

type PatternSchemas[N <: Arity] =
  Map[Pattern[N], (Seq[Variable[Ind]], Expr[Prop])]

def asIndEquality(formula: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = formula match
  case App(App(eqFun, lhs: Expr[Ind]), rhs: Expr[Ind]) if eqFun == equality => Some((lhs, rhs))
  case _ => None

def splitConjunctions(formula: Expr[Prop]): Seq[Expr[Prop]] = formula match
  case left /\ right => splitConjunctions(left) ++ splitConjunctions(right)
  case other => Seq(other)

def stripForalls(formula: Expr[Prop]): (Seq[Variable[Ind]], Expr[Prop]) = formula match
  case forall(v, phi) =>
    val (restVars, core) = stripForalls(phi)
    (v +: restVars, core)
  case other => (Seq.empty, other)

def splitImplication(formula: Expr[Prop]): (Expr[Prop], Expr[Prop]) = formula match
  case antecedent ==> consequent =>
    (
      simplify(antecedent.asInstanceOf[Expr[Prop]]),
      consequent.asInstanceOf[Expr[Prop]]
    )
  case other => (⊤, other)

def extractPatternCaseSchema[N <: Arity](
    definition: Expr[Prop],
    functionHead: Expr[Ind],
    pattern: Pattern[N]
): (Seq[Variable[Ind]], Expr[Prop]) = {
  val maybeSchema = splitConjunctions(definition).iterator.flatMap(candidate =>
    val (vars, core) = stripForalls(candidate)
    val (antecedent, conclusion) = splitImplication(core)
    val maybeEquality = asIndEquality(conclusion)

    maybeEquality.flatMap((lhs, rhs) =>
      val expectedApplication = functionHead * pattern.inputTermAt(vars)
      val expectedPremise = simplify(pattern.branchPremiseAt(vars))
      if (lhs == expectedApplication || rhs == expectedApplication) && antecedent == expectedPremise then
        Some(vars -> candidate)
      else None
    )
  ).toSeq.headOption

  maybeSchema.getOrElse(
    throw IllegalArgumentException(
      s"Unable to extract pattern case schema for pattern ${pattern.name} and function ${functionHead}."
    )
  )
}
