package lisa.maths.SetTheory.Types.ADT.recursion

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.encoding._
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.Thm

/**
 * The parameters, cases, and defining predicate of a function.
 */
final class FunSpec(
    val functionName: String,
    val typeVariablesSeq: Seq[Variable[Ind]],
    val adt: SemanticADT,
    val argType: Expr[Ind],
    val typeSubstitutions: Seq[TypeSubstitution],
    val selfPlaceholder: Variable[Ind],
    val patternMatching: PatternSystem[Expr[Ind]],
    val returnType: Expr[Ind]
) {
  val cases: Seq[Clause[Expr[Ind]]] = patternMatching.clauses
  val typ: Expr[Ind] = argType ->: returnType

  /**
   * Checks parameter scope before constructing any function definitions or proofs.
   */
  private def validateParameters(): Unit = {
    require(typeVariablesSeq.distinct.size == typeVariablesSeq.size, s"Function $functionName has duplicate parameters.")
    val parameters = typeVariablesSeq.toSet
    cases.foreach { pattern =>
      val shadowed = pattern.binders.filter(v => parameters.contains(v) || v == selfPlaceholder)
      require(shadowed.isEmpty, s"Function $functionName: pattern ${pattern.name} shadows a parameter or recursive self-reference: ${shadowed.mkString(", ")}.")
    }
    val branchVariables = cases.flatMap { pattern =>
      (pattern.typingFormula.freeVars ++ pattern.branchCondition.freeVars ++ pattern.inputTerm.freeVars ++ pattern.body.freeVars) -- pattern.binders
    }
    val undeclared = (typ.freeVars ++ branchVariables) -- parameters - selfPlaceholder
    require(undeclared.isEmpty, s"Function $functionName has undeclared free variables: ${undeclared.toSeq.map(_.toString).sorted.mkString(", ")}.")
  }

  validateParameters()

  private val proofVariables = collection.mutable.Map.empty[String, Variable[Ind]]
  private val proofContext: Seq[Expr[?]] = typeVariablesSeq ++ Seq(typ, selfPlaceholder) ++
    adt.constructors.flatMap(constructor => constructor.variables1 ++ constructor.variables2) ++ cases.flatMap { pattern =>
      pattern.binders ++ pattern.variables1 ++ pattern.variables2 ++
        Seq(pattern.typingFormula, pattern.branchCondition, pattern.inputTerm, pattern.body)
    }

  /**
   * Shares proof variables fresh against the declaration and the other generated variables.
   */
  private[recursion] def proofVariable(name: String): Variable[Ind] =
    proofVariables.getOrElseUpdate(name, Variable[Ind](freshId(proofContext ++ proofVariables.values, name)))

  def typeConstraint(fVar: Expr[Ind]): Expr[Prop] =
    fVar :: typ

  def patternConstraint(pattern: Clause[Expr[Ind]], fVar: Expr[Ind]): Expr[Prop] =
    forallSeq(
      pattern.binders,
      pattern.branchPremise ==> (selfPlaceholder * pattern.inputTerm === pattern.body)
    ).substitute(selfPlaceholder := fVar)

  def equationConstraint(fVar: Expr[Ind]): Expr[Prop] =
    simplify(seqAnd(cases.map(pattern => patternConstraint(pattern, fVar))))

  /**
   * The defining predicate, stated about the recursive self-reference.
   */
  lazy val definitionFormula: Expr[Prop] =
    typeConstraint(selfPlaceholder) /\ equationConstraint(selfPlaceholder)

  /**
   * The defining predicate specialized to the candidate `fVar`.
   */
  def definitionAt(fVar: Expr[Ind]): Expr[Prop] =
    definitionFormula.substitute(selfPlaceholder := fVar)

  /**
   * The height predicate specialized to this function's domain.
   */
  def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    adt.height.predicateAt(typeSubstitutions)(hh)

  /**
   * The domain's specialized height function.
   */
  val heightFun: Expr[Ind] = specializeTerm(adt.height.function, typeSubstitutions)

  /**
   * Validity of the domain's specialized height function.
   */
  def heightFunValid(using proof: lisa.SetTheoryLibrary.Proof): Thm = adt.height.validAt(typeSubstitutions)

  /**
   * The height function starts with the empty stage.
   */
  def heightZero(point: Expr[Ind])(using proof: lisa.SetTheoryLibrary.Proof): Thm =
    adt.height.zeroAt(typeSubstitutions, Seq(h := heightFun, x := point))
}
