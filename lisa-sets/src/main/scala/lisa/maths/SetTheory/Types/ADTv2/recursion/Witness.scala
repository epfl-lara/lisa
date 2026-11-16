package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.WitnessBase
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.InstantiateForallSeq

/**
 * Layer 2 — Witness construction.
 *
 * Defines the witness set
 *   W(g) = { p ∈ A×T | caseMembership_g(p) }
 * where `g` = [[spec.selfPlaceholder]] stands for the recursive self-reference.
 *
 * The case-defined witness proof core is shared with ordinary semantic functions
 * through [[CaseDefinedWitness]]. This class keeps only the recursion-specific shell:
 *   - the free self-reference [[spec.selfPlaceholder]]
 *   - the contextual typing premise `selfPlaceholder :: A→T`
 *   - branch return-type checks, without that premise for base constructors
 */
private[recursion] final class Witness(spec: FunSpec)
    extends WitnessBase(
      functionName = spec.functionName,
      adt = spec.adt,
      argType = spec.argType,
      patternMatching = spec.patternMatching,
      returnType = spec.returnType,
      typ = spec.typ,
      typeVariablesSeq = spec.typeVariablesSeq
    ) {

  private val selfPlaceholder: Variable[Ind] = spec.selfPlaceholder

  /**
   * typingPremise = selfPlaceholder :: A→T (the induction hypothesis on the self-reference).
   */
  val typingPremise: Expr[Prop] = selfPlaceholder :: spec.typ

  /**
   * Definitional equation for the witness: W(selfPlaceholder) = witnessBody.
   */
  val witnessDef: JUSTIFICATION = witnessDefCore

  def apply(g: Expr[Ind]): Expr[Ind] =
    witness.substitute(spec.selfPlaceholder := g)

  override protected def witnessParametersSeq: Seq[Variable[Ind]] =
    spec.typeVariablesSeq :+ selfPlaceholder

  override protected def contextPremises: Seq[Expr[Prop]] =
    Seq(typingPremise)

  private val basePatterns: Set[Pattern] = spec.adt.constructors
    .filter(_.selfRefVariables2.isEmpty)
    .flatMap(spec.patternMatching.patternsFor)
    .toSet

  protected val checkReturnType: Map[Pattern, JUSTIFICATION] =
    WitnessBase.returnTypeChecks(
      patterns = spec.cases,
      returnType = spec.returnType,
      bodyAt = _.body,
      extraPremisesAt = pattern => if basePatterns.contains(pattern) then Set.empty else Set(typingPremise)
    )

  /** An input provides a target inhabitant, by induction on the input ADT. */
  val targetInhabited: THM = {
    val point = Variable[Ind](freshId(Seq(spec.argType, spec.returnType), "input"))
    val value = Variable[Ind](freshId(Seq(spec.returnType), "inhabitant"))
    val inhabited = ∃(value, value :: spec.returnType)
    val predicate = λ(point, inhabited)

    Lemma(∀(point, point :: spec.argType ==> inhabited)) {
      val cases = spec.adt.constructors.map { constructor =>
        val inductiveCase = constructor.inductiveCase.substitute(spec.typeSubstitutions*).substitute(P := predicate)
        have(inductiveCase) subproof {
          if constructor.selfRefVariables2.nonEmpty then
            // Any recursive argument supplies the same constant induction hypothesis.
            have(thesis) by Tautology
          else
            val vars = constructor.variables2
            val input = constructor.appliedTerm2.substitute(spec.typeSubstitutions*)
            val typing = constructor.semanticSignature2.map((v, t) => v :: t.substitute(spec.typeSubstitutions*))
            val patterns = spec.patternMatching.patternsFor(constructor)
            val branches = patterns.map { pattern =>
              val guard = pattern.branchSelectionBody(input)
              val branch = have((typing.toSet + guard) |- inhabited) subproof {
                have(pattern.freshTypingFormula |- pattern.bodyAtFreshVars2 :: spec.returnType) by Restate.from(
                  checkReturnType(pattern).of(pattern.binders.zip(pattern.variables2).map((from, to) => from := to)*)
                )
                thenHave(pattern.freshTypingFormula |- inhabited) by RightExists
                thenHave(thesis) by Tautology
              }
              val (selection, selected) = pattern.variables2.drop(pattern.arity).foldRight((guard, branch)) {
                case (v, (condition, fact)) =>
                  val existential = ∃(v, condition)
                  val lifted = have((typing.toSet + existential) |- inhabited) by LeftExists(fact)
                  (existential, lifted)
              }
              have(typing.toSet |- selection ==> inhabited) by RightImplies.withParameters(selection, inhabited)(selected)
            }
            val alternatives = seqOr(patterns.map(_.branchSelectionDisjunct(input)))
            val selector = have((seqAnd(typing) /\ (input === input)) ==> alternatives) by
              InstantiateForallSeq(vars)(spec.patternMatching.branchSelectionFor(constructor, input))
            val combined = have(typing.toSet |- inhabited) by Tautology.from((selector +: branches)*)
            val abstracted = vars.zip(typing).foldRight(combined) { case ((v, assumption), fact) =>
              val implication = have((fact.statement -<? assumption).left |- assumption ==> fact.statement.right.head) by Restate.from(fact)
              have(implication.statement.left |- ∀(v, implication.statement.right.head)) by RightForall(implication)
            }
            have(thesis) by Restate.from(abstracted)
        }
      }
      have(thesis) by Tautology.from((cases :+ spec.adt.induction.of(spec.typeSubstitutions*).of(P := predicate))*)
    }
  }

  private val _ = witnessSemantics
}
