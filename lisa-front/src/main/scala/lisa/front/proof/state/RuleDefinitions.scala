package lisa.front.proof.state

import lisa.kernel.proof.SequentCalculus.{SCProofStep, SCSubproof}
import lisa.front.fol.FOL.*
import lisa.front.proof.unification.UnificationUtils

import scala.collection.View

trait RuleDefinitions extends ProofEnvironmentDefinitions with UnificationUtils {

  type ReconstructRule = PartialFunction[(lisa.kernel.proof.SequentCalculus.Sequent, UnificationContext), IndexedSeq[SCProofStep]]

  /**
   * The parameters to instantiate a rule into a tactic (see [[RuleTactic]]).
   * @param selectors the correspondence between patterns and values, can be partial 
   * @param functions a partial assignment of functions
   * @param predicates a partial assignment of predicates
   * @param connectors a partial assignment of connectors
   * @param variables a partial assignment of free variables
   */
  case class RuleParameters(
    selectors: Map[Int, SequentSelector] = Map.empty,
    functions: Seq[AssignedFunction] = Seq.empty,
    predicates: Seq[AssignedPredicate] = Seq.empty,
    connectors: Seq[AssignedConnector] = Seq.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  ) {
    def withIndices(i: Int)(left: Int*)(right: Int*): RuleParameters = {
      val pair = (left.toIndexedSeq, right.toIndexedSeq)
      copy(selectors = selectors + (i -> pair))
    }

    def withFunction[N <: Arity](
      label: SchematicTermLabel[N], f: FillArgs[SchematicTermLabel[0], N] => Term
    )(using ValueOf[N]): RuleParameters =
      copy(functions = functions :+ AssignedFunction(label, LambdaFunction[N](f)))
    def withFunction(label: SchematicTermLabel[0], value: Term): RuleParameters =
      withFunction(label, _ => value)

    def withPredicate[N <: Arity](
      label: SchematicPredicateLabel[N], f: FillArgs[SchematicTermLabel[0], N] => Formula
    )(using ValueOf[N]): RuleParameters = copy(predicates = predicates :+ AssignedPredicate(label, LambdaPredicate(f)))
    def withPredicate(label: SchematicPredicateLabel[0], value: Formula): RuleParameters =
      withPredicate(label, _ => value)

    def withConnector[N <: Arity](
      label: SchematicConnectorLabel[N], f: FillArgs[SchematicPredicateLabel[0], N] => Formula
    )(using ValueOf[N]): RuleParameters = {
      require(label.arity > 0, "For consistency, use nullary predicate schemas instead of connectors")
      copy(connectors = connectors :+ AssignedConnector(label, LambdaConnector(f)))
    }

    def withVariable(label: VariableLabel, value: VariableLabel): RuleParameters =
      copy(variables = variables + (label -> value))
  }
  object RuleParameters {
    def apply(args: (AssignedFunction | AssignedPredicate | AssignedConnector | (VariableLabel, VariableLabel))*): RuleParameters =
      args.foldLeft(new RuleParameters())((acc, e) => e match {
        case assigned: AssignedFunction => acc.copy(functions = acc.functions :+ assigned)
        case assigned: AssignedPredicate => acc.copy(predicates = acc.predicates :+ assigned)
        case assigned: AssignedConnector => acc.copy(connectors = acc.connectors :+ assigned)
        case pair @ (_: VariableLabel, _: VariableLabel) => acc.copy(variables = acc.variables + pair)
      })
  }

  protected def applyRuleInference(
    parameters: RuleParameters,
    patternsFrom: IndexedSeq[PartialSequent],
    patternsTo: IndexedSeq[PartialSequent],
    valuesFrom: IndexedSeq[Sequent],
  ): Option[(IndexedSeq[Sequent], UnificationContext)] = {
    def parametersView: View[IndexedSeq[SequentSelector]] =
      if(patternsFrom.size == valuesFrom.size) {
        matchIndices(parameters.selectors, patternsFrom, valuesFrom)
      } else {
        View.empty
      }

    parametersView.flatMap { selectors =>
      val ctx = UnificationContext(
        parameters.predicates.map(r => r.schema -> r.lambda).toMap,
        parameters.functions.map(r => r.schema -> r.lambda).toMap,
        parameters.connectors.map(r => r.schema -> r.lambda).toMap)
      unifyAndResolve(patternsFrom, valuesFrom, patternsTo, ctx, selectors)
    }.headOption
  }

  /**
   * An instantiated rule. Note that the parameters can be incorrect, in that case the tactic will always fail.
   * @param rule the original rule
   * @param parameters the parameters used for the instantiation
   */
  case class RuleTactic private[RuleDefinitions](rule: Rule, parameters: RuleParameters) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      applyRuleInference(parameters, IndexedSeq(rule.conclusion), rule.hypotheses, IndexedSeq(proofGoal)).flatMap {
        case (newGoals, ctx) =>
          val stepsOption = rule.reconstruct.andThen(Some.apply).applyOrElse((proofGoal, ctx), _ => None)
          stepsOption.map(steps => (newGoals, () => steps))
      }
    }

    override def toString: String = s"${rule.getClass.getSimpleName}(...)"
  }

  /**
   * An rule is an object specifying a type of transformation on a justified statement or a proof goal.
   * It is characterized by a sequence of premises (also known as hypotheses) and a conclusion; all patterns.
   * It must also define a reconstruction function, in order to translate it to kernel proof steps.
   */
  sealed abstract class Rule {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    def reconstruct: ReconstructRule

    require(isLegalPatterns(hypotheses) && isLegalPatterns(IndexedSeq(conclusion)))

    final def apply(parameters: RuleParameters = RuleParameters()): RuleTactic =
      RuleTactic(this, parameters)

    final def apply(justification0: Justified, rest: Justified*): Option[Theorem] =
      apply(RuleParameters())((justification0 +: rest)*)(using justification0.environment)
    /*final def apply(parameters: RuleParameters)(justification0: Justified, rest: Justified*): Option[Theorem] = {
      val env = justification0.environment
      val justifications = justification0 +: rest
      apply(parameters)(justifications: _*)(using env)
    }*/
    final def apply(parameters: RuleParameters)(using env: ProofEnvironment): Option[Theorem] =
      apply(parameters)()

    final def apply(parameters: RuleParameters)(justifications: Justified*)(using env: ProofEnvironment): Option[Theorem] = {
      val justificationsSeq = justifications.toIndexedSeq
      val topSequents = justificationsSeq.map(_.sequent)
      applyRuleInference(parameters, hypotheses, IndexedSeq(conclusion), topSequents).flatMap {
        case (IndexedSeq(newSequent), ctx) =>
          reconstruct.andThen(Some.apply).applyOrElse((newSequent, ctx), _ => None).map { scSteps =>
            val scProof = lisa.kernel.proof.SCProof(scSteps, justificationsSeq.map(_.sequentAsKernel))
            env.mkTheorem(newSequent, scProof, justificationsSeq)
          }
        case _ => throw new Error
      }
    }

    override def toString: String = {
      val top = hypotheses.map(_.toString).mkString(" " * 6)
      val bottom = conclusion.toString
      val length = Math.max(top.length, bottom.length)

      def pad(s: String): String = " " * ((length - s.length) / 2) + s

      Seq(pad(top), "=" * length, pad(bottom)).mkString("\n")
    }
  }

  /**
   * A constructor for [[Rule]].
   */
  open class RuleBase(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule

  given Conversion[Rule, RuleTactic] = _()

}
