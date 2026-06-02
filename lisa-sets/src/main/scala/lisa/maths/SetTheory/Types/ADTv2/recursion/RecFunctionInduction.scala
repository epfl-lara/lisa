package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{Pattern, PatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{TypeSubstitution, instantiatedSemanticSignature, specializeFormula, specializeTerm}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate

private[recursion] object RecFunctionInduction {

  private def requireSchemaCoverage[N <: Arity](
      patternMatching: PatternSystem[N],
      schemas: PatternSchemas[N],
      schemaLabel: String,
      functionName: String
  ): Unit = {
    val expectedPatterns = patternMatching.patterns.toSet
    require(
      schemas.keySet == expectedPatterns,
      s"$schemaLabel($functionName): pattern schemas do not cover the pattern system."
    )
    patternMatching.patterns.foreach(pattern =>
      val (vars, _) = schemas(pattern)
      require(
        vars.length == pattern.binders.length,
        s"$schemaLabel($functionName): pattern schema for ${pattern.name} has arity ${vars.length}, expected ${pattern.binders.length}."
      )
    )
  }

  private def instantiateSchemaAtBranch(using proof: lisa.SetTheoryLibrary.Proof)(
      localAssumptions: Set[Expr[Prop]],
      branchVars: Seq[Variable[Ind]],
      branchPremise: proof.Fact,
      schema: (Seq[Variable[Ind]], Expr[Prop]),
      schemaFact: proof.Fact,
      errorContext: String
  ): proof.Fact = {
    val (schemaVars, _) = schema

    require(
      schemaVars.length == branchVars.length,
      s"$errorContext: schema arity mismatch (${schemaVars.length} vs ${branchVars.length})."
    )

    val schemaAtBranch = schemaVars.zip(branchVars).foldLeft(schemaFact)((fact, varsPair) =>
      fact.statement.right.head match
        case forall(v, phi) =>
          val instantiated = phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]
          have(fact.statement.left |- instantiated) by InstantiateForall(varsPair._2)(fact)
        case _ => throw UnreachableException
    )

    schemaAtBranch.statement.right.head match
      case antecedent ==> consequent =>
        val normalizedAntecedent = simplify(antecedent.asInstanceOf[Expr[Prop]])
        val normalizedBranchPremise = simplify(branchPremise.statement.right.head.asInstanceOf[Expr[Prop]])
        require(
          normalizedAntecedent == normalizedBranchPremise,
          s"$errorContext: schema antecedent does not match branch premise.\nSchema antecedent: $normalizedAntecedent\nBranch premise: $normalizedBranchPremise"
        )
        have(localAssumptions |- consequent.asInstanceOf[Expr[Prop]]) by Tautology.from(schemaAtBranch, branchPremise)
      case equalityFormula =>
        have(localAssumptions |- equalityFormula.asInstanceOf[Expr[Prop]]) by Restate.from(schemaAtBranch)
  }

  private def extractBodyAtBranch(using proof: lisa.SetTheoryLibrary.Proof)(
      equalityAtBranch: proof.Fact,
      functionHead: Expr[Ind],
      inputTerm: Expr[Ind],
      branchName: String,
      sideLabel: String
  ): Expr[Ind] = {
    asIndEquality(equalityAtBranch.statement.right.head.asInstanceOf[Expr[Prop]]) match
      case Some((leftEq, rightEq)) =>
        if leftEq == (functionHead * inputTerm) then rightEq
        else if rightEq == (functionHead * inputTerm) then leftEq
        else
          throw IllegalArgumentException(
            s"Unexpected $sideLabel-branch equality shape for $branchName: ${equalityAtBranch.statement.right.head}"
          )
      case _ =>
        throw IllegalArgumentException(
          s"Unexpected $sideLabel-branch equality shape for $branchName: ${equalityAtBranch.statement.right.head}"
        )
  }

  private def proveBodyEqualityFromRecursiveFacts(using proof: lisa.SetTheoryLibrary.Proof)(
      localAssumptions: Set[Expr[Prop]],
      leftBody: Expr[Ind],
      rightBody: Expr[Ind],
      recursiveFacts: Seq[proof.Fact],
      constructorName: String,
      contextLabel: String
  ): proof.Fact = {
    try LambdaBodyEquality.proveUnder(localAssumptions, leftBody, rightBody, recursiveFacts)
    catch
      case _: IllegalArgumentException =>
        throw IllegalArgumentException(
          s"$contextLabel: constructor $constructorName has mismatching bodies without recursive arguments: $leftBody vs $rightBody."
        )
  }

  private def liftBranchToInductiveCase[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      adt: SemanticADT[N],
      argType: Expr[Ind],
      syntacticSignature: Seq[(Variable[Ind], ConstructorArg)],
      propertyAt: Expr[Ind] => Expr[Prop],
      branchEquality: proof.Fact,
      selectSelfRefAssumption: (Variable[Ind], Set[Expr[Prop]]) => Expr[Prop]
  ): proof.Fact = {
    var liftedInductiveCase = branchEquality
    syntacticSignature.reverse.foreach((el) =>
      val (v, typ) = el
      val accRight = liftedInductiveCase.statement.right.head

      typ match
        case SelfRef =>
          val ihAssumptionAtVar = selectSelfRefAssumption(v, liftedInductiveCase.statement.left)
          val selfTypingAtVar = liftedInductiveCase.statement.left.find(typing =>
            typing == (v ∈ argType) || typing == (v :: argType)
          ).getOrElse(v ∈ argType)
          val ihLifted = have((liftedInductiveCase.statement -<? ihAssumptionAtVar).left |- ihAssumptionAtVar ==> accRight) by
            RightImplies.withParameters(ihAssumptionAtVar, accRight)(liftedInductiveCase)
          val typingLifted = have((ihLifted.statement -<? selfTypingAtVar).left |- selfTypingAtVar ==> (ihAssumptionAtVar ==> accRight)) by
            RightImplies.withParameters(selfTypingAtVar, ihAssumptionAtVar ==> accRight)(ihLifted)
          liftedInductiveCase = have(typingLifted.statement.left |- forall(v, selfTypingAtVar ==> (ihAssumptionAtVar ==> accRight))) by
            RightForall(typingLifted)

        case TypeArg(typeName) =>
          val typingAtVar = liftedInductiveCase.statement.left.find(typing =>
            typing match
              case VarTypeAssign(variable, _) => variable == v
              case _                          => false
          ).getOrElse(
            throw IllegalArgumentException(
              s"Missing specialized typing assumption for $v in constructor argument of type $typeName."
            )
          )
          val typingLifted = have((liftedInductiveCase.statement -<? typingAtVar).left |- typingAtVar ==> accRight) by
            RightImplies.withParameters(typingAtVar, accRight)(liftedInductiveCase)
          liftedInductiveCase = have(typingLifted.statement.left |- forall(v, typingAtVar ==> accRight)) by
            RightForall(typingLifted)
    )
    liftedInductiveCase
  }

  private def assemblePointwiseFromConstructorCases[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      adt: SemanticADT[N],
      typeSubstitutions: Seq[TypeSubstitution],
      assumptions: Set[Expr[Prop]],
      pointwiseGoal: Expr[Prop],
      prop: Expr[lisa.utils.fol.FOL.Arrow[Ind, Prop]],
      constructorCases: Seq[(SemanticConstructor[N], proof.Fact)],
      contextLabel: String
  ): proof.Fact = {
    val rawInductionGoal =
      adt.constructors.foldRight[Expr[Prop]](pointwiseGoal)((c, fc) =>
        specializeFormula(c.inductiveCase.substitute(P := prop).asInstanceOf[Expr[Prop]], typeSubstitutions) ==> fc
      )
    val inductionInstantiation = have(rawInductionGoal) by Restate.from(adt.inductionAt(typeSubstitutions) of (P := prop))

    val constructorImplications: Seq[proof.Fact] = constructorCases.map { case (constructor, caseFact) =>
      val expectedCase =
        specializeFormula(constructor.inductiveCase.substitute(P := prop).asInstanceOf[Expr[Prop]], typeSubstitutions)
      val normalizedExpectedCase = normalForm(expectedCase)
      val normalizedCase = have(assumptions |- normalizedExpectedCase) by Tableau.from(caseFact)
      have(assumptions |- expectedCase) by Restate.from(normalizedCase)
    }

    val assembledInduction = constructorImplications.foldLeft[proof.Fact](inductionInstantiation)((acc, caseImplication) =>
      acc.statement.right.head match
        case _ ==> remainder =>
          have(assumptions |- remainder.asInstanceOf[Expr[Prop]]) by Tautology.from(acc, caseImplication)
        case other =>
          throw IllegalArgumentException(
            s"Unexpected induction shape while assembling $contextLabel: $other"
          )
    )

    have(assumptions |- pointwiseGoal) by Restate.from(assembledInduction)
  }

  def pointwiseUniquenessAt[N <: Arity](
      adt: SemanticADT[N],
      patternMatching: PatternSystem[N],
      argType: Expr[Ind],
      typeSubstitutions: Seq[TypeSubstitution],
      inductionVariable: Variable[Ind],
      assumptions: Set[Expr[Prop]],
      propertyAt: Expr[Ind] => Expr[Prop],
      xFun: Expr[Ind],
      yFun: Expr[Ind],
      xDefinitionFormula: Expr[Prop],
      yDefinitionFormula: Expr[Prop],
      xPatternSchemas: PatternSchemas[N],
      yPatternSchemas: PatternSchemas[N]
  ): JUSTIFICATION = {
    requireSchemaCoverage(patternMatching, xPatternSchemas, "pointwiseUniquenessAt/x", "<anonymous>")
    requireSchemaCoverage(patternMatching, yPatternSchemas, "pointwiseUniquenessAt/y", "<anonymous>")

    val pointwiseGoal = ∀(inductionVariable, inductionVariable ∈ argType ==> propertyAt(inductionVariable))

    Lemma(assumptions |- pointwiseGoal) {
      val prop = λ(inductionVariable, propertyAt(inductionVariable))

      val constructorCases = adt.constructors.map(c =>
        val branchVars = c.variables1
        val branchInput = specializeTerm(c.appliedTerm(branchVars), typeSubstitutions)
        val branchTarget = propertyAt(branchInput)
        val constructorCaseGoal = normalForm(
          specializeFormula(c.inductiveCase.substitute(P := prop).asInstanceOf[Expr[Prop]], typeSubstitutions)
        )
        val specializedSignature = instantiatedSemanticSignature(c.semanticSignature(branchVars), typeSubstitutions)
        val localAssumptions = assumptions ++
          wellTypedSet(specializedSignature) ++
          c.syntacticSignature(branchVars).collect {
            case (v, SelfRef) => propertyAt(v)
          }.toSet

        c -> Lemma(assumptions |- constructorCaseGoal) {
          val argsTyped = have(localAssumptions |- wellTypedFormula(specializedSignature)) by Tautology
          val constructorPatterns = patternMatching.patternsFor(c)
          val selectionSchema = patternMatching.branchSelectionFor(c, branchInput)
          val selectionSchemaInContext = have(selectionSchema.statement.right.head) by Tautology.from(selectionSchema)
          val selectionAtBranchVars = have(
            localAssumptions |- seqOr(constructorPatterns.map(pattern =>
              pattern.branchConditionAt(branchVars) /\ (branchInput === pattern.inputTermAt(branchVars))
            ))
          ) by InstantiateForallSeq(branchVars)(selectionSchemaInContext)

          def instantiateCaseFromDefinition(using proof: lisa.SetTheoryLibrary.Proof)(
              contextAssumptions: Set[Expr[Prop]],
              definition: Expr[Prop],
              schema: (Seq[Variable[Ind]], Expr[Prop]),
              branchPremise: proof.Fact
          ): proof.Fact = {
            val (caseVars, caseSchemaFormula) = schema
            val definitionFact = have(contextAssumptions |- definition) by Tautology
            val schemaFromDefinition = have(definition |- caseSchemaFormula) by Tautology
            val caseSchema = have(contextAssumptions |- caseSchemaFormula) by
              Cut.withParameters(definition)(definitionFact, schemaFromDefinition)
            instantiateSchemaAtBranch(
              localAssumptions = contextAssumptions,
              branchVars = branchVars,
              branchPremise = branchPremise,
              schema = caseVars -> caseSchemaFormula,
              schemaFact = caseSchema,
              errorContext = s"pointwiseUniquenessAt/${c.name}"
            )
          }

          val branchEqualities = constructorPatterns.map(pattern =>
            have(
              localAssumptions + (pattern.branchConditionAt(branchVars) /\ (branchInput === pattern.inputTermAt(branchVars))) |- branchTarget
            ) subproof {
              val selectedPattern = assume(pattern.branchConditionAt(branchVars) /\ (branchInput === pattern.inputTermAt(branchVars)))
              val branchAssumptions = localAssumptions + selectedPattern.statement.left.head
              val patternGuard = have(pattern.branchConditionAt(branchVars)) by Tautology.from(selectedPattern)
              val branchInputEqPattern = have(branchInput === pattern.inputTermAt(branchVars)) by Tautology.from(selectedPattern)
              val patternPremise = have(branchAssumptions |- pattern.branchPremiseAt(branchVars)) by
                Tautology.from(argsTyped, patternGuard)

              val xAtBranch = instantiateCaseFromDefinition(
                contextAssumptions = branchAssumptions,
                definition = xDefinitionFormula,
                schema = xPatternSchemas(pattern),
                branchPremise = patternPremise
              )

              val yAtBranch = instantiateCaseFromDefinition(
                contextAssumptions = branchAssumptions,
                definition = yDefinitionFormula,
                schema = yPatternSchemas(pattern),
                branchPremise = patternPremise
              )

              val xBody = extractBodyAtBranch(
                equalityAtBranch = xAtBranch,
                functionHead = xFun,
                inputTerm = pattern.inputTermAt(branchVars),
                branchName = pattern.name,
                sideLabel = "x"
              )

              val yBody = extractBodyAtBranch(
                equalityAtBranch = yAtBranch,
                functionHead = yFun,
                inputTerm = pattern.inputTermAt(branchVars),
                branchName = pattern.name,
                sideLabel = "y"
              )

              val recursiveEqualityFacts = c.syntacticSignature(branchVars).collect {
                case (v, SelfRef) =>
                  have(branchAssumptions |- propertyAt(v)) by Tautology
              }

              val bodyEquality = proveBodyEqualityFromRecursiveFacts(
                localAssumptions = branchAssumptions,
                leftBody = xBody,
                rightBody = yBody,
                recursiveFacts = recursiveEqualityFacts,
                constructorName = s"${c.name}/${pattern.name}",
                contextLabel = "pointwiseUniquenessAt"
              )

              val xCtorToPattern = have(branchAssumptions |- (xFun * branchInput) === (xFun * pattern.inputTermAt(branchVars))) by
                Congruence.from(branchInputEqPattern)
              val yPatternToCtor = have(branchAssumptions |- (yFun * pattern.inputTermAt(branchVars)) === (yFun * branchInput)) by
                Congruence.from(branchInputEqPattern)

              val xBodyToYCtor = have(branchAssumptions |- xBody === (yFun * branchInput)) by Tautology.from(
                altEqualityTransitivity of (
                  x := xBody,
                  y := yBody,
                  z := yFun * branchInput
                ),
                bodyEquality,
                yAtBranch,
                yPatternToCtor
              )

              val branchEquality = have(branchAssumptions |- branchTarget) by Tautology.from(
                altEqualityTransitivity of (
                  x := xFun * branchInput,
                  y := xBody,
                  z := yFun * branchInput
                ),
                xCtorToPattern,
                xAtBranch,
                xBodyToYCtor
              )

              have(thesis) by Tautology.from(branchEquality)
            }
          )

          val branchEquality =
            if branchEqualities.size == 1 then
              have(localAssumptions |- branchTarget) by Tautology.from(selectionAtBranchVars, branchEqualities.head)
            else
              val branchDisjunctionCase = have(
                localAssumptions + selectionAtBranchVars.statement.right.head.asInstanceOf[Expr[Prop]] |- branchTarget
              ) by LeftOr(branchEqualities*)
              have(localAssumptions |- branchTarget) by Tautology.from(
                selectionAtBranchVars,
                branchDisjunctionCase
              )

          val liftedInductiveCase = liftBranchToInductiveCase(
            adt = adt,
            argType = argType,
            syntacticSignature = c.syntacticSignature(branchVars),
            propertyAt = propertyAt,
            branchEquality = branchEquality,
            selectSelfRefAssumption = (v, leftAssumptions) =>
              leftAssumptions.collectFirst {
                case assumption if asIndEquality(assumption).exists((lhs, rhs) =>
                    lhs == (xFun * v) && rhs == (yFun * v)
                  ) => assumption
              }.getOrElse(propertyAt(v))
          )

          have(thesis) by Tautology.from(liftedInductiveCase)
        }
      )

      val pointwiseFromInduction = assemblePointwiseFromConstructorCases(
        adt = adt,
        typeSubstitutions = typeSubstitutions,
        assumptions = assumptions,
        pointwiseGoal = pointwiseGoal,
        prop = prop,
        constructorCases = constructorCases,
        contextLabel = "pointwise uniqueness proof"
      )
      have(thesis) by Restate.from(pointwiseFromInduction)
    }
  }
}
