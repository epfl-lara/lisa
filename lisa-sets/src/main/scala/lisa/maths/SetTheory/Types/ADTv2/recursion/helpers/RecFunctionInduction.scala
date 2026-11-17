package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.specializedConstructors
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.LimitKernel
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.DefinedProperty
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.Weakening

/**
 * Quantified clause formulas paired with their ordered binders.
 */
private[recursion] type PatternSchemas =
  Map[Clause[Expr[Ind]], (Seq[Variable[Ind]], Expr[Prop])]

/**
 * Recognizes equality between set-valued expressions.
 */
private[recursion] def asIndEquality(formula: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = formula match
  case App(App(eqFun, lhs: Expr[Ind]), rhs: Expr[Ind]) if eqFun == equality => Some((lhs, rhs))
  case _ => None

private[recursion] object RecFunctionInduction {

  private inline def app(f: Expr[Ind])(x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def requireSchemaCoverage(
      patternMatching: PatternSystem[Expr[Ind]],
      schemas: PatternSchemas,
      schemaLabel: String
  ): Unit = {
    val expectedPatterns = patternMatching.clauses.toSet
    require(
      schemas.keySet == expectedPatterns,
      s"$schemaLabel: pattern schemas do not cover the pattern system."
    )
    patternMatching.clauses.foreach(pattern =>
      val (vars, _) = schemas(pattern)
      require(
        vars.length == pattern.binders.length,
        s"$schemaLabel: pattern schema for ${pattern.name} has arity ${vars.length}, expected ${pattern.binders.length}."
      )
    )
  }

  private def caseEqualityAtBranch(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      contextAssumptions: Set[Expr[Prop]],
      definition: Expr[Prop],
      schema: (Seq[Variable[Ind]], Expr[Prop]),
      branchVars: Seq[Variable[Ind]],
      branchPremise: proof.Fact,
      defUnfold: proof.Fact,
      functionHead: Expr[Ind],
      inputTerm: Expr[Ind],
      errorContext: String
  ): (Expr[Ind], proof.Fact) = {
    val (caseVars, caseSchemaFormula) = schema
    // Unfold the defining predicate only for this clause, keeping the other assumptions atomic.
    val definitionFact = have(contextAssumptions |- definition) by Weakening(defUnfold)
    val schemaFromDefinition = have(definition |- caseSchemaFormula) by Tautology
    val caseSchema = have(contextAssumptions |- caseSchemaFormula) by
      Cut.withParameters(definition)(definitionFact, schemaFromDefinition)

    require(
      caseVars.length == branchVars.length,
      s"$errorContext: schema arity mismatch (${caseVars.length} vs ${branchVars.length})."
    )

    val schemaAtBranch = branchVars.foldLeft(caseSchema) { (fact, argument) =>
      fact.statement.right.head match
        case forall(v, phi) =>
          val instantiated = phi.substitute(v := argument)
          have(fact.statement.left |- instantiated) by InstantiateForall(argument)(fact)
        case _ => throw UnreachableException
    }
    val atBranch = schemaAtBranch.statement.right.head match
      case antecedent ==> consequent =>
        require(
          simplify(antecedent) == simplify(branchPremise.statement.right.head),
          s"$errorContext: schema antecedent does not match branch premise."
        )

        val premiseAsAnte = have(branchPremise.statement.left |- antecedent) by Restate.from(branchPremise)
        val viaImpl = have((schemaAtBranch.statement.left + antecedent) |- consequent) by Weakening(schemaAtBranch)
        val combined = have((schemaAtBranch.statement.left ++ branchPremise.statement.left) |- consequent) by Cut(premiseAsAnte, viaImpl)
        have(contextAssumptions |- consequent) by Weakening(combined)
      case equalityFormula =>
        have(contextAssumptions |- equalityFormula) by Restate.from(schemaAtBranch)

    val applied = functionHead * inputTerm
    asIndEquality(atBranch.statement.right.head) match
      case Some((lhs, rhs)) if lhs == applied =>
        (rhs, atBranch)
      case Some((lhs, rhs)) if rhs == applied =>
        (lhs, have(atBranch.statement.left |- (applied === lhs)) by Congruence.from(atBranch))
      case _ =>
        throw IllegalArgumentException(
          s"$errorContext: expected an equality with `$applied` on one side, got ${atBranch.statement.right.head}."
        )
  }

  /**
   * Proves pointwise equality from two instances of the defining property by height induction.
   */
  def pointwiseUniquenessAt(
      adt: SemanticADT,
      patternMatching: PatternSystem[Expr[Ind]],
      argType: Expr[Ind],
      typeSubstitutions: Seq[TypeSubstitution],
      inductionVariable: Variable[Ind],
      assumptions: Set[Expr[Prop]],
      propertyAt: Expr[Ind] => Expr[Prop],
      xFun: Expr[Ind],
      yFun: Expr[Ind],
      xDefinitionFormula: Expr[Prop],
      yDefinitionFormula: Expr[Prop],
      xPatternSchemas: PatternSchemas,
      yPatternSchemas: PatternSchemas,
      definitionProperty: DefinedProperty
  ): THM = {
    requireSchemaCoverage(patternMatching, xPatternSchemas, "pointwiseUniquenessAt/x")
    requireSchemaCoverage(patternMatching, yPatternSchemas, "pointwiseUniquenessAt/y")

    val pointwiseGoal = ∀(inductionVariable, inductionVariable ∈ argType ==> propertyAt(inductionVariable))

    Lemma(assumptions |- pointwiseGoal) {
      // Keep the defining hypotheses available in nested branch proofs.
      assumptions.foreach(a => assume(a))
      val heightFun = specializeTerm(adt.height.function, typeSubstitutions)
      val constructorsAt = specializedConstructors(patternMatching, typeSubstitutions)
      val reserved: Seq[Expr[?]] =
        Seq(argType, heightFun, inductionVariable, pointwiseGoal, xFun, yFun, xDefinitionFormula, yDefinitionFormula) ++ assumptions ++
          patternMatching.clauses.flatMap(pattern => Seq(pattern.body, pattern.freshBranchPremise, pattern.freshInputTerm) ++ pattern.binders ++ pattern.variables2)
      val nVar = Variable[Ind](freshId(reserved, "nVar"))
      val slicePoint = inductionVariable
      val P = λ(nVar, ∀(slicePoint ∈ app(heightFun)(nVar), propertyAt(slicePoint)))

      val hValid = have(adt.height.predicateAt(typeSubstitutions)(heightFun)) by
        Weakening(adt.height.validAt(typeSubstitutions))

      val noElemAtEmpty = have(!(slicePoint ∈ app(heightFun)(∅))) by Cut(
        hValid,
        adt.height.zeroAt(typeSubstitutions, Seq(h := heightFun, x := slicePoint))
      )

      val base = have(P(∅)) subproof {
        have(slicePoint ∈ app(heightFun)(∅) |- propertyAt(slicePoint)) by
          Tautology.from(noElemAtEmpty)
        thenHave((slicePoint ∈ app(heightFun)(∅)) ==> propertyAt(slicePoint)) by RightImplies
        thenHave(∀(slicePoint, (slicePoint ∈ app(heightFun)(∅)) ==> propertyAt(slicePoint))) by RightForall
        thenHave(thesis) by Restate
      }

      val step = {
        have((nVar ∈ N) ==> (P(nVar) ==> P(S(nVar)))) subproof {
          val nInN = assume(nVar ∈ N)
          assume(P(nVar))
          // Reuse branch assembly, supplying each candidate's defining equation.
          PointwiseAgreementStep.pointwiseAgreementOnSucc(
            patternMatching = patternMatching,
            heightFun = heightFun,
            constructorsAt = constructorsAt,
            ambientTerm = slicePoint,
            currentIndex = nVar,
            currentIndexInN = nInN,
            hValid = hValid,
            heightSuccStrong = adt.height.successorStrongAt(typeSubstitutions, Seq(h := heightFun, n := nVar, x := slicePoint)),
            goalEqAt = propertyAt(slicePoint)
          )(new PointwiseAgreementStep.PatternCaseEquations {
            val recursiveType: Expr[Ind] = argType
            val sliceLeft: Expr[Ind] = xFun
            val sliceRight: Expr[Ind] = yFun

            // This callback runs inside a nested branch proof.
            def sliceAgreement(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
              have(
                ∀(slicePoint, (slicePoint ∈ app(heightFun)(nVar)) ==> propertyAt(slicePoint))
              ) by Restate.from(assume(P(nVar)))

            def bodyEqAssumptions(using
                proof: lisa.SetTheoryLibrary.Proof
            )(
                pattern: Clause[Expr[Ind]],
                patternGuard: proof.Fact
            ): Set[Expr[Prop]] = {
              val baseContext = Set[Expr[Prop]](
                slicePoint ∈ app(heightFun)(S(nVar)),
                P(nVar),
                nVar ∈ N,
                pattern.branchSelectionBody(slicePoint)
              )
              if simplify(pattern.freshBranchCondition) == ⊤ then baseContext
              else baseContext + pattern.freshBranchCondition
            }

            def caseEquation(using
                proof: lisa.SetTheoryLibrary.Proof
            )(
                pattern: Clause[Expr[Ind]],
                slice: Expr[Ind],
                patternPremise: proof.Fact,
                patternGuard: proof.Fact,
                bodyEqAssumptions: Set[Expr[Prop]]
            ): (Expr[Ind], proof.Fact) = {
              val (definition, schema, side) =
                if (slice == xFun) then (xDefinitionFormula, xPatternSchemas(pattern), "x")
                else (yDefinitionFormula, yPatternSchemas(pattern), "y")
              caseEqualityAtBranch(
                contextAssumptions = assumptions ++ bodyEqAssumptions,
                definition = definition,
                schema = schema,
                branchVars = pattern.variables2,
                branchPremise = patternPremise,
                defUnfold = definitionProperty.unfoldAt(slice),
                functionHead = slice,
                inputTerm = pattern.freshInputTerm,
                errorContext = s"pointwiseUniquenessAt/$side/${pattern.name}"
              )
            }
          })
        }
        thenHave(∀(nVar, (nVar ∈ N) ==> (P(nVar) ==> P(S(nVar))))) by RightForall

      }

      val theoremP = variable[Ind >>: Prop]("P")
      val allHeights = have(∀(nVar, (nVar ∈ N) ==> P(nVar))) by
        Tautology.from(omegaSuccessorInduction of (theoremP := P, m := nVar, n := nVar), base, step)
      have(inductionVariable ∈ argType ==> propertyAt(inductionVariable)) subproof {
        val inArg = assume(inductionVariable ∈ argType)
        val someHeight = have(∃(nVar, (nVar ∈ N) /\ (inductionVariable ∈ app(heightFun)(nVar)))) by
          Tautology.from(
            hValid,
            inArg,
            adt.height.termHasHeightAt(typeSubstitutions, Seq(x := inductionVariable, h := heightFun)),
            LimitKernel.pointHasSomeHeightAt(argType, heightFun, inductionVariable)
          )

        have((nVar ∈ N) /\ (inductionVariable ∈ app(heightFun)(nVar)) |- propertyAt(inductionVariable)) subproof {
          assume((nVar ∈ N) /\ (inductionVariable ∈ app(heightFun)(nVar)))
          val nInN = have(nVar ∈ N) by Tautology
          val pointInHeight = have(inductionVariable ∈ app(heightFun)(nVar)) by Tautology
          val sliceAgreement = have(P(nVar)) by Tautology.from(
            nInN,
            have(nVar ∈ N ==> P(nVar)) by InstantiateForall(nVar)(allHeights)
          )
          val agreementAtN = have((inductionVariable ∈ app(heightFun)(nVar)) ==> propertyAt(inductionVariable)) by
            InstantiateForall(inductionVariable)(
              have(∀(slicePoint, (slicePoint ∈ app(heightFun)(nVar)) ==> propertyAt(slicePoint))) by
                Restate.from(sliceAgreement)
            )
          have(propertyAt(inductionVariable)) by Tautology.from(nInN, pointInHeight, agreementAtN)
        }
        val fromExists = thenHave(∃(nVar, (nVar ∈ N) /\ (inductionVariable ∈ app(heightFun)(nVar))) |- propertyAt(inductionVariable)) by
          LeftExists
        have(propertyAt(inductionVariable)) by Cut(someHeight, fromExists)
      }
      thenHave(∀(inductionVariable, inductionVariable ∈ argType ==> propertyAt(inductionVariable))) by RightForall
      thenHave(thesis) by Restate
    }
  }
}
