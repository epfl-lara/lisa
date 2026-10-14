package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.specializedConstructors
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.LimitKernel
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeFormula
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] type PatternSchemas[N <: Arity] =
  Map[Pattern[N], (Seq[Variable[Ind]], Expr[Prop])]

private[recursion] def asIndEquality(formula: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = formula match
  case App(App(eqFun, lhs: Expr[Ind]), rhs: Expr[Ind]) if eqFun == equality => Some((lhs, rhs))
  case _ => None

private[recursion] object RecFunctionInduction {

  private inline def app(f: Expr[Ind])(x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

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

  private def caseEqualityAtBranch(using proof: lisa.SetTheoryLibrary.Proof)(
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
    // `contextAssumptions` carries the opaque `Def(·)`; unfold it to `definition` here
    // (the only place the real definition is needed). `Weakening` keeps the rest of the
    // context atomic instead of decomposing it.
    val definitionFact = have(contextAssumptions |- definition) by Weakening(defUnfold)
    val schemaFromDefinition = have(definition |- caseSchemaFormula) by Tautology
    val caseSchema = have(contextAssumptions |- caseSchemaFormula) by
      Cut.withParameters(definition)(definitionFact, schemaFromDefinition)

    val (schemaVars, _) = caseVars -> caseSchemaFormula

    require(
      schemaVars.length == branchVars.length,
      s"$errorContext: schema arity mismatch (${schemaVars.length} vs ${branchVars.length})."
    )

    val schemaAtBranch = schemaVars
      .zip(branchVars)
      .foldLeft(caseSchema)((fact, varsPair) =>
        fact.statement.right.head match
          case forall(v, phi) =>
            val instantiated = phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]
            have(fact.statement.left |- instantiated) by InstantiateForall(varsPair._2)(fact)
          case _ => throw UnreachableException
      )
    val atBranch = schemaAtBranch.statement.right.head match
      case antecedent ==> consequent =>
        require(
          simplify(antecedent) == simplify(branchPremise.statement.right.head.asInstanceOf[Expr[Prop]]),
          s"$errorContext: schema antecedent does not match branch premise."
        )
        
        val premiseAsAnte = have(branchPremise.statement.left |- antecedent) by Restate.from(branchPremise)
        val viaImpl = have((schemaAtBranch.statement.left + antecedent) |- consequent) by Weakening(schemaAtBranch)
        val combined = have((schemaAtBranch.statement.left ++ branchPremise.statement.left) |- consequent) by Cut(premiseAsAnte, viaImpl)
        have(contextAssumptions |- consequent) by Weakening(combined)
      case equalityFormula =>
        have(contextAssumptions |- equalityFormula.asInstanceOf[Expr[Prop]]) by Restate.from(schemaAtBranch)

    val applied = functionHead * inputTerm
    asIndEquality(atBranch.statement.right.head.asInstanceOf[Expr[Prop]]) match
      case Some((lhs, rhs)) if lhs == applied =>
        (rhs, have(atBranch.statement.left |- (applied === rhs)) by Restate.from(atBranch))
      case Some((lhs, rhs)) if rhs == applied =>
        (lhs, have(atBranch.statement.left |- (applied === lhs)) by Congruence.from(atBranch))
      case _ =>
        throw IllegalArgumentException(
          s"$errorContext: expected an equality with `$applied` on one side, got ${atBranch.statement.right.head}."
        )
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
      yPatternSchemas: PatternSchemas[N],
      // `Def(x) ⊢ xDefinitionFormula` / `Def(y) ⊢ yDefinitionFormula`: the assumptions are
      // the opaque `Def(·)`; these unfold them to the real definition only where a case
      // schema is extracted.
      xDefUnfold: THM,
      yDefUnfold: THM
  ): THM = {
    requireSchemaCoverage(patternMatching, xPatternSchemas, "pointwiseUniquenessAt/x", "<anonymous>")
    requireSchemaCoverage(patternMatching, yPatternSchemas, "pointwiseUniquenessAt/y", "<anonymous>")

    val pointwiseGoal = ∀(inductionVariable, inductionVariable ∈ argType ==> propertyAt(inductionVariable))

    Lemma(assumptions |- pointwiseGoal) {
      // Make the recursion hypotheses (the Lemma antecedents) ambient, so that
      // facts derived from the function definitions inside nested subproofs can
      // be re-normalized under a restricted local context without losing them
      // (mirrors WitnessAgreement, which assumes all its antecedents up front).
      assumptions.foreach(a => assume(a))
      val heightFun = specializeTerm(adt.height.function, typeSubstitutions)
      val constructorsAt = specializedConstructors(adt.constructors, typeSubstitutions)
      val nVar = variable[Ind]
      val slicePoint = inductionVariable
      val P = λ(nVar, ∀(slicePoint ∈ app(heightFun)(nVar), propertyAt(slicePoint)))

      

      val hValid = have(specializeFormula(adt.height.predicate(heightFun), typeSubstitutions)) by
        Weakening(adt.height.validAt(typeSubstitutions))

      val noElemAtEmpty = have(!(slicePoint ∈ app(heightFun)(∅))) by Cut(
        hValid,
        adt.height.zeroAt(typeSubstitutions) of (h := heightFun, x := slicePoint)
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
          // Shared S-step orchestration (height decomposition + branch selection +
          // per-pattern assembly) lives in PointwiseAgreementStep; only the
          // uniqueness-specific case equation `fun * input === body`, read from the
          // function definitions, is supplied here via [[PatternCaseEquations]].
          PointwiseAgreementStep.pointwiseAgreementOnSucc(
            patternMatching = patternMatching,
            heightFun = heightFun,
            constructorsAt = constructorsAt,
            ambientTerm = slicePoint,
            currentIndex = nVar,
            currentIndexInN = nInN,
            hValid = hValid,
            heightSuccStrong = adt.height.successorStrongAt(typeSubstitutions),
            goalEqAt = propertyAt(slicePoint)
          )(new PointwiseAgreementStep.PatternCaseEquations[N] {
            val recursiveType: Expr[Ind] = argType
            val heightMembershipMonotonic: THM = adt.height.membershipMonotonicAt(typeSubstitutions)
            val sliceLeft: Expr[Ind] = xFun
            val sliceRight: Expr[Ind] = yFun

            // Each method re-`assume`s the ambient hypotheses (idempotent) since it runs in
            // a nested proof, not the enclosing lemma proof.
            def sliceAgreement(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
              have(
                ∀(slicePoint, (slicePoint ∈ app(heightFun)(nVar)) ==> propertyAt(slicePoint))
              ) by Restate.from(assume(P(nVar)))

            def bodyEqAssumptions(using proof: lisa.SetTheoryLibrary.Proof)(
                pattern: Pattern[N],
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

            def caseEquation(using proof: lisa.SetTheoryLibrary.Proof)(
                pattern: Pattern[N],
                slice: Expr[Ind],
                patternPremise: proof.Fact,
                patternGuard: proof.Fact,
                bodyEqAssumptions: Set[Expr[Prop]]
            ): (Expr[Ind], proof.Fact) = {
              val (definition, schema, defUnfold, side) =
                if (slice == xFun) then (xDefinitionFormula, xPatternSchemas(pattern), xDefUnfold, "x")
                else (yDefinitionFormula, yPatternSchemas(pattern), yDefUnfold, "y")
              caseEqualityAtBranch(
                contextAssumptions = assumptions ++ bodyEqAssumptions,
                definition = definition,
                schema = schema,
                branchVars = pattern.variables2,
                branchPremise = patternPremise,
                defUnfold = defUnfold,
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
            adt.height.termHasHeightAt(typeSubstitutions) of (x := inductionVariable, h := heightFun),
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
