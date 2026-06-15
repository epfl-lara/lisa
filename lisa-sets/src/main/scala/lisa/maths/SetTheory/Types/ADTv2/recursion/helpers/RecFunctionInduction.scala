package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.SpecializedConstructorFacts
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.specializedConstructors
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.LimitKernel
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.WitnessCaseExtensionality
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeFormula
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.ProofTacticLib.Arity

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
        require(
          simplify(antecedent) == simplify(branchPremise.statement.right.head.asInstanceOf[Expr[Prop]]),
          s"$errorContext: schema antecedent does not match branch premise."
        )
        // 1. Re-derive the branch premise in the schema's (simplified) antecedent form.
        //    OL-normalization is polynomial — no propositional search.
        val premiseAsAnte = have(branchPremise.statement.left |- antecedent) by Restate.from(branchPremise)
        // 2. Modus ponens via kernel rules: antecedent and consequent stay atomic, so cost is linear in formula size.
        val mp = have( (antecedent ==> consequent, antecedent) |- consequent) by LeftImplies.withParameters(antecedent, consequent)(
          have(antecedent |- antecedent) by Hypothesis,
          have(consequent |- consequent) by Hypothesis
        )
        val viaImpl  = have((schemaAtBranch.statement.left + antecedent) |- consequent) by Cut(schemaAtBranch, mp)
        val combined = have((schemaAtBranch.statement.left ++ branchPremise.statement.left) |- consequent) by Cut(premiseAsAnte, viaImpl)
        have(localAssumptions |- consequent) by Weakening(combined)
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

  private def orientEquality(using proof: lisa.SetTheoryLibrary.Proof)(
      equalityAtBranch: proof.Fact,
      expectedLeft: Expr[Ind],
      expectedRight: Expr[Ind],
      errorContext: String
  ): proof.Fact =
    asIndEquality(equalityAtBranch.statement.right.head.asInstanceOf[Expr[Prop]]) match
      case Some((leftEq, rightEq)) if leftEq == expectedLeft && rightEq == expectedRight =>
        have(equalityAtBranch.statement.left |- (expectedLeft === expectedRight)) by Restate.from(equalityAtBranch)
      case Some((leftEq, rightEq)) if leftEq == expectedRight && rightEq == expectedLeft =>
        have(equalityAtBranch.statement.left |- (expectedLeft === expectedRight)) by
          Congruence.from(equalityAtBranch)
      case _ =>
        throw IllegalArgumentException(
          s"$errorContext: could not orient equality ${equalityAtBranch.statement.right.head} as $expectedLeft === $expectedRight."
        )

  private def normalizeFactInContext(using proof: lisa.SetTheoryLibrary.Proof)(
      localContext: Set[Expr[Prop]],
      fact: proof.Fact,
      expectedFormula: Expr[Prop],
      errorContext: String
  ): proof.Fact = {
    require(
      simplify(fact.statement.right.head.asInstanceOf[Expr[Prop]]) == simplify(expectedFormula),
      s"$errorContext: expected $expectedFormula but got ${fact.statement.right.head}."
    )
    have(localContext |- expectedFormula) by Restate.from(fact)
  }

  private def normalizeBranchFacts(using proof: lisa.SetTheoryLibrary.Proof)(
      localContext: Set[Expr[Prop]],
      pointEqInputFact: proof.Fact,
      leftEqualityAtInput: proof.Fact,
      rightEqualityAtInput: proof.Fact,
      bodyEqualityAtInput: proof.Fact,
      slicePoint: Expr[Ind],
      inputTerm: Expr[Ind],
      xFun: Expr[Ind],
      yFun: Expr[Ind],
      xBody: Expr[Ind],
      yBody: Expr[Ind],
      errorContext: String
  ): (Set[Expr[Prop]], proof.Fact, proof.Fact, proof.Fact, proof.Fact) = {
    val pointEqInput = normalizeFactInContext(
      localContext = localContext,
      fact = pointEqInputFact,
      expectedFormula = slicePoint === inputTerm,
      errorContext = s"$errorContext/input"
    )
    val leftAtInput = normalizeFactInContext(
      localContext = localContext,
      fact = leftEqualityAtInput,
      expectedFormula = (xFun * inputTerm) === xBody,
      errorContext = s"$errorContext/left"
    )
    val rightAtInput = normalizeFactInContext(
      localContext = localContext,
      fact = rightEqualityAtInput,
      expectedFormula = (yFun * inputTerm) === yBody,
      errorContext = s"$errorContext/right"
    )
    val bodyEquality = normalizeFactInContext(
      localContext = localContext,
      fact = bodyEqualityAtInput,
      expectedFormula = xBody === yBody,
      errorContext = s"$errorContext/body"
    )
    (
      localContext,
      pointEqInput,
      leftAtInput,
      rightAtInput,
      bodyEquality
    )
  }

  private def proveBranchPointwiseAgreement(using proof: lisa.SetTheoryLibrary.Proof)(
      normalized: (Set[Expr[Prop]], proof.Fact, proof.Fact, proof.Fact, proof.Fact),
      propertyAt: Expr[Ind] => Expr[Prop],
      slicePoint: Expr[Ind],
      xFun: Expr[Ind],
      yFun: Expr[Ind]
  ): proof.Fact = {
    val (localContext, pointEqInput, leftAtInput, rightAtInput, bodyEquality) = normalized
    val agreement = WitnessCaseExtensionality.pointwiseAgreementAt(
      leftWitness = xFun,
      rightWitness = yFun,
      ambientTerm = slicePoint,
      ambientEqInput = pointEqInput,
      leftAtInput = leftAtInput,
      rightAtInput = rightAtInput,
      bodyEquality = bodyEquality
    )
    have(localContext |- propertyAt(slicePoint)) by Restate.from(agreement)
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
      val heightMembershipMonotonic = adt.height.membershipMonotonicAt(typeSubstitutions)
      val constructorsAt = specializedConstructors(adt.constructors, typeSubstitutions)
      val nVar = variable[Ind]
      val slicePoint = inductionVariable
      val Pred = variable[Ind >>: Prop]("P")
      val P = λ(nVar, ∀(slicePoint ∈ app(heightFun)(nVar), propertyAt(slicePoint)))

      def instantiateCaseFromDefinition(using proof: lisa.SetTheoryLibrary.Proof)(
          contextAssumptions: Set[Expr[Prop]],
          definition: Expr[Prop],
          schema: (Seq[Variable[Ind]], Expr[Prop]),
          branchVars: Seq[Variable[Ind]],
          branchPremise: proof.Fact,
          defUnfold: proof.Fact,
          errorContext: String
      ): proof.Fact = {
        val (caseVars, caseSchemaFormula) = schema
        // `contextAssumptions` carries the opaque `Def(·)`; unfold it to `definition` here
        // (the only place the real definition is needed). `Weakening` keeps the rest of the
        // context atomic instead of decomposing it.
        val definitionFact =  have(contextAssumptions |- definition) by Weakening(defUnfold)
        val schemaFromDefinition = have(definition |- caseSchemaFormula) by Tautology
        val caseSchema = have(contextAssumptions |- caseSchemaFormula) by
          Cut.withParameters(definition)(definitionFact, schemaFromDefinition)
        instantiateSchemaAtBranch(
          localAssumptions = contextAssumptions,
          branchVars = branchVars,
          branchPremise = branchPremise,
          schema = caseVars -> caseSchemaFormula,
          schemaFact = caseSchema,
          errorContext = errorContext
        )
      }

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

      val step = Time.measure("Uniqueness/pointwise/step"){ have(∀(nVar, (nVar ∈ N) ==> (P(nVar) ==> P(successor(nVar))))) subproof {
        have((nVar ∈ N) ==> (P(nVar) ==> P(successor(nVar)))) subproof {
          val nInN = assume(nVar ∈ N)
          assume(P(nVar))
          // Shared successor-step orchestration (height decomposition + branch
          // selection + case assembly); only the uniqueness-specific per-pattern
          // proof — case equations from the function definitions + body equality +
          // pointwise agreement — lives in the callback below.
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
          )(new PointwiseAgreementStep.SelectedPatternProver[N] {
            def apply(using proof: lisa.SetTheoryLibrary.Proof)(
                sc: SpecializedConstructorFacts[N],
                argsTypedAtHeight: proof.Fact,
                argsTypedSemantic: proof.Fact,
                aEqApplied: proof.Fact
            ): Pattern[N] => proof.Fact = {
              // Re-establish ambient facts directly in this (inner) proof: captured
              // outer-proof facts cannot lift into the abstract `proof` here, so we
              // re-`assume` hypotheses already in the lemma's antecedent (idempotent).
              val nInN = assume(nVar ∈ N)
              val ih = assume(P(nVar))
              val hValid = have(specializeFormula(adt.height.predicate(heightFun), typeSubstitutions)) by
                Weakening(adt.height.validAt(typeSubstitutions))
              val ihAtN = have(
                ∀(slicePoint, (slicePoint ∈ app(heightFun)(nVar)) ==> propertyAt(slicePoint))
              ) by Restate.from(ih)
              val c = sc.underlying

              val selfArgEqualities = sc.selfRefVariables2.map(v =>
                val vInHeight = have(v ∈ app(heightFun)(nVar)) by Tautology.from(argsTypedAtHeight)
                RecursiveAgreement.selfAgreementFromForall(
                  heightFun = heightFun,
                  currentIndex = nVar,
                  leftFun = xFun,
                  rightFun = yFun,
                  agreeForall = ihAtN,
                  point = v,
                  pointInHeight = vInHeight
                )
              )

              (pattern: Pattern[N]) => Time.measure("Uniqueness/pointwise/patternEqualities"){
                  have(
                    pattern.branchSelectionBody(slicePoint) |- propertyAt(slicePoint)
                  ) subproof {
                    val selectedPattern = assume(pattern.branchSelectionBody(slicePoint))
                    val patternGuard = have(pattern.freshBranchCondition) by Restate.from(selectedPattern)
                    val pointEqPattern = have(slicePoint === pattern.freshInputTerm) by Restate.from(selectedPattern)
                    val patternPremise = Time.measure(s"Uniqueness/patternPremise"){have(pattern.freshBranchPremise) by Tautology.from(argsTypedSemantic, patternGuard)}
                    val innerAgreements = Time.measure(s"Uniqueness/innerAgreements"){
                      RecursiveAgreement.selfAgreementFromForallAt2(
                        pattern = pattern,
                        recursiveType = argType,
                        heightMembershipMonotonic = heightMembershipMonotonic,
                        argsTypedAtHeight = argsTypedAtHeight,
                        leafTyping = patternPremise,
                        patternGuard = patternGuard,
                        heightFun = heightFun,
                        hValid = hValid,
                        currentIndex = nVar,
                        currentIndexInN = nInN,
                        leftFun = xFun,
                        rightFun = yFun,
                        agreeForall = ihAtN
                      )
                    }
                    val selectedPatternFormula = pattern.branchSelectionBody(slicePoint)
                    val baseContext = Set[Expr[Prop]](
                      slicePoint ∈ app(heightFun)(successor(nVar)),
                      P(nVar),
                      nVar ∈ N,
                      selectedPatternFormula
                    )
                    val localContext =
                      if simplify(pattern.freshBranchCondition) == ⊤ then baseContext
                      else baseContext + pattern.freshBranchCondition
                    val instantiationContext = assumptions ++ localContext


                    val xAtBranch = instantiateCaseFromDefinition(
                      contextAssumptions = instantiationContext,
                      definition = xDefinitionFormula,
                      schema = xPatternSchemas(pattern),
                      branchVars = pattern.variables2,
                      branchPremise = patternPremise,
                      defUnfold = xDefUnfold,
                      errorContext = s"pointwiseUniquenessAt/x/${c.name}/${pattern.name}"
                    )
                    val yAtBranch = instantiateCaseFromDefinition(
                      contextAssumptions = instantiationContext,
                      definition = yDefinitionFormula,
                      schema = yPatternSchemas(pattern),
                      branchVars = pattern.variables2,
                      branchPremise = patternPremise,
                      defUnfold = yDefUnfold,
                      errorContext = s"pointwiseUniquenessAt/y/${c.name}/${pattern.name}"
                    )

                    val xBody = extractBodyAtBranch(
                      equalityAtBranch = xAtBranch,
                      functionHead = xFun,
                      inputTerm = pattern.freshInputTerm,
                      branchName = pattern.name,
                      sideLabel = "x"
                    )
                    val yBody = extractBodyAtBranch(
                      equalityAtBranch = yAtBranch,
                      functionHead = yFun,
                      inputTerm = pattern.freshInputTerm,
                      branchName = pattern.name,
                      sideLabel = "y"
                    )
                    val xAtPattern = orientEquality(
                      equalityAtBranch = xAtBranch,
                      expectedLeft = xFun * pattern.freshInputTerm,
                      expectedRight = xBody,
                      errorContext = s"pointwiseUniquenessAt/x/${c.name}/${pattern.name}"
                    )
                    val yPatternToBody = orientEquality(
                      equalityAtBranch = yAtBranch,
                      expectedLeft = yFun * pattern.freshInputTerm,
                      expectedRight = yBody,
                      errorContext = s"pointwiseUniquenessAt/y/${c.name}/${pattern.name}"
                    )

                    val bodyEquality = proveBodyEqualityFromRecursiveFacts(
                      localAssumptions = localContext,
                      leftBody = xBody,
                      rightBody = yBody,
                      recursiveFacts = selfArgEqualities ++ innerAgreements,
                      constructorName = s"${c.name}/${pattern.name}",
                      contextLabel = "pointwiseUniquenessAt"
                    )

                    val patternEqPoint = orientEquality(
                      equalityAtBranch = pointEqPattern,
                      expectedLeft = slicePoint,
                      expectedRight = pattern.freshInputTerm,
                      errorContext = s"pointwiseUniquenessAt/input/${c.name}/${pattern.name}"
                    )

                    val normalizedFacts = normalizeBranchFacts(
                      localContext = localContext,
                      pointEqInputFact = patternEqPoint,
                      leftEqualityAtInput = xAtPattern,
                      rightEqualityAtInput = yPatternToBody,
                      bodyEqualityAtInput = bodyEquality,
                      slicePoint = slicePoint,
                      inputTerm = pattern.freshInputTerm,
                      xFun = xFun,
                      yFun = yFun,
                      xBody = xBody,
                      yBody = yBody,
                      errorContext = s"pointwiseUniquenessAt/${c.name}/${pattern.name}"
                    )
                    
                    proveBranchPointwiseAgreement(
                      normalized = normalizedFacts,
                      propertyAt = propertyAt,
                      slicePoint = slicePoint,
                      xFun = xFun,
                      yFun = yFun
                    )
                  }
                }
              }
            })
        }
        thenHave(thesis) by RightForall
      }}

      val allHeights = have(∀(nVar, (nVar ∈ N) ==> P(nVar))) by
        Tautology.from(Integer.natInduction of (Pred := P), base, step)
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
            InstantiateForall(inductionVariable)(have(∀(slicePoint, (slicePoint ∈ app(heightFun)(nVar)) ==> propertyAt(slicePoint))) by
              Restate.from(sliceAgreement))
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
