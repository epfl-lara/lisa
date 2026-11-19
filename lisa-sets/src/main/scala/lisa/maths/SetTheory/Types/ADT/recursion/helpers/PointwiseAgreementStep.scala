package lisa.maths.SetTheory.Types.ADT.recursion.helpers

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.recursion.proofs.ConstructorSemanticFacts.SpecializedConstructorFacts
import lisa.maths.SetTheory.Types.ADT.recursion.proofs.ConstructorSemanticFacts.constructorBranchAtHeight
import lisa.maths.SetTheory.Types.ADT.recursion.proofs.ConstructorSemanticFacts.constructorDisjunctionAtHeight
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.tactics.Cuts
import lisa.utils.prooflib.InstantiateForallSeq

/**
 * Shared structural core of a "pointwise agreement at the S height"
 * proof — the step shape common to [[WitnessAgreement.witnessAgreementAtSucc]]
 * and the inductive step of `RecFunctionInduction.pointwiseUniquenessAt`.
 *
 * It performs the height decomposition, per-constructor branch selection,
 * existential unbinding and case assembly that prove
 *
 *   ∀ a ∈ h(Succ currentIndex), goalEqAt
 *
 * and, for each selected pattern, the full per-pattern agreement proof:
 * recursive-argument agreements (direct and nested), body equality, and the
 * closing congruence. The only genuinely function-specific input — how to
 * obtain, for one side, the case body and the `goalFun * input === body`
 * equation — is delegated to [[PatternCaseEquations]].
 */
private[recursion] object PointwiseAgreementStep {

  /**
   * Function-specific per-pattern ingredients consumed by [[pointwiseAgreementOnSucc]].
   *
   * Every method that builds proof facts is `(using proof)` so that, when the
   * orchestration invokes it inside a constructor's / pattern's subproof, its `proof`
   * binds to that subproof's inner proof. Facts are therefore re-derived there (the
   * implementations `assume` the ambient hypotheses, which is idempotent) rather than
   * captured from an enclosing proof, which cannot lift into the abstract `proof`.
   *
   *   - `sliceLeft`/`sliceRight` — the functions the slice-agreement hypothesis relates
   *     (recursion threads through these); the case bodies substitute them.
   *   - `recursiveType` — locates and types the nested recursive agreement points.
   *   - `sliceAgreement` — the `∀(v ∈ h(currentIndex), sliceLeft(v) === sliceRight(v))` hypothesis.
   *   - `bodyEqAssumptions` — the assumption set under which body equality is proved
   *     (kept atomic to control proof cost).
   *   - `caseEquation` — for one side, the case body (with `slice` substituted) and the
   *     equation `goalFun * input === body`, where `goalFun` is determined by the side.
   */
  trait PatternCaseEquations {
    def recursiveType: Expr[Ind]
    def sliceLeft: Expr[Ind]
    def sliceRight: Expr[Ind]
    def sliceAgreement(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact
    def bodyEqAssumptions(using
        proof: lisa.SetTheoryLibrary.Proof
    )(
        pattern: Clause[Expr[Ind]],
        patternGuard: proof.Fact
    ): Set[Expr[Prop]]
    def caseEquation(using
        proof: lisa.SetTheoryLibrary.Proof
    )(
        pattern: Clause[Expr[Ind]],
        slice: Expr[Ind],
        patternPremise: proof.Fact,
        patternGuard: proof.Fact,
        bodyEqAssumptions: Set[Expr[Prop]]
    ): (Expr[Ind], proof.Fact)
  }

  private def agreementAt(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      heightFun: Expr[Ind],
      currentIndex: Expr[Ind],
      leftFun: Expr[Ind],
      rightFun: Expr[Ind],
      agreeForall: proof.Fact,
      point: Expr[Ind],
      pointInHeight: proof.Fact
  ): proof.Fact = {
    val pIn: Expr[Prop] = point ∈ app(heightFun)(currentIndex)
    val pEq: Expr[Prop] = app(leftFun)(point) === app(rightFun)(point)
    val atPoint = have(pIn ==> pEq) by InstantiateForall(point)(agreeForall)

    val viaImpl = have((atPoint.statement.left + pIn) |- pEq) by Weakening(atPoint)
    have((atPoint.statement.left ++ pointInHeight.statement.left) |- pEq) by Cut(pointInHeight, viaImpl)
  }

  def pointwiseAgreementOnSucc(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      patternMatching: PatternSystem[Expr[Ind]],
      heightFun: Expr[Ind],
      constructorsAt: Seq[SpecializedConstructorFacts],
      ambientTerm: Variable[Ind],
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact,
      hValid: proof.Fact,
      heightSuccStrong: proof.Fact,
      goalEqAt: Expr[Prop]
  )(
      caseEqs: PatternCaseEquations
  ): proof.Fact = {
    val pointwiseAtSucc =
      have((ambientTerm ∈ app(heightFun)(S(currentIndex))) ==> goalEqAt) subproof {
        val aInHeightOrd = assume(ambientTerm ∈ app(heightFun)(S(currentIndex)))

        val constructorDisjunction =
          constructorDisjunctionAtHeight(constructorsAt, app(heightFun)(currentIndex), ambientTerm)

        // `heightSuccStrong` instantiated at the point gives the membership/constructor
        // biconditional; discharge its two side conditions by Cut, then rewrite the
        // height-membership hypothesis through it to land on the constructor disjunction.
        val heightSuccIff = have(
          (ambientTerm ∈ app(heightFun)(S(currentIndex))) <=> constructorDisjunction
        ) by Cuts(heightSuccStrong)(
          hValid,
          currentIndexInN
        )
        val decomposeAtA = have(constructorDisjunction) by Substitute(heightSuccIff)(aInHeightOrd)

        val branchEqualities = constructorsAt.map { sc =>
          val c = sc.underlying
          val constructorPatterns = patternMatching.clausesFor(c)
          val branchPremise = sc.branchPremiseAtHeight(app(heightFun)(currentIndex), ambientTerm)

          val directBranch = have(branchPremise |- goalEqAt) subproof {
            assume(branchPremise)

            val argsTypedAtHeight = have(sc.heightTypingFormula(app(heightFun)(currentIndex))) by Restate
            val argsTypedSemantic = have(wellTypedFormula(sc.semanticSignature2)) by
              Cuts(sc.semanticTypingFromHeight(heightFun, currentIndex))(hValid, currentIndexInN, argsTypedAtHeight)
            val aEqApplied = have(ambientTerm === sc.appliedTerm2) by
              Cuts(sc.appliedEqualityFromStructural(heightFun, currentIndex, ambientTerm))(hValid, currentIndexInN)

            // Agreements at the constructor's direct self-referential arguments, derived
            // from the slice-agreement hypothesis; reused inside every pattern subproof.
            val sliceAgreement = caseEqs.sliceAgreement
            val selfArgEqualities = sc.selfRefVariables2.map(v =>
              val vInHeight = have(v ∈ app(heightFun)(currentIndex)) by Weakening(argsTypedAtHeight)
              agreementAt(heightFun, currentIndex, caseEqs.sliceLeft, caseEqs.sliceRight, sliceAgreement, v, vInHeight)
            )

            // The per-pattern agreement proof, shared between the witness and uniqueness
            // steps; only `caseEqs.caseEquation` (how `goalFun * input === body` is obtained
            // for each side) is function-specific.
            val rawEqFor = (pattern: Clause[Expr[Ind]]) =>
              have(pattern.branchSelectionBody(ambientTerm) |- goalEqAt) subproof {
                val selectedPattern = assume(pattern.branchSelectionBody(ambientTerm))
                val patternGuard = have(pattern.freshBranchCondition) by Weakening(selectedPattern)
                val inputEq = have(ambientTerm === pattern.freshInputTerm) by Weakening(selectedPattern)
                have(pattern.freshTypingFormula) by Tautology.from(argsTypedSemantic)
                val patternPremiseConj = have(pattern.freshTypingFormula /\ pattern.freshBranchCondition) by
                  RightAnd(lastStep, patternGuard)
                val patternPremise = have(pattern.freshBranchPremise) by Weakening(patternPremiseConj)

                val innerAgreements = pattern.recursiveAgreementPoints(caseEqs.recursiveType).map { point =>
                  val pointInHeight = pattern.pattern.recursiveAgreementPointInHeight(
                    target = point,
                    recursiveType = caseEqs.recursiveType,
                    heightFun = heightFun,
                    hValid = hValid,
                    currentIndex = currentIndex,
                    currentIndexInN = currentIndexInN,
                    argsTypedAtHeight = argsTypedAtHeight,
                    leafTyping = patternPremise,
                    patternGuard = patternGuard
                  )
                  agreementAt(heightFun, currentIndex, caseEqs.sliceLeft, caseEqs.sliceRight, sliceAgreement, point, pointInHeight)
                }

                val bodyEqAssumptions = caseEqs.bodyEqAssumptions(pattern, patternGuard)
                val (leftBody, leftEq) = caseEqs.caseEquation(pattern, caseEqs.sliceLeft, patternPremise, patternGuard, bodyEqAssumptions)
                val (rightBody, rightEq) = caseEqs.caseEquation(pattern, caseEqs.sliceRight, patternPremise, patternGuard, bodyEqAssumptions)
                val bodyEq = LambdaBodyEquality.prove(bodyEqAssumptions, leftBody, rightBody, selfArgEqualities ++ innerAgreements)
                val agreement = have((bodyEqAssumptions + pattern.branchSelectionBody(ambientTerm)) |- goalEqAt) by
                  Congruence.from(inputEq, leftEq, rightEq, bodyEq)
                have(thesis) by Restate.from(agreement)
              }

            val selectionSchema = patternMatching.branchSelectionFor(c, ambientTerm)
            val selectionSchemaInContext = have(selectionSchema.statement.right.head) by
              Weakening(selectionSchema)
            val selectionAtCtorVars = have(
              (wellTypedFormula(sc.semanticSignature2) /\ (ambientTerm === sc.appliedTerm2)) |-
                seqOr(constructorPatterns.map(pattern => pattern.branchSelectionDisjunct(ambientTerm)))
            ) by InstantiateForallSeq(sc.variables2)(selectionSchemaInContext)
            val selectionConjunction = have(
              wellTypedFormula(sc.semanticSignature2) /\ (ambientTerm === sc.appliedTerm2)
            ) by RightAnd(argsTypedSemantic, aEqApplied)
            val selectedBranch = have(
              seqOr(constructorPatterns.map(pattern => pattern.branchSelectionDisjunct(ambientTerm)))
            ) by Cut(selectionConjunction, selectionAtCtorVars)

            val patternEqualities = constructorPatterns.map { pattern =>
              val rawEq = rawEqFor(pattern)
              pattern.variables2
                .drop(pattern.arity)
                .reverse
                .foldLeft(
                  (pattern.branchSelectionBody(ambientTerm), rawEq)
                ) { case ((body, _), v) =>
                  val quantified = ∃(v, body)
                  (quantified, thenHave(quantified |- goalEqAt) by LeftExists)
                }
                ._2
            }

            val branchesToGoal =
              have(selectedBranch.statement.right.head |- goalEqAt) by Tautology.from(patternEqualities*)

            have(goalEqAt) by Cut(selectedBranch, branchesToGoal)
          }

          val rawBranch = sc.variables2.reverse.foldLeft(directBranch -> branchPremise) { case ((fact, premise), v) =>
            val wrappedPremise = ∃(v, premise)
            val lifted = have(fact.statement -<? premise +<? wrappedPremise) by
              LeftExists.withParameters(premise, v)(fact)
            (lifted, wrappedPremise)
          }

          have(constructorBranchAtHeight(sc, app(heightFun)(currentIndex), ambientTerm) |- goalEqAt) by Restate.from(rawBranch._1)
        }

        val branchesToGoal =
          have(constructorDisjunction |- goalEqAt) by Tautology.from(branchEqualities*)

        have(goalEqAt) by Cut(decomposeAtA, branchesToGoal)
        thenHave(ambientTerm ∈ app(heightFun)(S(currentIndex)) ==> goalEqAt) by
          RightImplies.withParameters(ambientTerm ∈ app(heightFun)(S(currentIndex)), goalEqAt)
      }

    have((ambientTerm ∈ app(heightFun)(S(currentIndex))) ==> goalEqAt) by Restate.from(pointwiseAtSucc)
    thenHave(∀(ambientTerm ∈ app(heightFun)(S(currentIndex)), goalEqAt)) by RightForall
  }
}
