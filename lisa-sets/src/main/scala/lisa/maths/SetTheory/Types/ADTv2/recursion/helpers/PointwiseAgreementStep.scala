package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.SpecializedConstructorFacts
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.constructorDisjunctionAtHeight
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.LeftOr
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Shared structural core of a "pointwise agreement at the successor height"
 * proof — the step shape common to [[WitnessAgreement.witnessAgreementAtSucc]]
 * and the inductive step of `RecFunctionInduction.pointwiseUniquenessAt`.
 *
 * It performs the height decomposition, per-constructor branch selection,
 * existential unbinding and case assembly that prove
 *
 *   ∀ a ∈ h(Succ currentIndex), goalEqAt
 *
 * delegating the genuinely function-specific part — proving `goalEqAt` from a
 * single selected pattern body (recursive-argument agreements + case equations
 * + extensionality) — to [[SelectedPatternProver]].
 */
private[recursion] object PointwiseAgreementStep {

  /**
   * Per-constructor pattern prover. `apply` is itself `(using proof)` so that,
   * when the orchestration invokes it inside a constructor's subproof, its
   * `proof` binds to that subproof's inner proof — the facts it receives and
   * returns then live in the same proof. Facts captured from an enclosing proof
   * (e.g. the slice-agreement hypothesis) lift in automatically as outside facts.
   *
   * Given the per-constructor facts (args typed at height `h(n)`, args typed
   * semantically, and `a = c(args)`), it returns a prover that, for each pattern
   * of that constructor, proves `pattern.branchSelectionBody(a) ⊢ goalEqAt`.
   */
  trait SelectedPatternProver[N <: Arity] {
    def apply(using proof: lisa.SetTheoryLibrary.Proof)(
        sc: SpecializedConstructorFacts[N],
        argsTypedAtHeight: proof.Fact,
        argsTypedSemantic: proof.Fact,
        aEqApplied: proof.Fact
    ): Pattern[N] => proof.Fact
  }

  def pointwiseAgreementOnSucc[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      patternMatching: PatternSystem[N],
      heightFun: Expr[Ind],
      constructorsAt: Seq[SpecializedConstructorFacts[N]],
      ambientTerm: Variable[Ind],
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact,
      hValid: proof.Fact,
      heightSuccStrong: THM,
      goalEqAt: Expr[Prop]
  )(
      proveSelectedPattern: SelectedPatternProver[N]
  ): proof.Fact = {
    val pointwiseAtSucc =
      have((ambientTerm ∈ app(heightFun)(successor(currentIndex))) ==> goalEqAt) subproof {
        val aInHeightOrd = assume(ambientTerm ∈ app(heightFun)(successor(currentIndex)))

        val constructorDisjunction =
          constructorDisjunctionAtHeight(constructorsAt, app(heightFun)(currentIndex), ambientTerm)

        val decomposeAtA = have(constructorDisjunction) by Tautology.from(
          hValid,
          currentIndexInN,
          aInHeightOrd,
          heightSuccStrong of (h := heightFun, n := currentIndex, x := ambientTerm)
        )

        val branchEqualities = constructorsAt.map { sc =>
          val c = sc.underlying
          val constructorPatterns = patternMatching.patternsFor(c)
          val branchPremise = sc.branchPremiseAtHeight(app(heightFun)(currentIndex), ambientTerm)

          val directBranch = have(branchPremise |- goalEqAt) subproof {
            assume(branchPremise)

            val argsTypedAtHeight = have(sc.heightTypingFormula(app(heightFun)(currentIndex))) by Restate
            val argsTypedSemantic = have(wellTypedFormula(sc.semanticSignature2)) by
              Tautology.from(hValid, currentIndexInN, sc.semanticTypingFromHeight(heightFun, currentIndex))
            val aEqApplied = have(ambientTerm === sc.appliedTerm2) by
              Tautology.from(hValid, currentIndexInN, sc.appliedEqualityFromStructural(heightFun, currentIndex, ambientTerm))

            val rawEqFor = proveSelectedPattern(sc, argsTypedAtHeight, argsTypedSemantic, aEqApplied)

            val selectionSchema = patternMatching.branchSelectionFor(c, ambientTerm)
            val selectionSchemaInContext = have(selectionSchema.statement.right.head) by
              Weakening(selectionSchema)
            val selectionAtCtorVars = have(
              (wellTypedFormula(sc.semanticSignature2) /\ (ambientTerm === sc.appliedTerm2)) |-
                seqOr(constructorPatterns.map(pattern => pattern.branchSelectionDisjunct(ambientTerm)))
            ) by InstantiateForallSeq(c.variables2)(selectionSchemaInContext)
            val selectedBranch = have(
              seqOr(constructorPatterns.map(pattern => pattern.branchSelectionDisjunct(ambientTerm)))
            ) by Tautology.from(selectionAtCtorVars, argsTypedSemantic, aEqApplied)

            val patternEqualities = constructorPatterns.map { pattern =>
              val rawEq = rawEqFor(pattern)
              pattern.variables2.drop(pattern.arity).reverse.foldLeft(
                (pattern.branchSelectionBody(ambientTerm), rawEq)
              ) { case ((body, _), v) =>
                val quantified = ∃(v, body)
                (quantified, thenHave(quantified |- goalEqAt) by LeftExists)
              }._2
            }

            val branchesToGoal =
              if patternEqualities.size == 1 then
                have(selectedBranch.statement.right.head |- goalEqAt) by Restate.from(patternEqualities.head)
              else
                have(selectedBranch.statement.right.head |- goalEqAt) by LeftOr(patternEqualities*)

            have(goalEqAt) by Cut(selectedBranch, branchesToGoal)
          }

          ConstructorCaseAssembly.liftConstructorCase(
            sc = sc,
            heightSet = app(heightFun)(currentIndex),
            ambientTerm = ambientTerm,
            branchPremise = branchPremise,
            goal = goalEqAt,
            directBranch = directBranch
          )
        }

        ConstructorCaseAssembly.assemblePointwiseFromConstructors(
          constructorDisjunction = constructorDisjunction,
          decomposeFact = decomposeAtA,
          constructorFacts = branchEqualities,
          antecedent = ambientTerm ∈ app(heightFun)(successor(currentIndex)),
          goal = goalEqAt
        )
      }

    have((ambientTerm ∈ app(heightFun)(successor(currentIndex))) ==> goalEqAt) by Restate.from(pointwiseAtSucc)
    thenHave(∀(ambientTerm ∈ app(heightFun)(successor(currentIndex)), goalEqAt)) by RightForall
  }
}
