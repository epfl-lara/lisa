package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.recursion.FunSpec
import lisa.maths.SetTheory.Types.ADTv2.recursion.Witness
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.SpecializedConstructorFacts
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.specializedConstructors
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeFormula
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class WitnessAgreement[N <: Arity](
    val spec: FunSpec[N],
    val recWitness: Witness[N]
) {

  val leftFun = variable[Ind]
  val rightFun = variable[Ind]
  val nVar = variable[Ind]
  private val vVar = variable[Ind]

  private def substitutedCaseBody[N <: Arity](
      pattern: Pattern[N],
      selfPlaceholder: Variable[Ind],
      selfTerm: Expr[Ind],
      vars: Seq[Variable[Ind]]
  ): Expr[Ind] =
    pattern.body
      .substitute(selfPlaceholder := selfTerm)
      .substitute(pattern.binders.zip(vars).map((from, to) => from := to)*)

  private def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    specializeFormula(spec.adt.height.predicate(hh), spec.typeSubstitutions)

  private val heightFun: Expr[Ind] = specializeTerm(spec.adt.height.function, spec.typeSubstitutions)
  private val heightFunValid: THM = spec.adt.height.validAt(spec.typeSubstitutions)
  private val heightSuccStrong = spec.adt.height.successorStrongAt(spec.typeSubstitutions)
  private val constructorsAt = specializedConstructors(spec.adt.constructors, spec.typeSubstitutions)

  private def instantiateWitnessAtPattern(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      pattern: Pattern[N],
      selfTerm: Expr[Ind],
      selfTyped: proof.Fact,
      patternPremise: proof.Fact,
      body: Expr[Ind]
  ): proof.Fact = {
    val witnessSchema = recWitness.witnessCase(pattern).of(spec.selfPlaceholder := selfTerm)
    val witnessBase = witnessSchema.statement.right.head match
      case _ ==> consequent =>
        have(consequent) by Tautology.from(witnessSchema, selfTyped)
      case _ => throw UnreachableException

    val witnessAtVars = have(
      pattern.freshBranchPremise ==> (recWitness(selfTerm) * pattern.freshInputTerm === body)
    ) by InstantiateForallSeq(pattern.variables2)(witnessBase)

    witnessAtVars.statement.right.head match
      case _ ==> consequent =>
        val premise = pattern.freshBranchPremise
        val mp = have(Set[Expr[Prop]](premise ==> consequent, premise) |- consequent) by
          LeftImplies.withParameters(premise, consequent)(
            have(premise |- premise) by Hypothesis,
            have(consequent |- consequent) by Hypothesis
          )
        val viaImpl = have((witnessAtVars.statement.left + premise) |- consequent) by
          Cut(witnessAtVars, mp)
        have((witnessAtVars.statement.left ++ patternPremise.statement.left) |- consequent) by
          Cut(patternPremise, viaImpl)
      case _ => throw UnreachableException
  }

  private val agreeOnSlice = ∀(vVar ∈ app(heightFun)(nVar), app(leftFun)(vVar) === app(rightFun)(vVar))

  private val witnessAgreementAtSucc: THM = Time.measure(s"WA/witnessAgreementAtSucc")(
    Lemma(
      (
        leftFun :: spec.typ,
        rightFun :: spec.typ,
        nVar ∈ N,
        agreeOnSlice
      ) |- ∀(a ∈ app(heightFun)(S(nVar)), app(recWitness(leftFun))(a) === app(recWitness(rightFun))(a))
    ) {
      have(thesis) subproof {
        assume(leftFun :: spec.typ)
        assume(rightFun :: spec.typ)
        val nInN = assume(nVar ∈ N)
        assume(agreeOnSlice)

        val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)

        val goalW = app(recWitness(leftFun))(a) === app(recWitness(rightFun))(a)

        // Orchestration (height decomposition + branch selection + assembly) is shared
        // with the uniqueness step via PointwiseAgreementStep; only the per-pattern
        // proof — recursive-argument agreements + witness case equations + pointwise
        // extensionality — is witness-specific and lives in the callback below.
        val agreementAtSucc = PointwiseAgreementStep.pointwiseAgreementOnSucc(
          patternMatching = spec.patternMatching,
          heightFun = heightFun,
          constructorsAt = constructorsAt,
          ambientTerm = a,
          currentIndex = nVar,
          currentIndexInN = nInN,
          hValid = hValid,
          heightSuccStrong = heightSuccStrong,
          goalEqAt = goalW
        )(new PointwiseAgreementStep.SelectedPatternProver[N] {
          def apply(using
              proof: lisa.SetTheoryLibrary.Proof
          )(
              sc: SpecializedConstructorFacts[N],
              argsTypedAtHeight: proof.Fact,
              argsTypedSemantic: proof.Fact,
              aEqApplied: proof.Fact
          ): Pattern[N] => proof.Fact = {
            // Re-establish the ambient facts the callback needs directly in this
            // (inner) proof. Capturing them from the enclosing lemma proof is not
            // possible: a fact lifts into a nested proof only where that nesting is
            // statically known, which the abstract `proof` here is not. Re-`assume`ing
            // hypotheses already in the lemma's antecedent is idempotent.
            val leftTyped = assume(leftFun :: spec.typ)
            val rightTyped = assume(rightFun :: spec.typ)
            val nInN = assume(nVar ∈ N)
            val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)
            val agreeForall = have(
              ∀(vVar, (vVar ∈ app(heightFun)(nVar)) ==> (app(leftFun)(vVar) === app(rightFun)(vVar)))
            ) by Restate.from(assume(agreeOnSlice))

            val selfArgEqualities = sc.selfRefVariables2.map(v =>
              val vInHeight = have(v ∈ app(heightFun)(nVar)) by Restate.from(argsTypedAtHeight)
              RecursiveAgreement.selfAgreementFromForall(
                heightFun = heightFun,
                currentIndex = nVar,
                leftFun = leftFun,
                rightFun = rightFun,
                agreeForall = agreeForall,
                point = v,
                pointInHeight = vInHeight
              )
            )

            (pattern: Pattern[N]) =>
              have(pattern.branchSelectionBody(a) |- goalW) subproof {
                val selectedPattern = assume(pattern.branchSelectionBody(a))
                val patternGuard = have(pattern.freshBranchCondition) by Weakening(selectedPattern)
                val aEqPattern = have(a === pattern.freshInputTerm) by Weakening(selectedPattern)
                val patternPremise = have(pattern.freshBranchPremise) by Tautology.from(argsTypedSemantic, patternGuard)
                val innerAgreements = RecursiveAgreement.selfAgreementFromForallAt2(
                  pattern = pattern,
                  recursiveType = spec.argType,
                  heightMembershipMonotonic = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions),
                  argsTypedAtHeight = argsTypedAtHeight,
                  leafTyping = patternPremise,
                  patternGuard = patternGuard,
                  heightFun = heightFun,
                  hValid = hValid,
                  currentIndex = nVar,
                  currentIndexInN = nInN,
                  leftFun = leftFun,
                  rightFun = rightFun,
                  agreeForall = agreeForall
                )

                val bodyLeft = substitutedCaseBody(pattern, spec.selfPlaceholder, leftFun, pattern.variables2)
                val bodyRight = substitutedCaseBody(pattern, spec.selfPlaceholder, rightFun, pattern.variables2)
                val bodyEq = LambdaBodyEquality.prove(bodyLeft, bodyRight, selfArgEqualities ++ innerAgreements)
                val witnessAtLeft = instantiateWitnessAtPattern(pattern, leftFun, leftTyped, patternPremise, bodyLeft)
                val witnessAtRight = instantiateWitnessAtPattern(pattern, rightFun, rightTyped, patternPremise, bodyRight)

                val witnessesAgreeAtA = have(
                  aEqPattern.statement.left |- (app(recWitness(leftFun))(a) === app(recWitness(rightFun))(a))
                  ) by Congruence.from(aEqPattern, witnessAtLeft, witnessAtRight, bodyEq)

                have(goalW) by Restate.from(witnessesAgreeAtA)
              }
          }
        })

        have(thesis) by Restate.from(agreementAtSucc)
      }
    }
  )

  /** Specializes [[witnessAgreementAtSucc]] to the ambient point `a` and chains the
    * resulting witness agreement `app(recWitness(lhs))(a) === app(recWitness(rhs))(a)`
    * through the caller-supplied `bridges` to prove the equation `goal`.
    *
    * `goal` is the endpoint equation to prove; `bridges` are the remaining equalities
    * that, together with the derived witness agreement, connect its two sides. A
    * single `Congruence` closes the chain from those equality facts, so the bridges
    * need no particular order or orientation.
    *
    * This packages both the four-step witness-agreement ritual (instantiate the
    * lemma, discharge its premises, instantiate the `∀` at `a`, discharge the height
    * membership) and the equational chaining shared by the limit step in `Existence`
    * and the successor step in `ApproxStabilization`.
    */
  def witnessesAgreeAt(using proof: lisa.SetTheoryLibrary.Proof)(
      lhs: Expr[Ind],
      rhs: Expr[Ind],
      index: Expr[Ind],
      lhsTyped: proof.Fact,
      rhsTyped: proof.Fact,
      indexInN: proof.Fact,
      sliceAgreement: proof.Fact,
      pointInHeightSucc: proof.Fact,
      goal: Expr[Prop],
      bridges: Seq[proof.Fact]
  ): proof.Fact = {
    val lemma = witnessAgreementAtSucc.of(leftFun := lhs, rightFun := rhs, nVar := index)
    val agreeOnSucc = have(lemma.statement.right.head) by Tautology.from(
      lemma,
      lhsTyped,
      rhsTyped,
      indexInN,
      sliceAgreement
    )
    val impl = have(
      (a ∈ app(heightFun)(S(index))) ==> (app(recWitness(lhs))(a) === app(recWitness(rhs))(a))
    ) by InstantiateForall(a)(agreeOnSucc)
    val witnessesAgreeAtA = have(
      app(recWitness(lhs))(a) === app(recWitness(rhs))(a)
    ) by Tautology.from(impl, pointInHeightSucc)

    have(goal) by Congruence.from((bridges :+ witnessesAgreeAtA)*)
  }
}
