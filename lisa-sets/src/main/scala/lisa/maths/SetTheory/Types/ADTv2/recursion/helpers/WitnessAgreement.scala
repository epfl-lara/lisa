package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.recursion.FunSpec
import lisa.maths.SetTheory.Types.ADTv2.recursion.Witness
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.specializedConstructors
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeFormula
import lisa.utils.debug.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class WitnessAgreement[N <: Arity](
    val spec: FunSpec[N],
    val recWitness: Witness[N]
) {

  private val leftFun = variable[Ind]
  private val rightFun = variable[Ind]
  private val nVar = variable[Ind]
  private val vVar = variable[Ind]

  private def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    specializeFormula(spec.adt.height.predicate(hh), spec.typeSubstitutions)

  private val heightFun: Expr[Ind] = spec.heightFun
  private val heightFunValid: THM = spec.heightFunValid
  private val heightSuccStrong = spec.adt.height.successorStrongAt(spec.typeSubstitutions)
  private val constructorsAt = specializedConstructors(spec.adt.constructors, spec.typeSubstitutions)

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

        // Orchestration (height decomposition + branch selection + per-pattern assembly)
        // is shared with the uniqueness step via PointwiseAgreementStep; only the
        // witness-specific case equation `recWitness(slice) * input === body` is supplied
        // here, via the [[PatternCaseEquations]] callback below.
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
        )(new PointwiseAgreementStep.PatternCaseEquations[N] {
          val recursiveType: Expr[Ind] = spec.argType
          val heightMembershipMonotonic: THM = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions)
          val sliceLeft: Expr[Ind] = leftFun
          val sliceRight: Expr[Ind] = rightFun

          // Each method re-`assume`s the ambient hypotheses (idempotent) since it runs in a
          // nested proof, not the enclosing lemma proof.
          def sliceAgreement(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
            have(
              ∀(vVar, (vVar ∈ app(heightFun)(nVar)) ==> (app(leftFun)(vVar) === app(rightFun)(vVar)))
            ) by Restate.from(assume(agreeOnSlice))

          // Witness case equations carry their own contexts, so body equality needs no extra
          // ambient assumptions.
          def bodyEqAssumptions(using proof: lisa.SetTheoryLibrary.Proof)(
              pattern: Pattern[N],
              patternGuard: proof.Fact
          ): Set[Expr[Prop]] = Set.empty

          def caseEquation(using proof: lisa.SetTheoryLibrary.Proof)(
              pattern: Pattern[N],
              slice: Expr[Ind],
              patternPremise: proof.Fact,
              patternGuard: proof.Fact,
              bodyEqAssumptions: Set[Expr[Prop]]
          ): (Expr[Ind], proof.Fact) = {
            val selfTyped = assume(slice :: spec.typ)
            val body = pattern.body
              .substitute(spec.selfPlaceholder := slice)
              .substitute(pattern.binders.zip(pattern.variables2).map((from, to) => from := to)*)

            val witnessSchema = recWitness.witnessCase(pattern).of(spec.selfPlaceholder := slice)
            val witnessBase = witnessSchema.statement.right.head match
              case _ ==> consequent =>
                have(consequent) by Tautology.from(witnessSchema, selfTyped)
              case _ => throw UnreachableException

            val witnessAtVars = have(
              pattern.freshBranchPremise ==> (recWitness(slice) * pattern.freshInputTerm === body)
            ) by InstantiateForallSeq(pattern.variables2)(witnessBase)

            val instantiateWitness = witnessAtVars.statement.right.head match
              case _ ==> consequent =>
                val premise = pattern.freshBranchPremise
                val viaImpl = have((witnessAtVars.statement.left + premise) |- consequent) by
                  Weakening(witnessAtVars)
                have((witnessAtVars.statement.left ++ patternPremise.statement.left) |- consequent) by
                  Cut(patternPremise, viaImpl)
              case _ => throw UnreachableException
            (body, instantiateWitness)
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
