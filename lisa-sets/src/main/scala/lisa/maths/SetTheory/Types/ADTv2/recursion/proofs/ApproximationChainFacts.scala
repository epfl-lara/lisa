package lisa.maths.SetTheory.Types.ADTv2.recursion.proofs

import lisa.maths.SetTheory.Types.ADTv2.recursion.{Approx, ApproxProp, FunSpec}
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.{Succ, Zero}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity, unionOfTwoNats}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Base.{Subset, Union}
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class ApproximationChainFacts[N <: Arity](
  val spec: FunSpec[N],
  val approx: Approx[N],
  val approxProp: ApproxProp[N]
) {

  val nVar = variable[Ind]
  val mVar = variable[Ind]
  val kVar = variable[Ind]
  val uVar = variable[Ind]
  import approx.G
  import approxProp.{heightFun, heightFunValid, isHeightPred, stabilization}

  private val heightMembershipMonotonic = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions)

  val approximantsAgreeFromSubset: THM = Time.measure(s"AppCF/approximantsAgreeFromSubset for ${spec.functionName}")(Lemma(
    (nVar ∈ N, mVar ∈ N, nVar ⊆ mVar, a ∈ app(heightFun)(nVar)) |-
      app(G(nVar))(a) === app(G(mVar))(a)
  ) {
    val nInN = assume(nVar ∈ N)
    val mInN = assume(mVar ∈ N)
    val nSubM = assume(nVar ⊆ mVar)
    val aInHn = assume(a ∈ app(heightFun)(nVar))

    val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)

    val propM = λ(
      uVar,
      (nVar ⊆ uVar) ==> (
        (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(uVar))(a))
      )
    )

    val base = have(propM(Zero)) subproof {
      val zeroDef = have(Zero === ∅) by Weakening(Zero.definition)
      have((nVar ⊆ Zero) ==> ((a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Zero))(a)))) subproof {
        val nSubZero = assume(nVar ⊆ Zero)
        val nSubEmpty = have(nVar ⊆ ∅) by Congruence.from(nSubZero, zeroDef)
        val nEqEmpty = have(nVar === ∅) by Tautology.from(
          nSubEmpty,
          Subset.rightEmpty of (x := nVar),
          lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.equivalenceApply of (p1 := subset(nVar, ∅), p2 := nVar === ∅)
        )
        val emptyEqZero = have(∅ === Zero) by Congruence.from(zeroDef)
        val nEqZero = have(nVar === Zero) by Tautology.from(
          altEqualityTransitivity of (x := nVar, y := ∅, z := Zero),
          nEqEmpty,
          emptyEqZero
        )
        val eqAtZero = have(app(G(nVar))(a) === app(G(Zero))(a)) by Congruence.from(nEqZero)
        have(thesis) by Tautology.from(eqAtZero)
      }
      thenHave(thesis) by Restate
    }

    val step = have(∀(uVar, (uVar ∈ N) ==> (propM(uVar) ==> propM(Succ(uVar))))) subproof {
      have((uVar ∈ N) ==> (propM(uVar) ==> propM(Succ(uVar)))) subproof {
        val uInNStep = assume(uVar ∈ N)
        val ih = assume(propM(uVar))

        val goalAtSucc = have(propM(Succ(uVar))) subproof {
          have(
            (nVar ⊆ Succ(uVar)) ==> (
              (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Succ(uVar)))(a))
            )
          ) subproof {
            val nSubSuccU = assume(nVar ⊆ Succ(uVar))
            val aInHeightN = assume(a ∈ app(heightFun)(nVar))

            val split = have((nVar === Succ(uVar)) \/ (nVar ⊆ uVar)) by Tautology.from(
              nInN,
              uInNStep,
              nSubSuccU,
              NatFacts.subsetBelowSucc.of(m := nVar, n := uVar)
            )

            val caseEq = have(
              nVar === Succ(uVar) |- app(G(nVar))(a) === app(G(Succ(uVar)))(a)
            ) by Congruence

            val caseSub = have(
              nVar ⊆ uVar |- app(G(nVar))(a) === app(G(Succ(uVar)))(a)
            ) subproof {
              val nSubUCase = assume(nVar ⊆ uVar)
              val eqNu = have(app(G(nVar))(a) === app(G(uVar))(a)) by Tautology.from(
                ih,
                nSubUCase,
                aInHeightN
              )

              val aInHu = have(a ∈ app(heightFun)(uVar)) by Tautology.from(
                hValid,
                uInNStep,
                nInN,
                nSubUCase,
                aInHeightN,
                heightMembershipMonotonic.of(h := heightFun, n := uVar, m := nVar, x := a)
              )

              val stabAtU = have(
                uVar ∈ N ==> ∀(a ∈ app(heightFun)(uVar), app(G(uVar))(a) === app(G(Succ(uVar)))(a))
              ) by InstantiateForall(uVar)(stabilization)
              val stabU = have(
                ∀(a ∈ app(heightFun)(uVar), app(G(uVar))(a) === app(G(Succ(uVar)))(a))
              ) by Tautology.from(uInNStep, stabAtU)
              val stabAtA = have(
                a ∈ app(heightFun)(uVar) ==> (app(G(uVar))(a) === app(G(Succ(uVar)))(a))
              ) by InstantiateForall(a)(stabU)
              val eqUSu = have(app(G(uVar))(a) === app(G(Succ(uVar)))(a)) by
                Tautology.from(aInHu, stabAtA)

              have(thesis) by Tautology.from(
                altEqualityTransitivity of (
                  x := app(G(nVar))(a),
                  y := app(G(uVar))(a),
                  z := app(G(Succ(uVar)))(a)
                ),
                eqNu,
                eqUSu
              )
            }

            have(app(G(nVar))(a) === app(G(Succ(uVar)))(a)) by
              Tautology.from(split, caseEq, caseSub)
            have(
              (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Succ(uVar)))(a))
            ) by Tautology.from(lastStep)
            thenHave(thesis) by Restate
          }
          thenHave(thesis) by Restate
        }

        val imp = have(propM(uVar) ==> propM(Succ(uVar))) by Tautology.from(goalAtSucc)
        have(thesis) by Tautology.from(imp)
      }
      thenHave(thesis) by RightForall
    }

    val Pred = variable[Ind >>: Prop]
    val indInst = have(
      (propM(Zero), ∀(uVar, (uVar ∈ N) ==> (propM(uVar) ==> propM(Succ(uVar))))) |-
        ∀(uVar, (uVar ∈ N) ==> propM(uVar))
    ) by Weakening(NatFacts.induction of (Pred := propM))
    val all = have(∀(uVar, (uVar ∈ N) ==> propM(uVar))) by
      Tautology.from(base, step, indInst)
    val atM = have(mVar ∈ N ==> propM(mVar)) by InstantiateForall(mVar)(all)
    val propAtM = have(propM(mVar)) by Tautology.from(mInN, atM)

    have(app(G(nVar))(a) === app(G(mVar))(a)) by Tautology.from(propAtM, nSubM, aInHn)
    thenHave(thesis) by Restate
  })

  val approximantsAgreeAcrossHeights: THM = Time.measure(s"approximantsAgreeAcrossHeights for ${spec.functionName}")(Lemma(
    (nVar ∈ N, mVar ∈ N, a ∈ app(heightFun)(nVar), a ∈ app(heightFun)(mVar)) |-
      app(G(nVar))(a) === app(G(mVar))(a)
  ) {
    val nInN = assume(nVar ∈ N)
    val mInN = assume(mVar ∈ N)
    val aInHn = assume(a ∈ app(heightFun)(nVar))
    val aInHm = assume(a ∈ app(heightFun)(mVar))

    val upperInN = have((nVar ∪ mVar) ∈ N) by Tautology.from(
      nInN,
      mInN,
      unionOfTwoNats.of(a := nVar, b := mVar)
    )

    val nSubUpper = have(nVar ⊆ (nVar ∪ mVar)) by
      Tautology.from(Union.leftSubset of (x := nVar, y := mVar))
    val mSubUpper = have(mVar ⊆ (nVar ∪ mVar)) by
      Tautology.from(Union.rightSubset of (x := nVar, y := mVar))

    val eqNUpper = have(app(G(nVar))(a) === app(G(nVar ∪ mVar))(a)) by Tautology.from(
      nInN,
      upperInN,
      nSubUpper,
      aInHn,
      approximantsAgreeFromSubset.of(nVar := nVar, mVar := nVar ∪ mVar)
    )
    val eqMUpper = have(app(G(mVar))(a) === app(G(nVar ∪ mVar))(a)) by Tautology.from(
      mInN,
      upperInN,
      mSubUpper,
      aInHm,
      approximantsAgreeFromSubset.of(nVar := mVar, mVar := nVar ∪ mVar)
    )
    val eqUpperM = have(app(G(nVar ∪ mVar))(a) === app(G(mVar))(a)) by
      Congruence.from(eqMUpper)

    have(app(G(nVar))(a) === app(G(mVar))(a)) by Tautology.from(
      altEqualityTransitivity of (
        x := app(G(nVar))(a),
        y := app(G(nVar ∪ mVar))(a),
        z := app(G(mVar))(a)
      ),
      eqNUpper,
      eqUpperM
    )
    thenHave(thesis) by Restate
  })
}
