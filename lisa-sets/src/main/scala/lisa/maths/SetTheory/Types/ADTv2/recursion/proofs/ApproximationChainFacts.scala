package lisa.maths.SetTheory.Types.ADTv2.recursion.proofs

import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Succ
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Zero
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts.altEqualityTransitivity
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.unionOfTwoNats
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.BasicStepTactic.RightImplies

private[recursion] object ApproximationChainFacts {

  private val heightFun = variable[Ind]
  private val G = variable[Ind >>: Ind]

  private val nVar = variable[Ind]
  private val mVar = variable[Ind]
  private val uVar = variable[Ind]
  private val aVar = variable[Ind]
  private val upperVar = variable[Ind]
  private val lowerVar = variable[Ind]
  private val pointVar = variable[Ind]
  private val stabVar = variable[Ind]

  private def stabilizationSchema(heightFun0: Expr[Ind], G0: Expr[Ind >>: Ind]): Expr[Prop] =
    ∀(stabVar, (stabVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun0)(stabVar)) ==> (app(G0(stabVar))(pointVar) === app(G0(Succ(stabVar)))(pointVar))))

  private def heightMembershipMonotonicSchema(heightFun0: Expr[Ind]): Expr[Prop] =
    ∀(upperVar, (upperVar ∈ N) ==> ∀(lowerVar, (lowerVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun0)(lowerVar)) ==> ((lowerVar ⊆ upperVar) ==> (pointVar ∈ app(heightFun0)(upperVar))))))

  val approximantsAgreeFromSubset: THM = Time.measure(s"AppCF/approximantsAgreeFromSubset")(Lemma(
    (
      stabilizationSchema(heightFun, G),
      heightMembershipMonotonicSchema(heightFun),
      nVar ∈ N,
      mVar ∈ N,
      nVar ⊆ mVar,
      a ∈ app(heightFun)(nVar)
    ) |- app(G(nVar))(a) === app(G(mVar))(a)
  ) {
    val stabilization = assume(stabilizationSchema(heightFun, G))
    val heightMonotonic = assume(heightMembershipMonotonicSchema(heightFun))
    val nInN = assume(nVar ∈ N)
    val mInN = assume(mVar ∈ N)
    val nSubM = assume(nVar ⊆ mVar)
    val aInHn = assume(a ∈ app(heightFun)(nVar))

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

              val heightMonoAtUpper = have(
                (uVar ∈ N) ==> ∀(lowerVar, (lowerVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun)(lowerVar)) ==> ((lowerVar ⊆ uVar) ==> (pointVar ∈ app(heightFun)(uVar)))))
              ) by InstantiateForall(uVar)(heightMonotonic)
              val heightMonoUpper = have(
                ∀(lowerVar, (lowerVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun)(lowerVar)) ==> ((lowerVar ⊆ uVar) ==> (pointVar ∈ app(heightFun)(uVar)))))
              ) by Tautology.from(uInNStep, heightMonoAtUpper)
              val heightMonoAtNInst = have(
                (nVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun)(nVar)) ==> ((nVar ⊆ uVar) ==> (pointVar ∈ app(heightFun)(uVar))))
              ) by InstantiateForall(nVar)(heightMonoUpper)
              val heightMonoAtLower = have(
                (nVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun)(nVar)) ==> ((nVar ⊆ uVar) ==> (pointVar ∈ app(heightFun)(uVar))))
              ) by Restate.from(heightMonoAtNInst)
              val heightMonoAtN = have(
                (nVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun)(nVar)) ==> ((nVar ⊆ uVar) ==> (pointVar ∈ app(heightFun)(uVar))))
              ) by Restate.from(heightMonoAtLower)
              val heightMonoAtPoint = have(
                ∀(pointVar, (pointVar ∈ app(heightFun)(nVar)) ==> ((nVar ⊆ uVar) ==> (pointVar ∈ app(heightFun)(uVar))))
              ) by Tautology.from(nInN, heightMonoAtN)
              val heightMonoAtA = have(
                (a ∈ app(heightFun)(nVar)) ==> ((nVar ⊆ uVar) ==> (a ∈ app(heightFun)(uVar)))
              ) by InstantiateForall(a)(heightMonoAtPoint)

              val aInHu = have(a ∈ app(heightFun)(uVar)) by Tautology.from(
                aInHeightN,
                nSubUCase,
                heightMonoAtA
              )

              val stabAtU = have(
                (uVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun)(uVar)) ==> (app(G(uVar))(pointVar) === app(G(Succ(uVar)))(pointVar)))
              ) by InstantiateForall(uVar)(stabilization)
              val stabU = have(
                ∀(pointVar, (pointVar ∈ app(heightFun)(uVar)) ==> (app(G(uVar))(pointVar) === app(G(Succ(uVar)))(pointVar)))
              ) by Tautology.from(uInNStep, stabAtU)
              val stabAtA = have(
                (a ∈ app(heightFun)(uVar)) ==> (app(G(uVar))(a) === app(G(Succ(uVar)))(a))
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

  val approximantsAgreeAcrossHeights: THM = Time.measure(s"AppCF/approximantsAgreeAcrossHeights")(Lemma(
    (
      stabilizationSchema(heightFun, G),
      heightMembershipMonotonicSchema(heightFun),
      nVar ∈ N,
      mVar ∈ N,
      a ∈ app(heightFun)(nVar),
      a ∈ app(heightFun)(mVar)
    ) |- app(G(nVar))(a) === app(G(mVar))(a)
  ) {
    val stabilization = assume(stabilizationSchema(heightFun, G))
    val heightMonotonic = assume(heightMembershipMonotonicSchema(heightFun))
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
      stabilization,
      heightMonotonic,
      nInN,
      upperInN,
      nSubUpper,
      aInHn,
      approximantsAgreeFromSubset.of(nVar := nVar, mVar := nVar ∪ mVar)
    )
    val eqMUpper = have(app(G(mVar))(a) === app(G(nVar ∪ mVar))(a)) by Tautology.from(
      stabilization,
      heightMonotonic,
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

  def stabilizationSchemaAt(
      heightFun0: Expr[Ind],
      G0: Expr[Ind >>: Ind],
      stabilization0: THM
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    have(stabilizationSchema(heightFun0, G0)) by Restate.from(stabilization0)

  def heightMembershipMonotonicSchemaAt(
      heightFun0: Expr[Ind],
      heightMembershipMonotonic0: THM
  )(using proof: lisa.SetTheoryLibrary.Proof)(isHeightPredFact: proof.Fact): proof.Fact = {
    val monoAtVars = have(
      (upperVar ∈ N, lowerVar ∈ N, lowerVar ⊆ upperVar, pointVar ∈ app(heightFun0)(lowerVar)) |- pointVar ∈ app(heightFun0)(upperVar)
    ) by Tautology.from(
      isHeightPredFact,
      heightMembershipMonotonic0.of(h := heightFun0, n := upperVar, m := lowerVar, x := pointVar)
    )

    val monoImp = have(
      (upperVar ∈ N, lowerVar ∈ N, pointVar ∈ app(heightFun0)(lowerVar)) |- (lowerVar ⊆ upperVar) ==> (pointVar ∈ app(heightFun0)(upperVar))
    ) by RightImplies(monoAtVars)

    val monoPointImp = have(
      (upperVar ∈ N, lowerVar ∈ N) |- (pointVar ∈ app(heightFun0)(lowerVar)) ==> ((lowerVar ⊆ upperVar) ==> (pointVar ∈ app(heightFun0)(upperVar)))
    ) by RightImplies(monoImp)

    val monoForallA = have(
      (upperVar ∈ N, lowerVar ∈ N) |- ∀(pointVar, (pointVar ∈ app(heightFun0)(lowerVar)) ==> ((lowerVar ⊆ upperVar) ==> (pointVar ∈ app(heightFun0)(upperVar))))
    ) by RightForall(monoPointImp)

    val monoImpM = have(
      (upperVar ∈ N) |- (lowerVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun0)(lowerVar)) ==> ((lowerVar ⊆ upperVar) ==> (pointVar ∈ app(heightFun0)(upperVar))))
    ) by RightImplies(monoForallA)

    val monoForallM = have(
      (upperVar ∈ N) |- ∀(lowerVar, (lowerVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun0)(lowerVar)) ==> ((lowerVar ⊆ upperVar) ==> (pointVar ∈ app(heightFun0)(upperVar)))))
    ) by RightForall(monoImpM)

    val monoImpU = have(
      (upperVar ∈ N) ==> ∀(lowerVar, (lowerVar ∈ N) ==> ∀(pointVar, (pointVar ∈ app(heightFun0)(lowerVar)) ==> ((lowerVar ⊆ upperVar) ==> (pointVar ∈ app(heightFun0)(upperVar)))))
    ) by RightImplies(monoForallM)

    have(heightMembershipMonotonicSchema(heightFun0)) by RightForall(monoImpU)
  }

  def approximantsAgreeFromSubsetAt(
      heightFun0: Expr[Ind],
      G0: Expr[Ind >>: Ind],
      n0: Expr[Ind],
      m0: Expr[Ind],
      point0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof)(
      stabilization0: proof.Fact,
      heightMembershipMonotonic0: proof.Fact
  ): proof.Fact =
    have(
      (n0 ∈ N, m0 ∈ N, n0 ⊆ m0, point0 ∈ app(heightFun0)(n0)) |- app(G0(n0))(point0) === app(G0(m0))(point0)
    ) by Tautology.from(
      stabilization0,
      heightMembershipMonotonic0,
      approximantsAgreeFromSubset.of(heightFun := heightFun0, G := G0, nVar := n0, mVar := m0, a := point0)
    )

  def approximantsAgreeAcrossHeightsAt(
      heightFun0: Expr[Ind],
      G0: Expr[Ind >>: Ind],
      n0: Expr[Ind],
      m0: Expr[Ind],
      point0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof)(
      stabilization0: proof.Fact,
      heightMembershipMonotonic0: proof.Fact
  ): proof.Fact =
    have(
      (n0 ∈ N, m0 ∈ N, point0 ∈ app(heightFun0)(n0), point0 ∈ app(heightFun0)(m0)) |- app(G0(n0))(point0) === app(G0(m0))(point0)
    ) by Tautology.from(
      stabilization0,
      heightMembershipMonotonic0,
      approximantsAgreeAcrossHeights.of(heightFun := heightFun0, G := G0, nVar := n0, mVar := m0, a := point0)
    )

  def initialize(): Unit = {
    val _ = approximantsAgreeFromSubset
    val _ = approximantsAgreeAcrossHeights
  }
}
