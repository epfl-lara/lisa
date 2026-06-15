package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeFormula
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.altEqualityTransitivity
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity


/**
 * Approximant stabilization.
 *
 * Proves stabilization of the approximant sequence:
 *
 *   stabilization : ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
 *
 * Exports:
 *   - [[heightFun]], [[heightFunValid]]
 *   - [[stabilization]]
 */
private[recursion] final class ApproxProp[N <: Arity](
  val spec: FunSpec[N],
  val recWitness: Witness[N],
  val approx: Approx[N],
  val witnessAgreement: lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.WitnessAgreement[N]
) {

  val nVar = variable[Ind]
  val mVar = variable[Ind]
  val kVar = variable[Ind]
  import approx.G

  // ─────────────────────────────────────────────────────────────────────────
  // Height function — ε-chosen concrete height function
  // ─────────────────────────────────────────────────────────────────────────

  def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    specializeFormula(spec.adt.height.predicate(hh), spec.typeSubstitutions)

  val heightFun: Expr[Ind] =
    specializeTerm(spec.adt.height.function, spec.typeSubstitutions)

  val heightFunValid: THM = spec.adt.height.validAt(spec.typeSubstitutions)

  private val heightZero = spec.adt.height.zeroAt(spec.typeSubstitutions)

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma D — stabilization
  // ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
  // ─────────────────────────────────────────────────────────────────────────

  private[recursion] val stabilization: THM = Time.measure(s"AP/stabilization")(Lemma(
    ∀(nVar ∈ N, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(successor(nVar)))(a)))
  ) {
    val Pred = variable[Ind >>: Prop]("P")
    val P = λ(nVar, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(successor(nVar)))(a)))

    val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)

    val noElemAtEmpty = have(!in(a, app(heightFun)(∅))) by Cut(
      hValid,
      heightZero of (h := heightFun, x := a)
    )

    val base = Time.measure(s"AP/stab base") { have(P(∅)) subproof {
      have(a ∈ app(heightFun)(∅) |- app(G(∅))(a) === app(G(successor(∅)))(a)) by
        Tautology.from(noElemAtEmpty)
      thenHave(
        (a ∈ app(heightFun)(∅)) ==> (app(G(∅))(a) === app(G(successor(∅)))(a))
      ) by RightImplies
      thenHave(
        ∀(a, (a ∈ app(heightFun)(∅)) ==> (app(G(∅))(a) === app(G(successor(∅)))(a)))
      ) by RightForall
      thenHave(thesis) by Restate
    } }

    val step = have(∀(nVar, (nVar ∈ N) ==> (P(nVar) ==> P(successor(nVar))))) subproof {
      have((nVar ∈ N) ==> (P(nVar) ==> P(successor(nVar)))) subproof {
        val nInN = assume(nVar ∈ N)
        val ih     = assume(P(nVar))

        val pointwiseAtSucc = have(
          (a ∈ app(heightFun)(successor(nVar))) ==> (app(G(successor(nVar)))(a) === app(G(successor(successor(nVar))))(a))
        ) subproof {
          val goalAtA = app(G(successor(nVar)))(a) === app(G(successor(successor(nVar))))(a)
          val aInHeightSucc = assume(a ∈ app(heightFun)(successor(nVar)))

          val succInN = have(successor(nVar) ∈ N) by
            Tautology.from(nInN, Integer.successorInOmega.of(n := nVar))

          // Approximant typings, fed to the shared witness-agreement lemma.
          val approxTypeAtN = have(nVar ∈ N ==> (G(nVar) :: spec.typ)) by
            InstantiateForall(nVar)(approx.approxHasType)
          val gNHasType = have(G(nVar) :: spec.typ) by Tautology.from(nInN, approxTypeAtN)
          val approxTypeAtSuccN = have(successor(nVar) ∈ N ==> (G(successor(nVar)) :: spec.typ)) by
            InstantiateForall(successor(nVar))(approx.approxHasType)
          val gSuccHasType = have(G(successor(nVar)) :: spec.typ) by Tautology.from(
            succInN,
            approxTypeAtSuccN
          )

          // approxSucc glue: G(Succ n) = W(G n), G(Succ Succ n) = W(G(Succ n)).
          val approxSuccAtN = have(nVar ∈ N ==> (G(successor(nVar)) === recWitness(G(nVar)))) by
            InstantiateForall(nVar)(approx.approxSucc)
          val gSuccEq = have(G(successor(nVar)) === recWitness(G(nVar))) by
            Tautology.from(nInN, approxSuccAtN)
          val gSuccAtAIsWitness = have(app(G(successor(nVar)))(a) === app(recWitness(G(nVar)))(a)) by
            Congruence.from(gSuccEq)

          val approxSuccAtSuccN = have(
            successor(nVar) ∈ N ==> (G(successor(successor(nVar))) === recWitness(G(successor(nVar))))
          ) by InstantiateForall(successor(nVar))(approx.approxSucc)
          val gSuccSuccEq = have(G(successor(successor(nVar))) === recWitness(G(successor(nVar)))) by
            Tautology.from(succInN, approxSuccAtSuccN)
          val witnessSuccAtARev = have(
            app(recWitness(G(successor(nVar))))(a) === app(G(successor(successor(nVar))))(a)
          ) by Congruence.from(gSuccSuccEq)

          // The induction hypothesis `ih = P(n)` is exactly the slice-agreement premise of
          // WitnessAgreement.witnessAgreementAtSucc at leftFun := G(n), rightFun := G(Succ n).
          val witnessAgreeOnSucc = have(
            ∀(a ∈ app(heightFun)(successor(nVar)), app(recWitness(G(nVar)))(a) === app(recWitness(G(successor(nVar))))(a))
          ) by Tautology.from(
            witnessAgreement.witnessAgreementAtSucc.of(
              witnessAgreement.leftFun := G(nVar),
              witnessAgreement.rightFun := G(successor(nVar)),
              witnessAgreement.nVar := nVar
            ),
            gNHasType,
            gSuccHasType,
            nInN,
            ih
          )
          val witnessAgreeImpl = have(
            (a ∈ app(heightFun)(successor(nVar))) ==> (app(recWitness(G(nVar)))(a) === app(recWitness(G(successor(nVar))))(a))
          ) by InstantiateForall(a)(witnessAgreeOnSucc)
          val witnessesAgreeAtA = have(
            app(recWitness(G(nVar)))(a) === app(recWitness(G(successor(nVar))))(a)
          ) by Tautology.from(witnessAgreeImpl, aInHeightSucc)

          have(goalAtA) by Tautology.from(
            altEqualityTransitivity of (
              x := app(G(successor(nVar)))(a),
              y := app(recWitness(G(nVar)))(a),
              z := app(G(successor(successor(nVar))))(a)
            ),
            altEqualityTransitivity of (
              x := app(recWitness(G(nVar)))(a),
              y := app(recWitness(G(successor(nVar))))(a),
              z := app(G(successor(successor(nVar))))(a)
            ),
            gSuccAtAIsWitness,
            witnessesAgreeAtA,
            witnessSuccAtARev
          )
        }
        have(
          a ∈ app(heightFun)(successor(nVar)) ==> (app(G(successor(nVar)))(a) === app(G(successor(successor(nVar))))(a))
        ) by Restate.from(pointwiseAtSucc)
        thenHave(
          ∀(a ∈ app(heightFun)(successor(nVar)), app(G(successor(nVar)))(a) === app(G(successor(successor(nVar))))(a))
        ) by RightForall
      }
      thenHave(thesis) by RightForall
    }

    have(∀(nVar, (nVar ∈ N) ==> P(nVar))) by
      Tautology.from(Integer.omegaSuccessorInduction of (Pred := P), base, step)
    thenHave(thesis) by Restate
  })

}
