package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.specializedConstructors
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeFormula
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Succ
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Zero
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

  private val heightZero       = spec.adt.height.zeroAt(spec.typeSubstitutions)
  private val heightSuccStrong = spec.adt.height.successorStrongAt(spec.typeSubstitutions)
  private val heightMembershipMonotonic = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions)
  private val constructorsAt = specializedConstructors(spec.adt.constructors, spec.typeSubstitutions)

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma D — stabilization
  // ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
  // ─────────────────────────────────────────────────────────────────────────

  private[recursion] val stabilization: THM = Time.measure(s"AP/stabilization")(Lemma(
    ∀(nVar ∈ N, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(Succ(nVar)))(a)))
  ) {
    val Pred = variable[Ind >>: Prop]
    val P = λ(nVar, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(Succ(nVar)))(a)))

    val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)

    val zeroDef = have(Zero === ∅) by Restate.from(Zero.definition)
    val noElemAtEmpty = have(!in(a, app(heightFun)(∅))) by Cut(
      hValid,
      heightZero of (h := heightFun, x := a)
    )
    val noElemAtZero = have(!in(a, app(heightFun)(Zero))) by Congruence.from(noElemAtEmpty, zeroDef)

    val base = Time.measure(s"AP/stab base") { have(P(Zero)) subproof {
      have(a ∈ app(heightFun)(Zero) |- app(G(Zero))(a) === app(G(Succ(Zero)))(a)) by
        Tautology.from(noElemAtZero)
      thenHave(
        (a ∈ app(heightFun)(Zero)) ==> (app(G(Zero))(a) === app(G(Succ(Zero)))(a))
      ) by RightImplies
      thenHave(
        ∀(a, (a ∈ app(heightFun)(Zero)) ==> (app(G(Zero))(a) === app(G(Succ(Zero)))(a)))
      ) by RightForall
      thenHave(thesis) by Restate
    } }

    val step = have(∀(nVar, (nVar ∈ N) ==> (P(nVar) ==> P(Succ(nVar))))) subproof {
      have((nVar ∈ N) ==> (P(nVar) ==> P(Succ(nVar)))) subproof {
        val nInN = assume(nVar ∈ N)
        val ih     = assume(P(nVar))

        val succEq = have(Succ(nVar) === successor(nVar)) by
          Tautology.from(Succ.definition of (x := nVar))

        val pointwiseAtSucc = have(
          (a ∈ app(heightFun)(Succ(nVar))) ==> (app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) subproof {
          val goalAtA = app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a)
          val aInHeightSucc = assume(a ∈ app(heightFun)(Succ(nVar)))

          val succInN = have(Succ(nVar) ∈ N) by
            Tautology.from(nInN, NatFacts.succIntro.of(n := nVar))

          // Approximant typings, fed to the shared witness-agreement lemma.
          val approxTypeAtN = have(nVar ∈ N ==> (G(nVar) :: spec.typ)) by
            InstantiateForall(nVar)(approx.approxHasType)
          val gNHasType = have(G(nVar) :: spec.typ) by Tautology.from(nInN, approxTypeAtN)
          val approxTypeAtSuccN = have(Succ(nVar) ∈ N ==> (G(Succ(nVar)) :: spec.typ)) by
            InstantiateForall(Succ(nVar))(approx.approxHasType)
          val gSuccHasType = have(G(Succ(nVar)) :: spec.typ) by Tautology.from(
            succInN,
            approxTypeAtSuccN
          )

          // approxSucc glue: G(Succ n) = W(G n), G(Succ Succ n) = W(G(Succ n)).
          val approxSuccAtN = have(nVar ∈ N ==> (G(Succ(nVar)) === recWitness(G(nVar)))) by
            InstantiateForall(nVar)(approx.approxSucc)
          val gSuccEq = have(G(Succ(nVar)) === recWitness(G(nVar))) by
            Tautology.from(nInN, approxSuccAtN)
          val gSuccAtAIsWitness = have(app(G(Succ(nVar)))(a) === app(recWitness(G(nVar)))(a)) by
            Congruence.from(gSuccEq)

          val approxSuccAtSuccN = have(
            Succ(nVar) ∈ N ==> (G(Succ(Succ(nVar))) === recWitness(G(Succ(nVar))))
          ) by InstantiateForall(Succ(nVar))(approx.approxSucc)
          val gSuccSuccEq = have(G(Succ(Succ(nVar))) === recWitness(G(Succ(nVar)))) by
            Tautology.from(succInN, approxSuccAtSuccN)
          val witnessSuccAtARev = have(
            app(recWitness(G(Succ(nVar))))(a) === app(G(Succ(Succ(nVar))))(a)
          ) by Congruence.from(gSuccSuccEq)

          // The induction hypothesis `ih = P(n)` is exactly the slice-agreement premise of
          // WitnessAgreement.witnessAgreementAtSucc at leftFun := G(n), rightFun := G(Succ n).
          val witnessAgreeOnSucc = have(
            ∀(a ∈ app(heightFun)(Succ(nVar)), app(recWitness(G(nVar)))(a) === app(recWitness(G(Succ(nVar))))(a))
          ) by Tautology.from(
            witnessAgreement.witnessAgreementAtSucc.of(
              witnessAgreement.leftFun := G(nVar),
              witnessAgreement.rightFun := G(Succ(nVar)),
              witnessAgreement.nVar := nVar
            ),
            gNHasType,
            gSuccHasType,
            nInN,
            ih
          )
          val witnessAgreeImpl = have(
            (a ∈ app(heightFun)(Succ(nVar))) ==> (app(recWitness(G(nVar)))(a) === app(recWitness(G(Succ(nVar))))(a))
          ) by InstantiateForall(a)(witnessAgreeOnSucc)
          val witnessesAgreeAtA = have(
            app(recWitness(G(nVar)))(a) === app(recWitness(G(Succ(nVar))))(a)
          ) by Tautology.from(witnessAgreeImpl, aInHeightSucc)

          have(goalAtA) by Tautology.from(
            altEqualityTransitivity of (
              x := app(G(Succ(nVar)))(a),
              y := app(recWitness(G(nVar)))(a),
              z := app(G(Succ(Succ(nVar))))(a)
            ),
            altEqualityTransitivity of (
              x := app(recWitness(G(nVar)))(a),
              y := app(recWitness(G(Succ(nVar))))(a),
              z := app(G(Succ(Succ(nVar))))(a)
            ),
            gSuccAtAIsWitness,
            witnessesAgreeAtA,
            witnessSuccAtARev
          )
        }
        have(
          a ∈ app(heightFun)(Succ(nVar)) ==> (app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) by Restate.from(pointwiseAtSucc)
        thenHave(
          ∀(a ∈ app(heightFun)(Succ(nVar)), app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) by RightForall
      }
      thenHave(thesis) by RightForall
    }

    have(∀(nVar, (nVar ∈ N) ==> P(nVar))) by
      Tautology.from(NatFacts.induction of (Pred := P), base, step)
    thenHave(thesis) by Restate
  })

}
