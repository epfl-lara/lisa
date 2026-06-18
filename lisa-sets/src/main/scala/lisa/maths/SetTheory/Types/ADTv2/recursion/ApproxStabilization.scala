package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.{omegaSuccessorInduction, successorInOmega}
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
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
 *   - [[stabilization]]
 */
private[recursion] final class ApproxStabilization[N <: Arity](
    val spec: FunSpec[N],
    val recWitness: Witness[N],
    val approxSeq: ApproxSequence[N],
    val witnessAgreement: helpers.WitnessAgreement[N]
) {

  private val nVar = variable[Ind]
  import approxSeq.G

  /**
   * Instantiates a `∀(x ∈ N, φ(x))` theorem at `m` and discharges the `m ∈ N` premise,
   * yielding `φ(m)`. `consequent` is the expected `φ(m)`.
   */
  private def instantiateAt(using proof: lisa.SetTheoryLibrary.Proof)(
      forallThm: THM,
      m: Expr[Ind],
      mInN: proof.Fact,
      consequent: Expr[Prop]
  ): proof.Fact = {
    val impl = have((m ∈ N) ==> consequent) by InstantiateForall(m)(forallThm)
    have(consequent) by Tautology.from(mInN, impl)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma D — stabilization
  // ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
  // ─────────────────────────────────────────────────────────────────────────

  val stabilization: THM = Time.measure(s"AP/stabilization")(
    Lemma(
      ∀(nVar ∈ N, ∀(a ∈ app(spec.heightFun)(nVar), app(G(nVar))(a) === app(G(S(nVar)))(a)))
    ) {
      val prop = λ(nVar, ∀(a ∈ app(spec.heightFun)(nVar), app(G(nVar))(a) === app(G(S(nVar)))(a)))

      val hValid = have(spec.isHeightPred(spec.heightFun)) by Weakening(spec.heightFunValid)

      val noElemAtEmpty = have(!(a ∈ app(spec.heightFun)(∅))) by Cut(
        hValid,
        spec.heightZero of (h := spec.heightFun, x := a)
      )

      have(a ∈ app(spec.heightFun)(∅) |- app(G(∅))(a) === app(G(S(∅)))(a)) by
        Tautology.from(noElemAtEmpty)
      thenHave(
        (a ∈ app(spec.heightFun)(∅)) ==> (app(G(∅))(a) === app(G(S(∅)))(a))
      ) by RightImplies
      thenHave(
        ∀(a, (a ∈ app(spec.heightFun)(∅)) ==> (app(G(∅))(a) === app(G(S(∅)))(a)))
      ) by RightForall
      val base = thenHave(prop(∅)) by Restate
      

      val goalAtA = app(G(S(nVar)))(a) === app(G(S(S(nVar))))(a)
      val pointwiseAtSucc = have(
        ((nVar ∈ N), prop(nVar), (a ∈ app(spec.heightFun)(S(nVar)))) |- goalAtA
      ) subproof {
        val nInN = assume(nVar ∈ N)
        val ih = assume(prop(nVar))
        val aInHeightSucc = assume(a ∈ app(spec.heightFun)(S(nVar)))

        val succInN = have(S(nVar) ∈ N) by
          Tautology.from(nInN, successorInOmega.of(n := nVar))

        // approxSucc glue: G(Succ n) = W(G n), G(Succ Succ n) = W(G(Succ n)).
        val gSuccAtAIsWitness = have(app(G(S(nVar)))(a) === app(recWitness(G(nVar)))(a)) by
          Congruence.from(instantiateAt(approxSeq.approxSucc, nVar, nInN, G(S(nVar)) === recWitness(G(nVar))))

        val witnessSuccAtARev = have(
          app(recWitness(G(S(nVar))))(a) === app(G(S(S(nVar))))(a)
        ) by Congruence.from(instantiateAt(
          approxSeq.approxSucc, S(nVar), succInN, G(S(S(nVar))) === recWitness(G(S(nVar)))
        ))

        // The induction hypothesis `ih = prop(n)` is exactly the slice-agreement premise of
        // WitnessAgreement.witnessAgreementAtSucc at leftFun := G(n), rightFun := G(Succ n).
        // Chain: G(Sn)(a) === W(Gn)(a) === W(G(Sn))(a) === G(SSn)(a), with the
        // middle link supplied by the witness agreement and the rest as bridges.
        have(thesis) by Restate.from(
          witnessAgreement.witnessesAgreeAt(
            lhs = G(nVar),
            rhs = G(S(nVar)),
            index = nVar,
            lhsTyped = instantiateAt(approxSeq.approxHasType, nVar, nInN, G(nVar) :: spec.typ),
            rhsTyped = instantiateAt(approxSeq.approxHasType, S(nVar), succInN, G(S(nVar)) :: spec.typ),
            indexInN = nInN,
            sliceAgreement = ih,
            pointInHeightSucc = aInHeightSucc,
            goal = goalAtA,
            bridges = Seq(gSuccAtAIsWitness, witnessSuccAtARev)
          )
        )
      }
      
      have( ((nVar ∈ N), prop(nVar)) |- (a ∈ app(spec.heightFun)(S(nVar))) ==> goalAtA) by 
        Restate.from(pointwiseAtSucc)
      have( ((nVar ∈ N), prop(nVar)) |-
        ∀(a ∈ app(spec.heightFun)(S(nVar)), goalAtA)
      ) by RightForall(lastStep)
      have((nVar ∈ N) ==> (prop(nVar) ==> prop(S(nVar)))) by Restate.from(lastStep)
      val step = have(∀(nVar ∈ N, prop(nVar) ==> prop(S(nVar)))) by RightForall(lastStep)

      val P = variable[Ind >>: Prop]
      have(∀(nVar, (nVar ∈ N) ==> prop(nVar))) by
        Tautology.from(omegaSuccessorInduction of (P := prop), base, step)
      thenHave(thesis) by Restate
    }
  )

}
