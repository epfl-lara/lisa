package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.FunctionAbstractions.TAbsConstOn
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.equivalenceApply
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class LimitConstruction[N <: Arity](
  val spec: FunSpec[N],
  val approx: Approx[N],
  val approxProp: ApproxProp[N]
) {

  val nVar = variable[Ind]
  val mVar = variable[Ind]
  val kVar = variable[Ind]
  import approx.G
  import approxProp.{heightFun, heightFunValid, isHeightPred}

  private val termHasHeight = spec.adt.height.termHasHeightAt(spec.typeSubstitutions)

  def limitIndex(point: Expr[Ind]): Expr[Ind] =
    ε(nVar, (nVar ∈ N) /\ (point ∈ app(heightFun)(nVar)))

  val limitFun: Expr[Ind] =
    abs(spec.argType)(λ(a, app(G(limitIndex(a)))(a)))

  val limitHasType: THM = Time.measure(s"limitHasType for ${spec.functionName}")(Lemma(limitFun :: spec.typ) {
    val hValid = have(isHeightPred(heightFun)) by Restate.from(heightFunValid)

    val everyValueTyped = have(
      ∀(a ∈ spec.argType, app(G(limitIndex(a)))(a) ∈ spec.returnType)
    ) subproof {
      val pointwiseAtA = have(
        (a ∈ spec.argType) ==> (app(G(limitIndex(a)))(a) ∈ spec.returnType)
      ) subproof {
        val aInArgType = assume(a ∈ spec.argType)

        val hasSomeHeight = have(
          ∃(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))
        ) by Tautology.from(
          hValid,
          aInArgType,
          termHasHeight of (x := a, h := heightFun),
          equivalenceApply of (
            p1 := in(a, spec.argType),
            p2 := ∃(nVar, in(nVar, N) /\ in(a, app(heightFun)(nVar)))
          )
        )

        val indexWitness = have(
          (limitIndex(a) ∈ N) /\ (a ∈ app(heightFun)(limitIndex(a)))
        ) by lisa.utils.prooflib.BasicStepTactic.Cut(
          hasSomeHeight,
          Quantifiers.existsEpsilon.of(
            x := nVar,
            P := λ(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))
          )
        )

        val indexInN = have(limitIndex(a) ∈ N) by Tautology.from(indexWitness)

        val approxAtIndex = have(limitIndex(a) ∈ N ==> (G(limitIndex(a)) :: spec.typ)) by
          InstantiateForall(limitIndex(a))(approx.approxHasType)
        val approxTyped = have(G(limitIndex(a)) :: spec.typ) by
          Tautology.from(indexInN, approxAtIndex)

        val approxBetween = have(
          functionBetween(G(limitIndex(a)))(spec.argType)(spec.returnType)
        ) by Tautology.from(
          funcBetweenEqInFuncSpace of (
            f := G(limitIndex(a)),
            A := spec.argType,
            B := spec.returnType
          ),
          approxTyped
        )

        have(app(G(limitIndex(a)))(a) ∈ spec.returnType) by Tautology.from(
          approxBetween,
          aInArgType,
          appTyping of (
            f := G(limitIndex(a)),
            A := spec.argType,
            B := spec.returnType,
            x := a
          )
        )
        thenHave(thesis) by RightImplies.withParameters(
          a ∈ spec.argType,
          app(G(limitIndex(a)))(a) ∈ spec.returnType
        )
      }
      have(
        (a ∈ spec.argType) ==> (app(G(limitIndex(a)))(a) ∈ spec.returnType)
      ) by Restate.from(pointwiseAtA)
      thenHave(
        ∀(a, (a ∈ spec.argType) ==> (app(G(limitIndex(a)))(a) ∈ spec.returnType))
      ) by RightForall
      thenHave(thesis) by Restate
    }

    val absTypedAtPi = have(
      abs(spec.argType)(λ(a, app(G(limitIndex(a)))(a))) ∈ Pi(spec.argType)(λ(y, spec.returnType))
    ) by Tautology.from(
      everyValueTyped,
      TAbsConstOn(spec.argType, spec.returnType, λ(a, app(G(limitIndex(a)))(a)))
    )

    have(limitFun :: spec.typ) by Congruence.from(absTypedAtPi)
    thenHave(thesis) by Restate
  })
}
