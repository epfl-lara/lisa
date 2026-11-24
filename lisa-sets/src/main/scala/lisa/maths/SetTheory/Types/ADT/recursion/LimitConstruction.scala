package lisa.maths.SetTheory.Types.ADT.recursion

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.maths.SetTheory.Types.TypingRules.TApp

/**
 * Chooses a sufficient height for each input to construct the typed limit function.
 */
private[recursion] final class LimitConstruction(
    val spec: FunSpec,
    val approxSeq: ApproxSequence,
    val approxStab: ApproxStabilization
) {
  private val nVar = spec.proofVariable("nVar")
  private val a = spec.proofVariable("a")
  private val typePoint = spec.proofVariable("typePoint")
  import approxSeq.G
  import spec.{heightFun, heightFunValid, isHeightPred}

  private val indexAtPoint = ε(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))

  /**
   * A natural-number height containing the supplied input when it belongs to the domain.
   */
  def limitIndex(point: Expr[Ind]): Expr[Ind] =
    indexAtPoint.substitute(a := point)

  /**
   * Evaluates each input using an approximant at its chosen height.
   */
  val limitFun: Expr[Ind] =
    abs(spec.argType)(λ(a, app(G(limitIndex(a)))(a)))

  /**
   * The limit has the function's declared type.
   */
  val limitHasType: THM = Lemma(limitFun :: spec.typ) {
    val T1, e1, e2 = variable[Ind]
    val T2, e = variable[Ind >>: Ind]
    val hValid = have(isHeightPred(heightFun)) by Restate.from(heightFunValid)

    have(a ∈ spec.argType |- app(G(limitIndex(a)))(a) ∈ spec.returnType) subproof {
      val aInArgType = assume(a ∈ spec.argType)
      val hasSomeHeight = have(
        ∃(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))
      ) by Tautology.from(
        hValid,
        aInArgType,
        spec.adt.height.termHasHeightAt(spec.typeSubstitutions, Seq(x := a, h := heightFun))
      )
      val indexWitness = have(
        (limitIndex(a) ∈ N) /\ (a ∈ app(heightFun)(limitIndex(a)))
      ) by Cut(
        hasSomeHeight,
        Quantifiers.existsEpsilon.of(
          x := nVar,
          P := λ(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))
        )
      )
      val approxAtIndex = have(limitIndex(a) ∈ N ==> (G(limitIndex(a)) :: spec.typ)) by
        InstantiateForall(limitIndex(a))(approxSeq.approxHasType)
      val approxTyped = have(G(limitIndex(a)) :: spec.typ) by Tautology.from(indexWitness, approxAtIndex)
      have(thesis) by Tautology.from(
        approxTyped,
        aInArgType,
        TApp.of(T1 := spec.argType, T2 := λ(typePoint, spec.returnType), e1 := G(limitIndex(a)), e2 := a)
      )
    }
    thenHave(a ∈ spec.argType ==> app(G(limitIndex(a)))(a) ∈ spec.returnType) by Restate
    val everyValueTyped = thenHave(∀(a ∈ spec.argType, app(G(limitIndex(a)))(a) ∈ spec.returnType)) by RightForall
    have(thesis) by Cut(
      everyValueTyped,
      TAbs.of(T1 := spec.argType, T2 := λ(typePoint, spec.returnType), e := λ(a, app(G(limitIndex(a)))(a)))
    )
  }
}
