package lisa.maths.SetTheory.Types.ADT.recursion.proofs

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.proofs.PropositionalFacts.altEqualityTransitivity
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.utils.fol.FOL.SubstPair
import lisa.utils.prooflib.Thm

private[recursion] object LimitKernel {

  private val argType = variable[Ind]
  private val heightFun = variable[Ind]
  private val limitFun = variable[Ind]
  private val G = variable[Ind >>: Ind]
  private val limitIndex = variable[Ind >>: Ind]

  private val pointVar = variable[Ind]
  private val nVar = variable[Ind]
  private val mVar = variable[Ind]

  private val pointHeightFormula =
    (pointVar ∈ argType) <=> ∃(nVar, nVar ∈ N /\ pointVar ∈ app(heightFun)(nVar))

  private val limitIndexFormula =
    limitIndex(pointVar) === ε(nVar, (nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar)))

  private val limitFunFormula =
    limitFun === abs(argType)(λ(pointVar, app(G(limitIndex(pointVar)))(pointVar)))

  def pointHeightCharAt(argType0: Expr[Ind], heightFun0: Expr[Ind], point0: Expr[Ind]): Expr[Prop] =
    pointHeightFormula.substitute(argType := argType0, heightFun := heightFun0, pointVar := point0)

  def limitIndexWitnessAt(heightFun0: Expr[Ind], limitIndex0: Expr[Ind >>: Ind], point0: Expr[Ind]): Expr[Prop] =
    (limitIndex0(point0) ∈ N) /\ (point0 ∈ app(heightFun0)(limitIndex0(point0)))

  private def limitIndexDefinitionAt(heightFun0: Expr[Ind], limitIndex0: Expr[Ind >>: Ind], point0: Expr[Ind]): Expr[Prop] =
    limitIndexFormula.substitute(heightFun := heightFun0, limitIndex := limitIndex0, pointVar := point0)

  def limitFunDefinition(
      argType0: Expr[Ind],
      limitFun0: Expr[Ind],
      G0: Expr[Ind >>: Ind],
      limitIndex0: Expr[Ind >>: Ind]
  ): Expr[Prop] =
    limitFunFormula.substitute(argType := argType0, limitFun := limitFun0, G := G0, limitIndex := limitIndex0)

  private val pointHasSomeHeight: Theorem = Lemma(
    (pointHeightCharAt(argType, heightFun, pointVar), pointVar ∈ argType) |- ∃(nVar, (nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar)))
  ) {
    val pointHeightChar = assume(pointHeightCharAt(argType, heightFun, pointVar))
    val pointInArgType = assume(pointVar ∈ argType)
    have(thesis) by Tautology.from(
      pointInArgType,
      pointHeightChar
    )
  }

  private val heightMembershipImpliesInArgType: Theorem = Lemma(
    (pointHeightCharAt(argType, heightFun, pointVar), nVar ∈ N, pointVar ∈ app(heightFun)(nVar)) |- pointVar ∈ argType
  ) {
    val pointHeightChar = assume(pointHeightCharAt(argType, heightFun, pointVar))
    val indexInN = assume(nVar ∈ N)
    val pointInHeight = assume(pointVar ∈ app(heightFun)(nVar))

    val pointHasHeight = have(
      ∃(mVar, (mVar ∈ N) /\ (pointVar ∈ app(heightFun)(mVar)))
    ) subproof {
      have((nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar))) by Tautology.from(indexInN, pointInHeight)
      thenHave(thesis) by RightExists
    }

    have(pointVar ∈ argType) by Tautology.from(
      pointHasHeight,
      pointHeightChar
    )
    thenHave(thesis) by Restate
  }

  private val limitIndexWitness: Theorem = Lemma(
    (
      pointHeightCharAt(argType, heightFun, pointVar),
      limitIndexDefinitionAt(heightFun, limitIndex, pointVar),
      pointVar ∈ argType
    ) |- limitIndexWitnessAt(heightFun, limitIndex, pointVar)
  ) {
    val pointHeightChar = assume(pointHeightCharAt(argType, heightFun, pointVar))
    val limitIndexDef = assume(limitIndexDefinitionAt(heightFun, limitIndex, pointVar))
    val pointInArgType = assume(pointVar ∈ argType)
    val pointHasSomeHeightInst = have(
      (pointHeightCharAt(argType, heightFun, pointVar), pointVar ∈ argType) |-
        ∃(nVar, (nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar)))
    ) by Restate.from(pointHasSomeHeight)
    val pointHasHeight = have(
      ∃(nVar, (nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar)))
    ) by Tautology.from(pointHeightChar, pointInArgType, pointHasSomeHeightInst)

    val epsilonWitness = have(
      (ε(nVar, (nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar))) ∈ N) /\
        (pointVar ∈ app(heightFun)(ε(nVar, (nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar)))))
    ) by Tautology.from(
      pointHasHeight,
      Quantifiers.existsEpsilon.of(
        x := nVar,
        P := λ(nVar, (nVar ∈ N) /\ (pointVar ∈ app(heightFun)(nVar)))
      )
    )

    have(thesis) by Congruence.from(limitIndexDef, epsilonWitness)
  }

  private val limitValueAtIndex: Theorem = Lemma(
    (limitFunDefinition(argType, limitFun, G, limitIndex), pointVar ∈ argType) |-
      app(limitFun)(pointVar) === app(G(limitIndex(pointVar)))(pointVar)
  ) {
    val T, e2 = variable[Ind]
    val e = variable[Ind >>: Ind]
    val pointInArgType = assume(pointVar ∈ argType)
    val limitDef = assume(limitFunDefinition(argType, limitFun, G, limitIndex))

    val betaAtPoint = have(
      app(abs(argType)(λ(pointVar, app(G(limitIndex(pointVar)))(pointVar))))(pointVar) ===
        app(G(limitIndex(pointVar)))(pointVar)
    ) by Tautology.from(
      pointInArgType,
      BetaReduction of (
        T := argType,
        e := λ(pointVar, app(G(limitIndex(pointVar)))(pointVar)),
        e2 := pointVar
      )
    )

    have(thesis) by Congruence.from(limitDef, betaAtPoint)
  }

  private val limitAtHeight: Theorem = Lemma(
    (
      pointHeightCharAt(argType, heightFun, pointVar),
      limitIndexDefinitionAt(heightFun, limitIndex, pointVar),
      limitFunDefinition(argType, limitFun, G, limitIndex),
      ApproximationChainFacts.stabilizationSchema(heightFun, G),
      ApproximationChainFacts.heightMembershipMonotonicSchema(heightFun),
      nVar ∈ N,
      pointVar ∈ app(heightFun)(nVar)
    ) |- app(limitFun)(pointVar) === app(G(nVar))(pointVar)
  ) {
    val pointHeightChar = assume(pointHeightCharAt(argType, heightFun, pointVar))
    val limitIndexDef = assume(limitIndexDefinitionAt(heightFun, limitIndex, pointVar))
    val limitDef = assume(limitFunDefinition(argType, limitFun, G, limitIndex))
    val stabSchema = assume(ApproximationChainFacts.stabilizationSchema(heightFun, G))
    val monoSchema = assume(ApproximationChainFacts.heightMembershipMonotonicSchema(heightFun))
    val indexInN = assume(nVar ∈ N)
    val pointInHeight = assume(pointVar ∈ app(heightFun)(nVar))
    val heightMembershipInst = have(
      (pointHeightCharAt(argType, heightFun, pointVar), nVar ∈ N, pointVar ∈ app(heightFun)(nVar)) |- pointVar ∈ argType
    ) by Tautology.from(heightMembershipImpliesInArgType)
    val limitValueAtIndexInst = have(
      (limitFunDefinition(argType, limitFun, G, limitIndex), pointVar ∈ argType) |-
        app(limitFun)(pointVar) === app(G(limitIndex(pointVar)))(pointVar)
    ) by Tautology.from(limitValueAtIndex)
    val limitIndexWitnessInst = have(
      (
        pointHeightCharAt(argType, heightFun, pointVar),
        limitIndexDefinitionAt(heightFun, limitIndex, pointVar),
        pointVar ∈ argType
      ) |- limitIndexWitnessAt(heightFun, limitIndex, pointVar)
    ) by Tautology.from(limitIndexWitness)

    val pointInArgType = have(pointVar ∈ argType) by Tautology.from(
      pointHeightChar,
      indexInN,
      pointInHeight,
      heightMembershipInst
    )

    val limitAtIndex = have(app(limitFun)(pointVar) === app(G(limitIndex(pointVar)))(pointVar)) by Tautology.from(
      limitDef,
      pointInArgType,
      limitValueAtIndexInst
    )

    val indexWitness = have(limitIndexWitnessAt(heightFun, limitIndex, pointVar)) by Tautology.from(
      pointHeightChar,
      limitIndexDef,
      pointInArgType,
      limitIndexWitnessInst
    )
    val limitIndexInN = have(limitIndex(pointVar) ∈ N) by Tautology.from(indexWitness)
    val pointInLimitHeight = have(pointVar ∈ app(heightFun)(limitIndex(pointVar))) by Tautology.from(indexWitness)

    val agreeAtHeight = have(app(G(limitIndex(pointVar)))(pointVar) === app(G(nVar))(pointVar)) by
      Tautology.from(
        ApproximationChainFacts.approximantsAgreeAcrossHeightsAt(heightFun, G, limitIndex(pointVar), nVar, pointVar),
        stabSchema,
        monoSchema,
        limitIndexInN,
        indexInN,
        pointInLimitHeight,
        pointInHeight
      )

    have(app(limitFun)(pointVar) === app(G(nVar))(pointVar)) by Tautology.from(
      altEqualityTransitivity of (
        x := app(limitFun)(pointVar),
        y := app(G(limitIndex(pointVar)))(pointVar),
        z := app(G(nVar))(pointVar)
      ),
      limitAtIndex,
      agreeAtHeight
    )
    thenHave(thesis) by Restate
  }

  def pointHasSomeHeightAt(argType0: Expr[Ind], heightFun0: Expr[Ind], point0: Expr[Ind])(using proof: lisa.SetTheoryLibrary.Proof): Thm =
    pointHasSomeHeight.of(argType := argType0, heightFun := heightFun0, pointVar := point0)

  def limitIndexWitnessAt(
      argType0: Expr[Ind],
      heightFun0: Expr[Ind],
      limitIndex0: Expr[Ind >>: Ind],
      point0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): Thm =
    limitIndexWitness.of(
      argType := argType0,
      heightFun := heightFun0,
      limitIndex := limitIndex0,
      pointVar := point0
    )

  def limitAtHeightAt(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      argType0: Expr[Ind],
      heightFun0: Expr[Ind],
      limitFun0: Expr[Ind],
      G0: Expr[Ind >>: Ind],
      limitIndex0: Expr[Ind >>: Ind],
      point0: Expr[Ind],
      n0: Expr[Ind],
      stabilization0: Theorem,
      heightMembershipMonotonic: Seq[SubstPair] => Thm,
      heightFunValid: Thm
  ): Thm =
    val monoSchema = ApproximationChainFacts.heightMembershipMonotonicSchemaAt(
      heightFun0,
      heightMembershipMonotonic,
      heightFunValid
    )
    have(
      (
        pointHeightCharAt(argType0, heightFun0, point0),
        limitIndexDefinitionAt(heightFun0, limitIndex0, point0),
        limitFunDefinition(argType0, limitFun0, G0, limitIndex0),
        n0 ∈ N,
        point0 ∈ app(heightFun0)(n0)
      ) |- app(limitFun0)(point0) === app(G0(n0))(point0)
    ) by Tautology.from(
      limitAtHeight.of(
        argType := argType0,
        heightFun := heightFun0,
        limitFun := limitFun0,
        G := G0,
        limitIndex := limitIndex0,
        pointVar := point0,
        nVar := n0
      ),
      stabilization0,
      monoSchema
    )

  def initialize(): Unit = {
    val _ = pointHasSomeHeight
    val _ = heightMembershipImpliesInArgType
    val _ = limitIndexWitness
    val _ = limitValueAtIndex
    val _ = limitAtHeight
  }
}
