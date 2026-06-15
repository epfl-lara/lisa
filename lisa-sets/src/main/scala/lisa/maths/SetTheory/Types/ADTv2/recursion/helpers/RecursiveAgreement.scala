package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ApproximationChainFacts
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.LimitKernel
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] object RecursiveAgreement {


  private val h = variable[Ind]
  private val x = variable[Ind]

  def selfAgreementFromForall(using proof: lisa.SetTheoryLibrary.Proof)(
      heightFun: Expr[Ind],
      currentIndex: Expr[Ind],
      leftFun: Expr[Ind],
      rightFun: Expr[Ind],
      agreeForall: proof.Fact,
      point: Expr[Ind],
      pointInHeight: proof.Fact
  ): proof.Fact = {
    val pIn: Expr[Prop] = point ∈ app(heightFun)(currentIndex)
    val pEq: Expr[Prop] = app(leftFun)(point) === app(rightFun)(point)
    val atPoint = have(pIn ==> pEq) by InstantiateForall(point)(agreeForall)
    
    // Modus ponens via kernel rules instead of `Tautology.from(pointInHeight, atPoint)`:
    // `pointInHeight` carries the deep ~1.5k-char branchSelectionBody in its context, and
    // Tautology would decompose it (~30s). With `pIn`/`pEq` kept atomic, that context is
    // carried untouched through the cut.
    val mp = have(Set[Expr[Prop]](pIn ==> pEq, pIn) |- pEq) by LeftImplies.withParameters(pIn, pEq)(
      have(pIn |- pIn) by Hypothesis,
      have(pEq |- pEq) by Hypothesis
    )
    val viaImpl = have((atPoint.statement.left + pIn) |- pEq) by Cut(atPoint, mp)
    have((atPoint.statement.left ++ pointInHeight.statement.left) |- pEq) by Cut(pointInHeight, viaImpl)
    
  }

  def selfAgreementFromForallAt2[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
    pattern: Pattern[N],
    recursiveType: Expr[Ind],
    heightMembershipMonotonic: THM,
    argsTypedAtHeight: proof.Fact,
    leafTyping: proof.Fact,
    patternGuard: proof.Fact,
    heightFun: Expr[Ind],
    hValid: proof.Fact,
    currentIndex: Expr[Ind],
    currentIndexInN: proof.Fact,
    leftFun: Expr[Ind],
    rightFun: Expr[Ind],
    agreeForall: proof.Fact
  ): Seq[proof.Fact] = {
    pattern.recursiveAgreementPoints(recursiveType).map { point =>
      val pointInHeight = pattern.recursiveAgreementPointInHeight(
        target = point,
        recursiveType = recursiveType,
        heightFun = heightFun,
        hValid = hValid,
        heightMembershipMonotonic = heightMembershipMonotonic,
        currentIndex = currentIndex,
        currentIndexInN = currentIndexInN,
        argsTypedAtHeight = argsTypedAtHeight,
        leafTyping = leafTyping,
        patternGuard = patternGuard
      )
      selfAgreementFromForall(
        heightFun,
        currentIndex,
        leftFun,
        rightFun,
        agreeForall,
        point,
        pointInHeight
      )
    }
  }

  def selfAgreementWithLimit(using proof: lisa.SetTheoryLibrary.Proof)(
      argType: Expr[Ind],
      heightFun: Expr[Ind],
      limitFun: Expr[Ind],
      approximantFamily: Expr[Ind >>: Ind],
      chosenIndexFamily: Expr[Ind >>: Ind],
      limitFunDef: Expr[Prop],
      termHasHeight: THM,
      stabilizationSchema: proof.Fact,
      heightMembershipMonotonicSchema: proof.Fact,
      hValid: proof.Fact,
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact,
      point: Expr[Ind],
      pointInHeight: proof.Fact
  ): proof.Fact = {
    val pointHeightChar = have(LimitKernel.pointHeightCharAt(argType, heightFun, point)) by
      Tautology.from(hValid, termHasHeight.of(x := point, h := heightFun))
    have(app(limitFun)(point) === app(approximantFamily(currentIndex))(point)) by Tautology.from(
      pointHeightChar,
      have(LimitKernel.limitIndexDefinitionAt(heightFun, chosenIndexFamily, point)) by Restate,
      have(limitFunDef) by Restate,
      have(LimitKernel.approxAgreementAt(heightFun, approximantFamily, point, chosenIndexFamily(point), currentIndex)) by
        Tautology.from(
          ApproximationChainFacts.approximantsAgreeAcrossHeightsAt(
            heightFun,
            approximantFamily,
            chosenIndexFamily(point),
            currentIndex,
            point
          )(stabilizationSchema, heightMembershipMonotonicSchema)
        ),
      currentIndexInN,
      pointInHeight,
      LimitKernel.limitAtHeightAt(
        argType,
        heightFun,
        limitFun,
        approximantFamily,
        chosenIndexFamily,
        point,
        currentIndex
      )
    )
  }

}
