package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.Functions.Pi.Pi
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts.altEqualityTransitivity
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingTheorems.arrowElim
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.BasicStepTactic.Restate

object FunctionAbstractions {

  private val domainVar = variable[Ind]("domain")
  private val codomainVar = variable[Ind]("codomain")
  private val bodyVar = variable[Ind >>: Ind]("body")
  private val pointVar = variable[Ind]("point")
  private val tailTypeVar = variable[Ind]("tailType")
  private val currentFunVar = variable[Ind]("currentFun")
  private val leftFunVar = variable[Ind]("leftFun")
  private val rightFunVar = variable[Ind]("rightFun")

  def nestedAbstraction(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      body: Expr[Ind]
  ): Expr[Ind] =
    signature.reverse.foldLeft(body) { case (acc, (v, domain)) =>
      TypingHelpers.fun(v :: domain, acc)
    }

  lazy val TAbsConstOnGeneral: THM = Lemma(
    ∀(pointVar ∈ domainVar, bodyVar(pointVar) ∈ codomainVar) |- abs(domainVar)(bodyVar) ∈ Pi(
      domainVar
    )(λ(x, codomainVar))
  ) {
    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val e = variable[Ind >>: Ind]

    assume(∀(pointVar ∈ domainVar, bodyVar(pointVar) ∈ codomainVar))
    val premiseAtX = have(pointVar ∈ domainVar ==> bodyVar(pointVar) ∈ codomainVar) by InstantiateForall
    have(pointVar ∈ domainVar ==> bodyVar(pointVar) ∈ λ(x, codomainVar)(pointVar)) by
      Tautology.from(premiseAtX)
    thenHave(∀(pointVar ∈ domainVar, bodyVar(pointVar) ∈ λ(x, codomainVar)(pointVar))) by RightForall
    have(abs(domainVar)(bodyVar) ∈ Pi(domainVar)(λ(x, codomainVar))) by
      Tautology.from(lastStep, TAbs of (T1 := domainVar, T2 := λ(x, codomainVar), e := bodyVar))
    thenHave(thesis) by Restate
  }

  def TAbsConstOn(
      domain: Expr[Ind],
      codomain: Expr[Ind],
      body: Expr[Ind >>: Ind]
  ): THM = Lemma(
    ∀(pointVar ∈ domain, body(pointVar) ∈ codomain) |- abs(domain)(body) ∈ Pi(domain)(λ(pointVar, codomain))
  ) {
    have(thesis) by Tautology.from(
      TAbsConstOnGeneral.of(
        domainVar := domain,
        codomainVar := codomain,
        bodyVar := body
      )
    )
  }

  def instantiateForallSeq(
      quantifiedFormula: Expr[Prop],
      args: Seq[Expr[Ind]]
  ): THM = {
    val instantiated = args.foldLeft(quantifiedFormula) { (current, arg) =>
      current match
        case forall(v, phi) =>
          phi.substitute(v := arg).asInstanceOf[Expr[Prop]]
        case _ => current
    }

    Lemma(quantifiedFormula |- instantiated) {
      var current = assume(quantifiedFormula)

      for arg <- args do
        current.statement.right.head match
          case forall(v, phi) =>
            current = have(phi.substitute(v := arg).asInstanceOf[Expr[Prop]]) by InstantiateForall(arg)(current)
          case _ =>

      have(thesis) by Restate.from(current)
    }
  }

  private def betaAtHead(
      remainingSig: Seq[(Variable[Ind], Expr[Ind])],
      current: Expr[Ind],
      currentVar: Variable[Ind],
      domain: Expr[Ind],
      inner: Expr[Ind]
  ): THM = Lemma(wellTypedFormula(remainingSig) |- (current * currentVar === inner)) {
    val T = variable[Ind]
    val e = variable[Ind >>: Ind]
    val e2 = variable[Ind]
    val allTyped = assume(wellTypedFormula(remainingSig))
    val headTyped = have(currentVar ∈ domain) by Tautology.from(allTyped)
    have(thesis) by Tautology.from(
      headTyped,
      BetaReduction of (T := domain, e := λ(currentVar, inner), e2 := currentVar)
    )
  }

  private def liftEqualityThroughApplications(
      context: Expr[Prop],
      initialEq: THM,
      startLeft: Expr[Ind],
      startRight: Expr[Ind],
      tailVars: Seq[Variable[Ind]]
  ): THM = {
    val finalLeft = tailVars.foldLeft(startLeft: Expr[Ind])(_ * _)
    val finalRight = tailVars.foldLeft(startRight: Expr[Ind])(_ * _)
    Lemma(context |- (finalLeft === finalRight)) {
      var currentEq = have(initialEq.statement) by Restate.from(initialEq)
      var leftExpr = startLeft
      var rightExpr = startRight

      for arg <- tailVars do
        val nextLeft = leftExpr * arg
        val nextRight = rightExpr * arg
        currentEq = have(context |- (nextLeft === nextRight)) by Congruence.from(currentEq)
        leftExpr = nextLeft
        rightExpr = nextRight

      have(thesis) by Restate.from(currentEq)
    }
  }

  private def weakenTailTyping(
      remainingSig: Seq[(Variable[Ind], Expr[Ind])],
      tailSig: Seq[(Variable[Ind], Expr[Ind])]
  ): THM = Lemma(wellTypedFormula(remainingSig) |- wellTypedFormula(tailSig)) {
    val allTyped = assume(wellTypedFormula(remainingSig))
    if tailSig.isEmpty then
      have(thesis) by Tautology
    else
      have(thesis) by Tautology.from(allTyped)
  }

  lazy val applicationTypingFromFunctionTypingGeneral: THM =
    Lemma((currentFunVar :: (domainVar ->: tailTypeVar), pointVar ∈ domainVar) |- ((currentFunVar * pointVar) :: tailTypeVar)) {
      val typedCurrent = assume(currentFunVar :: (domainVar ->: tailTypeVar))
      val argTyped = assume(pointVar ∈ domainVar)
      have(thesis) by Tautology.from(
        typedCurrent,
        argTyped,
        arrowElim of (f := currentFunVar, a := domainVar, b := tailTypeVar, x := pointVar)
      )
    }

  lazy val functionBetweenFromTypingGeneral: THM =
    Lemma((currentFunVar :: (domainVar ->: tailTypeVar)) |- Function.functionBetween(currentFunVar)(domainVar)(tailTypeVar)) {
      val typedCurrent = assume(currentFunVar :: (domainVar ->: tailTypeVar))
      have(thesis) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := currentFunVar,
          A := domainVar,
          B := tailTypeVar
        ),
        typedCurrent
      )
    }

  lazy val extensionalityStepGeneral: THM = Lemma(
    (
      leftFunVar :: (domainVar ->: tailTypeVar),
      rightFunVar :: (domainVar ->: tailTypeVar),
      ∀(pointVar, pointVar ∈ domainVar ==> ((leftFunVar * pointVar) === (rightFunVar * pointVar)))
    ) |- (leftFunVar === rightFunVar)
  ) {
    assume(leftFunVar :: (domainVar ->: tailTypeVar))
    assume(rightFunVar :: (domainVar ->: tailTypeVar))
    val pointwiseForall =
      assume(∀(pointVar, pointVar ∈ domainVar ==> ((leftFunVar * pointVar) === (rightFunVar * pointVar))))
    val leftBetween = have(Function.functionBetween(leftFunVar)(domainVar)(tailTypeVar)) by Weakening(
      functionBetweenFromTypingGeneral.of(currentFunVar := leftFunVar)
    )
    val rightBetween = have(Function.functionBetween(rightFunVar)(domainVar)(tailTypeVar)) by Weakening(
      functionBetweenFromTypingGeneral.of(currentFunVar := rightFunVar)
    )
    have(thesis) by Tautology.from(
      BasicTheorems.functionalExtentionality of (
        f := leftFunVar,
        g := rightFunVar,
        A := domainVar,
        B := tailTypeVar
      ),
      leftBetween,
      rightBetween,
      pointwiseForall
    )
  }

  def curriedBeta(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      body: Expr[Ind]
  ): THM = {
    val vars = signature.map(_._1)
    val witness = nestedAbstraction(signature, body)

    def rec(
        remainingSig: Seq[(Variable[Ind], Expr[Ind])],
        remainingVars: Seq[Variable[Ind]],
        current: Expr[Ind]
    ): THM =
      remainingSig match
        case Seq() =>
          Lemma(wellTypedFormula(Seq.empty) |- (current === body)) {
            have(thesis) by Tautology
          }
        case (v, domain) +: tailSig =>
          val tailVars = remainingVars.tail
          val inner = nestedAbstraction(tailSig, body)
          val tailRec = rec(tailSig, tailVars, inner)

          Lemma(wellTypedFormula(remainingSig) |- (appSeq(current)(remainingVars) === body)) {
            val liftedHead = liftEqualityThroughApplications(
              wellTypedFormula(remainingSig),
              betaAtHead(remainingSig, current, v, domain, inner),
              current * v,
              inner,
              tailVars
            )

            val tailTyped = have(wellTypedFormula(remainingSig) |- wellTypedFormula(tailSig)) by
              Restate.from(weakenTailTyping(remainingSig, tailSig))

            val tailEq = have(wellTypedFormula(remainingSig) |- (appSeq(inner)(tailVars) === body)) by Cut(
              tailTyped,
              tailRec
            )

            have(thesis) by Tautology.from(
              altEqualityTransitivity of (
                x := appSeq(current)(remainingVars),
                y := appSeq(inner)(tailVars),
                z := body
              ),
              liftedHead,
              tailEq
            )
          }

    rec(signature, vars, witness)
  }

  def curriedExtensionality(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      resultType: Expr[Ind],
      left: Expr[Ind],
      right: Expr[Ind]
  ): THM = {
    val vars = signature.map(_._1)

    def suffixType(sig: Seq[(Variable[Ind], Expr[Ind])]): Expr[Ind] =
      sig.map(_._2).foldRight[Expr[Ind]](resultType)(_ ->: _)

    def rec(
        remainingSig: Seq[(Variable[Ind], Expr[Ind])],
        remainingVars: Seq[Variable[Ind]],
        currentLeft: Expr[Ind],
        currentRight: Expr[Ind]
    ): THM = {
      val currentType = suffixType(remainingSig)
      val currentSchema =
        forallSeq(
          remainingVars,
          wellTypedFormula(remainingSig) ==> (appSeq(currentLeft)(remainingVars) === appSeq(currentRight)(remainingVars))
        )

      remainingSig match
        case Seq() =>
          Lemma((currentLeft :: currentType, currentRight :: currentType, currentSchema) |- (currentLeft === currentRight)) {
            assume(currentLeft :: currentType)
            assume(currentRight :: currentType)
            assume(currentSchema)
            have(thesis) by Tautology
          }

        case (_, domain) +: tailSig =>
          val pointArg = variable[Ind](s"pointarg${remainingSig.size}")
          val tailVars = remainingVars.tail
          val tailType = suffixType(tailSig)
          val tailRec = rec(tailSig, tailVars, currentLeft * pointArg, currentRight * pointArg)

          Lemma((currentLeft :: currentType, currentRight :: currentType, currentSchema) |- (currentLeft === currentRight)) {
            assume(currentLeft :: currentType)
            assume(currentRight :: currentType)
            val schema = assume(currentSchema)

            have(pointArg ∈ domain |- (currentLeft * pointArg === currentRight * pointArg)) subproof {
              val argTyped = assume(pointArg ∈ domain)

              val leftAppTyped = have((currentLeft * pointArg) :: tailType) by Weakening(
                applicationTypingFromFunctionTypingGeneral.of(
                  currentFunVar := currentLeft,
                  domainVar := domain,
                  tailTypeVar := tailType,
                  pointVar := pointArg
                )
              )
              val rightAppTyped = have((currentRight * pointArg) :: tailType) by Weakening(
                applicationTypingFromFunctionTypingGeneral.of(
                  currentFunVar := currentRight,
                  domainVar := domain,
                  tailTypeVar := tailType,
                  pointVar := pointArg
                )
              )

              val schemaAtHead = schema.statement.right.head match
                case forall(v, phi) =>
                  have(phi.substitute(v := pointArg).asInstanceOf[Expr[Prop]]) by InstantiateForall(pointArg)(schema)
                case _ => throw UnreachableException

              val schemaAtAllVars = have(
                wellTypedFormula(tailSig) ==> (
                  appSeq(currentLeft * pointArg)(tailVars) === appSeq(currentRight * pointArg)(tailVars)
                )
              ) by InstantiateForallSeq(tailVars)(schemaAtHead)

              val tailSchema =
                if tailVars.isEmpty then
                  have(
                    forallSeq(
                      Seq.empty,
                      wellTypedFormula(Seq.empty) ==> ((currentLeft * pointArg) === (currentRight * pointArg))
                    )
                  ) by Tautology.from(schemaAtAllVars, argTyped)
                else
                  have(
                    forallSeq(
                      tailVars,
                      wellTypedFormula(tailSig) ==> (appSeq(currentLeft * pointArg)(tailVars) === appSeq(currentRight * pointArg)(tailVars))
                    )
                  ) subproof {
                    have(
                      wellTypedFormula(tailSig) |- (appSeq(currentLeft * pointArg)(tailVars) === appSeq(currentRight * pointArg)(tailVars))
                    ) subproof {
                      val tailTyped = assume(wellTypedFormula(tailSig))
                      have(appSeq(currentLeft * pointArg)(tailVars) === appSeq(currentRight * pointArg)(tailVars)) by
                        Tautology.from(schemaAtAllVars, argTyped, tailTyped)
                    }
                    thenHave(
                      wellTypedFormula(tailSig) ==> (appSeq(currentLeft * pointArg)(tailVars) === appSeq(currentRight * pointArg)(tailVars))
                    ) by RightImplies
                    thenHave(thesis) by QuantifiersIntro(tailVars)
                  }

              have(currentLeft * pointArg === currentRight * pointArg) by Tautology.from(
                leftAppTyped,
                rightAppTyped,
                tailSchema,
                tailRec
              )
            }

            thenHave(pointArg ∈ domain ==> (currentLeft * pointArg === currentRight * pointArg)) by RightImplies
            val pointwiseForall = thenHave(∀(pointArg, pointArg ∈ domain ==> (currentLeft * pointArg === currentRight * pointArg))) by
              RightForall

            have(thesis) by Cut(
              pointwiseForall,
              extensionalityStepGeneral.of(
                leftFunVar := currentLeft,
                rightFunVar := currentRight,
                domainVar := domain,
                tailTypeVar := tailType
              )
            )
          }
    }

    rec(signature, vars, left, right)
  }
}
