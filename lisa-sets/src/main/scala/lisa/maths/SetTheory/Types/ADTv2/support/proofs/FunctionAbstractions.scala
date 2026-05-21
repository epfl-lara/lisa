package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Pi.{Pi, ->:}
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity, funEqDef}
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.TypingRules.{BetaReduction, TAbs}
import lisa.utils.prooflib.BasicStepTactic.Restate

object FunctionAbstractions {

  private val domainVar = variable[Ind]("domain")
  private val codomainVar = variable[Ind]("codomain")
  private val bodyVar = variable[Ind >>: Ind]("body")
  private val pointVar = variable[Ind]("point")

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
    ∀(x ∈ domain, body(x) ∈ codomain) |- abs(domain)(body) ∈ Pi(domain)(λ(y, codomain))
  ) {
    have(thesis) by Restate.from(
      TAbsConstOnGeneral.of(
        domainVar := domain,
        codomainVar := codomain,
        bodyVar := body
      )
    )
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

  private def applicationTypingFromFunctionTyping(
      current: Expr[Ind],
      currentType: Expr[Ind],
      domain: Expr[Ind],
      tailType: Expr[Ind],
      pointArg: Variable[Ind]
  ): THM = Lemma((current :: currentType, pointArg ∈ domain) |- ((current * pointArg) :: tailType)) {
    val typedCurrent = assume(current :: currentType)
    val argTyped = assume(pointArg ∈ domain)
    have(thesis) by Tautology.from(
      typedCurrent,
      argTyped,
      funEqDef of (f := current, a := domain, b := tailType, x := pointArg)
    )
  }

  private def functionBetweenFromTyping(
      current: Expr[Ind],
      domain: Expr[Ind],
      tailType: Expr[Ind],
      currentType: Expr[Ind]
  ): THM = Lemma((current :: currentType) |- Function.functionBetween(current)(domain)(tailType)) {
    val typedCurrent = assume(current :: currentType)
    have(thesis) by Tautology.from(
      BasicTheorems.funcBetweenEqInFuncSpace of (
        f := current,
        A := domain,
        B := tailType
      ),
      typedCurrent
    )
  }

  private def extensionalityStep(
      currentLeft: Expr[Ind],
      currentRight: Expr[Ind],
      domain: Expr[Ind],
      tailType: Expr[Ind],
      currentType: Expr[Ind],
      pointwiseFormula: Expr[Prop]
  ): THM = Lemma(
    (currentLeft :: currentType, currentRight :: currentType, pointwiseFormula) |- (currentLeft === currentRight)
  ) {
    val leftTyped = assume(currentLeft :: currentType)
    val rightTyped = assume(currentRight :: currentType)
    val pointwiseForall = assume(pointwiseFormula)
    val leftBetween = have(Function.functionBetween(currentLeft)(domain)(tailType)) by Weakening(
      functionBetweenFromTyping(currentLeft, domain, tailType, currentType)
    )
    val rightBetween = have(Function.functionBetween(currentRight)(domain)(tailType)) by Weakening(
      functionBetweenFromTyping(currentRight, domain, tailType, currentType)
    )
    have(thesis) by Tautology.from(
      BasicTheorems.functionalExtentionality of (
        f := currentLeft,
        g := currentRight,
        A := domain,
        B := tailType
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
            val leftTyped = assume(currentLeft :: currentType)
            val rightTyped = assume(currentRight :: currentType)
            val schema = assume(currentSchema)

            val pointwiseAtArg = have(pointArg ∈ domain |- (currentLeft * pointArg === currentRight * pointArg)) subproof {
              val argTyped = assume(pointArg ∈ domain)

              val leftAppTyped = have((currentLeft * pointArg) :: tailType) by Weakening(
                applicationTypingFromFunctionTyping(currentLeft, currentType, domain, tailType, pointArg)
              )
              val rightAppTyped = have((currentRight * pointArg) :: tailType) by Weakening(
                applicationTypingFromFunctionTyping(currentRight, currentType, domain, tailType, pointArg)
              )

              val schemaAtHead = schema.statement.right.head match
                case forall(v, phi) =>
                  have(phi.substitute(v := pointArg).asInstanceOf[Expr[Prop]]) by InstantiateForall(pointArg)(schema)
                case _ => throw UnreachableException

              val schemaAtAllVars = tailVars.foldLeft(schemaAtHead) { (fact, arg) =>
                fact.statement.right.head match
                  case forall(v, phi) =>
                    have(phi.substitute(v := arg).asInstanceOf[Expr[Prop]]) by InstantiateForall(arg)(fact)
                  case _ => fact
              }

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
              extensionalityStep(
                currentLeft,
                currentRight,
                domain,
                tailType,
                currentType,
                pointwiseForall.statement.right.head
              )
            )
          }
    }

    rec(signature, vars, left, right)
  }
}
