package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.encoding.SyntacticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*

final class HeightConstructors[N <: Arity](
  base: HeightADT[N],
  constructors: Seq[SyntacticConstructor],
  isConstructor: Expr[Ind >>: Ind >>: Prop]
) {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    base.inIntroImage(s)(y)

  private def constructorPredicate(
      c: SyntacticConstructor,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables2, wellTypedFormula(c.signature2)(s) /\ (x === c.term2))

  /**
   *  Lemma --- The introduction function is monotonic with respect to set inclusion.
   *
   *  `s ⊆ t |- introductionFunction(s) ⊆ introductionFunction(t)`
   */
  private[ADTv2] val introductionFunctionMononotic = Lemma(
    subset(s, t) |-
      inIntroImage(s)(x) ==> inIntroImage(t)(x)
  ) {
    val subsetST = s ⊆ t
    val isConstructorXS = isConstructor(x)(s)
    val isConstructorXT = isConstructor(x)(t)

    have(s ⊆ t |- forall(z, in(z, s) ==> in(z, t))) by
      Congruence.from(subsetAxiom of (x := s, y := t))
    val subsetElimination = thenHave(s ⊆ t |- in(z, s) ==> in(z, t)) by
      InstantiateForall(z)

    val isConstructorXSImpliesT =
      for c <- constructors yield
        val labelEq = x === c.term2
        val isConstructorCXS = constructorPredicate(c, x, s)
        val isConstructorCXT = constructorPredicate(c, x, t)
        val varsWellTypedS = wellTypedFormula(c.signature2)(s)
        val varsWellTypedT = wellTypedFormula(c.signature2)(t)

        if c.arity == 0 then
          have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
        else
          val andSeq =
            for (v, ty) <- c.signature2
            yield have((subsetST, varsWellTypedS) |- in(v, ty.getOrElse(t))) by
              Weakening(subsetElimination of (z := v))
          val expandingDomain = have((subsetST, varsWellTypedS) |- varsWellTypedT) by
            RightAnd(andSeq*)
          val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
          have((subsetST, varsWellTypedS, labelEq) |- varsWellTypedT /\ labelEq) by
            RightAnd(expandingDomain, weakeningLabelEq)

          val existsCXS = existsSeq(c.variables2, varsWellTypedS /\ labelEq)
          val existsCXT = existsSeq(c.variables2, varsWellTypedT /\ labelEq)

          thenHave((subsetST, varsWellTypedS, labelEq) |- existsCXT) by
            QuantifiersIntro(c.variables2)
          thenHave((subsetST, varsWellTypedS /\ labelEq) |- existsCXT) by LeftAnd
          thenHave((subsetST, existsCXS) |- existsCXT) by QuantifiersIntro(c.variables2)
          thenHave((subsetST, isConstructorCXS) |- isConstructorXT) by Weakening

    val constructorBranch =
      if constructors.isEmpty then
        have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
      else
        have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(
          isConstructorXSImpliesT*
        )

    val constructorCase = thenHave((subsetST, isConstructorXS) |- inIntroImage(t)(x)) by
      Weakening

    val subsetEliminationX = have(s ⊆ t |- in(x, s) ==> in(x, t)) by
      Restate.from(subsetElimination of (z := x))
    have((subsetST, in(x, s)) |- in(x, t)) by Tautology.from(subsetEliminationX)
    val membershipCase = thenHave((subsetST, in(x, s)) |- inIntroImage(t)(x)) by
      Weakening

    have((subsetST, inIntroImage(s)(x)) |- inIntroImage(t)(x)) by
      Tautology.from(constructorCase, membershipCase)
    thenHave(thesis) by RightImplies
  }

  private val introFunctionMonoHyp: THM = Lemma(
    forall(
      s,
      forall(t, subset(s, t) ==> forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x)))
    )
  ) {
    have(introductionFunctionMononotic.statement) by
      Restate.from(introductionFunctionMononotic)
    thenHave(subset(s, t) |- forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))) by
      RightForall
    thenHave(subset(s, t) ==> forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x))) by
      RightImplies
    thenHave(
      forall(t, subset(s, t) ==> forall(x, inIntroImage(s)(x) ==> inIntroImage(t)(x)))
    ) by RightForall
    thenHave(thesis) by RightForall
  }

  /**
   *  Lemma --- The extended introduction function is monotonic with respect to set
   *  inclusion.
   */
  private[ADTv2] val extIntroMonotonic = Lemma(
    subset(f, g) |-
      base.inExtIntroImage(f)(x) ==>
      base.inExtIntroImage(g)(x)
  ) {
    have(thesis) by Tautology.from(
      introFunctionMonoHyp,
      HeightKernel.extIntroMonotonic of (HeightKernel.isConstructor := isConstructor)
    )
  }

  /**
   *  Lemma --- The height function is monotonic.
   */
  val heightMonotonic = Lemma(
    (base.isHeight(h), in(n, N), in(m, N), subset(m, n)) |- subset(app(h, m), app(h, n))
  ) {
    have(thesis) by Tautology.from(
      base.heightIsCore,
      introFunctionMonoHyp,
      HeightKernel.heightMonotonic of (HeightKernel.isConstructor := isConstructor)
    )
  }

  /**
   *  Lemma --- The set of elements of height n + 1 is the introduction image of height n.
   */
  val heightSuccessorWeak = Lemma(
    (base.isHeight(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> inIntroImage(app(h, n))(x)
  ) {
    have(thesis) by Tautology.from(
      base.heightIsCore,
      introFunctionMonoHyp,
      HeightKernel.heightSuccessorWeak of (HeightKernel.isConstructor := isConstructor)
    )
  }

  /**
   *  Lemma --- Every constructor is in the image of the introduction function.
   */
  private[ADTv2] val constructorIsInIntroductionFunction = constructors.map(c =>
    val constructorVarsInDomainCS = wellTypedFormula(c.signature)(s)

    c -> Lemma(constructorVarsInDomainCS |- inIntroImage(s)(c.term)) {
      have(
        constructorVarsInDomainCS |- constructorVarsInDomainCS /\ (c.term === c.term)
      ) by Restate

      c.variables2.foldRight((c.variables1, List[Variable[Ind]]()))((v, acc) =>
        val oldVariables = acc._1.init
        val newVariables = v :: acc._2
        val vars = oldVariables ++ newVariables

        thenHave(
          constructorVarsInDomainCS |- existsSeq(
            newVariables,
            wellTypedFormula(vars.zip(c.specification))(s) /\ (c.term === c.term(vars))
          )
        ) by RightExists

        (oldVariables, newVariables)
      )

      thenHave(constructorVarsInDomainCS |- inIntroImage(s)(c.term)) by Weakening
    }
  ).toMap

  /**
   *  Base case used by the internal nat induction in heightSuccessorStrong.
   */
  private[ADTv2] lazy val introductionImageAtHeightZeroIsConstructor = Lemma(
    base.isHeight(h) |-
      inIntroImage(app(h, ∅))(x) ==> isConstructor(x)(app(h, ∅))
  ) {
    val isContructorXHEmptySet = isConstructor(x)(app(h, ∅))
    val baseCaseLeft = have(isContructorXHEmptySet |- isContructorXHEmptySet) by
      Hypothesis
    val baseCaseRight = have((base.isHeight(h), in(x, app(h, ∅))) |- ()) by
      Restate.from(base.heightZero)
    have((base.isHeight(h), inIntroImage(app(h, ∅))(x)) |- isContructorXHEmptySet) by
      LeftOr(baseCaseLeft, baseCaseRight)
    thenHave(
      base.isHeight(h) |-
        inIntroImage(app(h, ∅))(x) ==> isContructorXHEmptySet
    ) by RightImplies
  }

  private[ADTv2] lazy val heightSuccessorStrong = Lemma(
    (base.isHeight(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> isConstructor(x)(app(h, n))
  ) {
    val forward = have(
      (base.isHeight(h), in(n, N)) |-
        inIntroImage(app(h, n))(x) ==> isConstructor(x)(app(h, n))
    ) subproof {

      def inductionFormula(n: Expr[Ind]): Expr[Prop] =
        inIntroImage(app(h, n))(x) ==> isConstructor(x)(app(h, n))
      val inductionFormulaN: Expr[Prop] = inductionFormula(n)
      val inductionFormulaSuccN: Expr[Prop] = inductionFormula(successor(n))

      have(base.isHeight(h) |- inductionFormula(∅)) by
        Restate.from(introductionImageAtHeightZeroIsConstructor)
      val inductiveCaseRemaining = have(
        (
          base.isHeight(h),
          forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))
        ) |- forall(n, in(n, N) ==> inductionFormulaN)
      ) by Cut(lastStep, natInduction of (P := lambda(n, inductionFormulaN)))

      have(
        subset(app(h, n), app(h, successor(n))) |-
          forall(z, in(z, app(h, n)) ==> in(z, app(h, successor(n))))
      ) by Cut(
        subsetAxiom of (x := app(h, n), y := app(h, successor(n))),
        equivalenceApply of
          (
            p1 := subset(app(h, n), app(h, successor(n))),
            p2 := forall(z, in(z, app(h, n)) ==> in(z, app(h, successor(n))))
          )
      )
      val subsetElimination = thenHave(
        subset(app(h, n), app(h, successor(n))) |-
          in(y, app(h, n)) ==> in(y, app(h, successor(n)))
      ) by InstantiateForall(y)

      have(in(n, N) |- in(successor(n), N)) by Cut(
        successorIsNat,
        equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N))
      )
      have(
        (base.isHeight(h), in(n, N), subset(n, successor(n))) |-
          subset(app(h, n), app(h, successor(n)))
      ) by Cut(lastStep, heightMonotonic of (n := successor(n), m := n))
      have((base.isHeight(h), in(n, N)) |- subset(app(h, n), app(h, successor(n)))) by
        Cut(subsetSuccessor, lastStep)
      val liftHeight = have(
        (base.isHeight(h), in(n, N)) |-
          in(y, app(h, n)) ==> in(y, app(h, successor(n)))
      ) by Cut(lastStep, subsetElimination)

      val isConstructorXHN0 = isConstructor(x)(app(h, n))
      val isConstructorXHSuccN = isConstructor(x)(app(h, successor(n)))
      val liftConstructorHeight =
        if constructors.isEmpty then
          have((base.isHeight(h), in(n, N), isConstructorXHN0) |- isConstructorXHSuccN) by
            Restate
        else
          val liftConstructorHeightOrSequence =
            for c <- constructors yield
              val isConstructorCXHN = constructorPredicate(c, x, app(h, n))
              val isConstructorCXHSuccN = constructorPredicate(c, x, app(h, successor(n)))
              val constructorVarsInHN = wellTypedFormula(c.signature2)(app(h, n))
              val constructorVarsInHSuccN =
                wellTypedFormula(c.signature2)(app(h, successor(n)))

              if c.arity == 0 then
                have(
                  (base.isHeight(h), in(n, N), isConstructorCXHN) |-
                    isConstructorCXHSuccN
                ) by Restate
              else
                val liftHeightAndSequence =
                  for (v, ty) <- c.signature2
                  yield have(
                    (base.isHeight(h), in(n, N), constructorVarsInHN) |-
                      in(v, ty.getOrElse(app(h, successor(n))))
                  ) by Weakening(liftHeight of (y := v))

                val left = have(
                  (base.isHeight(h), in(n, N), constructorVarsInHN) |-
                    constructorVarsInHSuccN
                ) by RightAnd(liftHeightAndSequence*)
                val right = have(x === c.term2 |- x === c.term2) by Hypothesis

                have(
                  (base.isHeight(h), in(n, N), constructorVarsInHN, (x === c.term2)) |-
                    constructorVarsInHSuccN /\ (x === c.term2)
                ) by RightAnd(left, right)
                thenHave(
                  (
                    base.isHeight(h),
                    in(n, N),
                    constructorVarsInHN /\ (x === c.term2)
                  ) |- constructorVarsInHSuccN /\ (x === c.term2)
                ) by LeftAnd
                thenHave(
                  (
                    base.isHeight(h),
                    in(n, N),
                    constructorVarsInHN /\ (x === c.term2)
                  ) |- isConstructorCXHSuccN
                ) by QuantifiersIntro(c.variables2)
                thenHave(
                  (base.isHeight(h), in(n, N), isConstructorCXHN) |-
                    isConstructorCXHSuccN
                ) by QuantifiersIntro(c.variables2)

              thenHave(
                (base.isHeight(h), in(n, N), isConstructorCXHN) |-
                  isConstructorXHSuccN
              ) by Weakening

          have(
            (base.isHeight(h), in(n, N), isConstructorXHN0) |- isConstructorXHSuccN
          ) by LeftOr(liftConstructorHeightOrSequence*)

      val heightSuccessorWeakForward = have(
        (base.isHeight(h), in(n, N), in(x, app(h, successor(n)))) |-
          inIntroImage(app(h, n))(x)
      ) by Cut(
        heightSuccessorWeak,
        equivalenceApply of
          (
            p1 := in(x, app(h, successor(n))),
            p2 := inIntroImage(app(h, n))(x)
          )
      )
      have((inductionFormulaN, inIntroImage(app(h, n))(x)) |- isConstructorXHN0) by Restate
      have(
        (
          base.isHeight(h),
          in(n, N),
          in(x, app(h, successor(n))),
          inductionFormulaN
        ) |- isConstructorXHN0
      ) by Cut(heightSuccessorWeakForward, lastStep)
      val right = have(
        (
          base.isHeight(h),
          in(n, N),
          in(x, app(h, successor(n))),
          inductionFormulaN
        ) |- isConstructorXHSuccN
      ) by Cut(lastStep, liftConstructorHeight)
      val left = have(isConstructorXHSuccN |- isConstructorXHSuccN) by Hypothesis
      have(
        (
          base.isHeight(h),
          in(n, N),
          inductionFormulaN,
          inIntroImage(app(h, successor(n)))(x)
        ) |- isConstructorXHSuccN
      ) by LeftOr(left, right)

      thenHave(
        (base.isHeight(h), in(n, N), inductionFormulaN) |- inductionFormulaSuccN
      ) by RightImplies
      thenHave(
        (base.isHeight(h), in(n, N)) |- inductionFormulaN ==> inductionFormulaSuccN
      ) by RightImplies
      thenHave(
        base.isHeight(h) |- in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)
      ) by RightImplies
      thenHave(
        base.isHeight(h) |-
          forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))
      ) by RightForall
      have(base.isHeight(h) |- forall(n, in(n, N) ==> inductionFormulaN)) by
        Cut(lastStep, inductiveCaseRemaining)
      thenHave(base.isHeight(h) |- in(n, N) ==> inductionFormulaN) by
        InstantiateForall(n)
    }

    val backward = have(
      (base.isHeight(h), in(n, N)) |-
        isConstructor(x)(app(h, n)) ==> inIntroImage(app(h, n))(x)
    ) by Restate

    have(
      (base.isHeight(h), in(n, N)) |-
        inIntroImage(app(h, n))(x) <=> isConstructor(x)(app(h, n))
    ) by RightIff(forward, backward)
    have(thesis) by Tautology.from(equivalenceRewriting, lastStep, heightSuccessorWeak)
  }
}
