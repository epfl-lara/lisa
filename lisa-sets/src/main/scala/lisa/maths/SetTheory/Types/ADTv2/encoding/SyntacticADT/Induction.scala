package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate

private[encoding] trait SyntacticADTInduction[N <: Arity] extends SyntacticADTTerm[N] {
  this: SyntacticADT[N] =>

  // ************************
  // * STRUCTURAL INDUCTION *
  // ************************

  // Base case used by the internal nat-induction in heightSuccessorStrong.
  private[encoding] lazy val introductionImageAtHeightZeroIsConstructor = Lemma(
    isHeight(h) |-
      inIntroImage(app(h, ∅))(x) ==> isConstructor(x, app(h, ∅))
  ) {
    val isContructorXHEmptySet = isConstructor(x, app(h, ∅))
    val baseCaseLeft = have(isContructorXHEmptySet |- isContructorXHEmptySet) by
      Hypothesis
    val baseCaseRight = have((isHeight(h), in(x, app(h, ∅))) |- ()) by
      Restate.from(heightZero)
    have(
      (isHeight(h), inIntroImage(app(h, ∅))(x)) |-
        isContructorXHEmptySet
    ) by LeftOr(baseCaseLeft, baseCaseRight)
    thenHave(
      isHeight(h) |-
        inIntroImage(app(h, ∅))(x) ==> isContructorXHEmptySet
    ) by RightImplies
  }

  private[encoding] lazy val heightSuccessorStrong = Lemma(
    (isHeight(h), in(n, N)) |-
      in(x, app(h, successor(n))) <=> isConstructor(x, app(h, n))
  ) {
    val forward = have(
      (isHeight(h), in(n, N)) |-
        inIntroImage(app(h, n))(x) ==> isConstructor(x, app(h, n))
    ) subproof {

      def inductionFormula(n: Expr[Ind]): Expr[Prop] =
        inIntroImage(app(h, n))(x) ==> isConstructor(x, app(h, n))
      val inductionFormulaN: Expr[Prop] = inductionFormula(n)
      val inductionFormulaSuccN: Expr[Prop] = inductionFormula(successor(n))

      // STEP 1.1 : Base case
      have(isHeight(h) |- inductionFormula(∅)) by
        Restate.from(introductionImageAtHeightZeroIsConstructor)
      val inductiveCaseRemaining = have(
        (
          isHeight(h),
          forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))
        ) |- forall(n, in(n, N) ==> inductionFormulaN)
      ) by Cut(lastStep, natInduction of (P := lambda(n, inductionFormulaN)))

      // STEP 1.2: Unfolding the definition of subset
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

      // STEP 1.3 : Use monotonicity to prove that y ∈ height(n) => y ∈ height(n + 1)
      have(in(n, N) |- in(successor(n), N)) by Cut(
        successorIsNat,
        equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N))
      )
      have(
        (isHeight(h), in(n, N), subset(n, successor(n))) |-
          subset(app(h, n), app(h, successor(n)))
      ) by Cut(lastStep, heightMonotonic of (n := successor(n), m := n))
      have((isHeight(h), in(n, N)) |- subset(app(h, n), app(h, successor(n)))) by
        Cut(subsetSuccessor, lastStep)
      val liftHeight = have(
        (isHeight(h), in(n, N)) |-
          in(y, app(h, n)) ==> in(y, app(h, successor(n)))
      ) by Cut(lastStep, subsetElimination)

      // STEP 1.4 : Generalize the above result to show that if for some c, x = c(x1, ..., xn) with xi, ..., xj ∈ height(n)
      // then for some c', x = c'(x1, ..., xn) with xi, ..., xj ∈ height(n + 1).

      // Caching
      val isConstructorXHN = isConstructor(x, app(h, n))
      val isConstructorXHSuccN = isConstructor(x, app(h, successor(n)))
      val liftConstructorHeight =
        if constructors.size == 0 then
          have(
            (isHeight(h), in(n, N), isConstructorXHN) |- isConstructorXHSuccN
          ) by Restate
        else
          val liftConstructorHeightOrSequence =
            for c <- constructors yield

              // Caching
              val isConstructorCXHN = isConstructor(c, x, app(h, n))
              val isConstructorCXHSuccN = isConstructor(c, x, app(h, successor(n)))
              val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
              val constructorVarsInHSuccN =
                constructorVarsInDomain(c, app(h, successor(n)))

              if c.arity == 0 then
                have(
                  (isHeight(h), in(n, N), isConstructorCXHN) |-
                    isConstructorCXHSuccN
                ) by Restate
              else
                val liftHeightAndSequence =
                  for (v, ty) <- c.signature
                  yield have(
                    (isHeight(h), in(n, N), constructorVarsInHN) |-
                      in(v, ty.getOrElse(app(h, successor(n))))
                  ) by Weakening(liftHeight of (y := v))

                val left = have(
                  (isHeight(h), in(n, N), constructorVarsInHN) |-
                    constructorVarsInHSuccN
                ) by RightAnd(liftHeightAndSequence*)
                val right = have(x === c.term |- x === c.term) by Hypothesis

                have(
                  (isHeight(h), in(n, N), constructorVarsInHN, (x === c.term)) |-
                    constructorVarsInHSuccN /\ (x === c.term)
                ) by RightAnd(left, right)
                thenHave(
                  (
                    isHeight(h),
                    in(n, N),
                    constructorVarsInHN /\ (x === c.term)
                  ) |- constructorVarsInHSuccN /\ (x === c.term)
                ) by LeftAnd
                thenHave(
                  (
                    isHeight(h),
                    in(n, N),
                    constructorVarsInHN /\ (x === c.term)
                  ) |- isConstructorCXHSuccN
                ) by QuantifiersIntro(c.variables)
                thenHave(
                  (isHeight(h), in(n, N), isConstructorCXHN) |-
                    isConstructorCXHSuccN
                ) by QuantifiersIntro(c.variables)

              thenHave(
                (isHeight(h), in(n, N), isConstructorCXHN) |-
                  isConstructorXHSuccN
              ) by Weakening

          have(
            (isHeight(h), in(n, N), isConstructorXHN) |- isConstructorXHSuccN
          ) by LeftOr(liftConstructorHeightOrSequence*)

      // STEP 1.5: Show that x ∈ introductionFunction(height(n + 1)) => for some c, x = c(x1, ..., xn)
      // with xi, ..., xj ∈ height(n + 1).
      val heightSuccessorWeakForward = have(
        (isHeight(h), in(n, N), in(x, app(h, successor(n)))) |-
          inIntroImage(app(h, n))(x)
      ) by Cut(
        heightSuccessorWeak,
        equivalenceApply of
          (
            p1 := in(x, app(h, successor(n))),
            p2 := inIntroImage(app(h, n))(x)
          )
      )
      have(
        (inductionFormulaN, inIntroImage(app(h, n))(x)) |-
          isConstructorXHN
      ) by Restate
      have(
        (
          isHeight(h),
          in(n, N),
          in(x, app(h, successor(n))),
          inductionFormulaN
        ) |- isConstructorXHN
      ) by Cut(heightSuccessorWeakForward, lastStep)
      val right = have(
        (
          isHeight(h),
          in(n, N),
          in(x, app(h, successor(n))),
          inductionFormulaN
        ) |- isConstructorXHSuccN
      ) by Cut(lastStep, liftConstructorHeight)
      val left = have(isConstructorXHSuccN |- isConstructorXHSuccN) by Hypothesis
      have(
        (
          isHeight(h),
          in(n, N),
          inductionFormulaN,
          inIntroImage(app(h, successor(n)))(x)
        ) |- isConstructorXHSuccN
      ) by LeftOr(left, right)

      // STEP 1.6: Conclude
      thenHave(
        (isHeight(h), in(n, N), inductionFormulaN) |- inductionFormulaSuccN
      ) by RightImplies
      thenHave(
        (isHeight(h), in(n, N)) |- inductionFormulaN ==> inductionFormulaSuccN
      ) by RightImplies
      thenHave(
        isHeight(h) |- in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)
      ) by RightImplies
      thenHave(
        isHeight(h) |-
          forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))
      ) by RightForall
      have(isHeight(h) |- forall(n, in(n, N) ==> inductionFormulaN)) by
        Cut(lastStep, inductiveCaseRemaining)
      thenHave(isHeight(h) |- in(n, N) ==> inductionFormulaN) by
        InstantiateForall(n)
    }

    // STEP 2: Prove the backward implication
    val backward = have(
      (isHeight(h), in(n, N)) |-
        isConstructor(x, app(h, n)) ==> inIntroImage(app(h, n))(x)
    ) by Restate

    // STEP 3: Conclude
    have(
      (isHeight(h), in(n, N)) |-
        inIntroImage(app(h, n))(x) <=> isConstructor(x, app(h, n))
    ) by RightIff(forward, backward)
    have(thesis) by Tautology.from(equivalenceRewriting, lastStep, heightSuccessorWeak)
  }

  lazy val inductiveCase: Map[SyntacticConstructor, Expr[Prop]] = constructors.map(c =>
    c -> c.signature.foldRight[Expr[Prop]](P(c.term))((el, fc) =>
      val (v, ty) = el
      ty match
        case SelfRef => forall(v, in(v, term) ==> (P(v) ==> fc))
        case RegularArg(tpe) => forall(v, in(v, typeExprToTerm(tpe)) ==> fc)
    )
  ).toMap

  val induction = Lemma(using name = s"ADT_${name}_induction")(
    constructors.foldRight[Expr[Prop]](forall(x, in(x, term) ==> P(x)))((c, f) =>
      inductiveCase(c) ==> f
    )
  ) {
    // List of cases to prove for structural induction to hold
    val structuralInductionPreconditions: Expr[Prop] =
      seqAnd(constructors.map(inductiveCase))

    // We want to prove the claim by induction on the height of n, i.e. prove that for any
    // n in N, P holds.
    def inductionFormula(n: Expr[Ind]): Expr[Prop] = forall(x, in(x, app(h, n)) ==> P(x))
    val inductionFormulaN: Expr[Prop] = inductionFormula(n)

    // STEP 1: Prove the base case
    have(isHeight(h) |- in(x, app(h, ∅)) ==> P(x)) by Weakening(heightZero)
    val zeroCase = thenHave(isHeight(h) |- inductionFormula(∅)) by RightForall

    val inductiveCaseRemaining = have(
      (
        isHeight(h),
        forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n))))
      ) |- forall(n, in(n, N) ==> inductionFormulaN)
    ) by Cut(zeroCase, natInduction of (P := lam(n, inductionFormulaN)))

    // STEP 2: Prove the inductive case
    val succCase = have(
      (isHeight(h), structuralInductionPreconditions) |-
        forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n))))
    ) subproof {

      // STEP 2.1 : Prove that if the x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n) then P(x) holds.
      val isConstructorImpliesP = have(
        (
          isHeight(h),
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN,
          isConstructor(x, app(h, n))
        ) |- P(x)
      ) subproof {

        if constructors.isEmpty then have(thesis) by Restate
        else
          val orSeq = (for c <- constructors yield

            // Caching
            val constructorPrecondition = inductiveCase(c)
            val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
            val constructorVarsInHNEx =
              ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
            val constructorVarsInTerm = constructorVarsInDomain(c, term)

            // STEP 2.1.1: Prove that if xi, ..., xj ∈ height(n) then xi, ..., xj ∈ ADT.
            val constructorQuantVarsInHNToTerm = have(
              (isHeight(h), in(n, N), constructorVarsInHN) |-
                constructorVarsInTerm
            ) subproof {
              have(
                (isHeight(h), in(n, N), constructorVarsInHN) |-
                  in(n, N) /\ constructorVarsInHN
              ) by Restate
              val consVarL = thenHave(
                (isHeight(h), in(n, N), constructorVarsInHN) |-
                  constructorVarsInHNEx
              ) by RightExists
              have(
                (
                  constructorVarsInTerm <=> constructorVarsInHNEx,
                  constructorVarsInHNEx
                ) |- constructorVarsInTerm
              ) by Restate.from(
                equivalenceRevApply of
                  (p1 := constructorVarsInTerm, p2 := constructorVarsInHNEx)
              )
              have(
                (isHeight(h), constructorVarsInHNEx) |- constructorVarsInTerm
              ) by Cut(termsHaveHeight(c), lastStep)
              have(thesis) by Cut(consVarL, lastStep)
            }

            // STEP 2.1.2: Prove that if xi, ..., xj ∈ height(n) then P(c(x1, ..., xn)).
            val constructorVarsInHNImpliesPCTerm = have(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN
              ) |- P(c.term)
            ) subproof {
              have(
                (
                  isHeight(h),
                  constructorPrecondition,
                  in(n, N),
                  inductionFormulaN,
                  constructorVarsInHN
                ) |- constructorPrecondition
              ) by Restate

              c.signature.foldLeft(lastStep)((fact, el) =>
                val (v, ty) = el

                fact.statement.right.head match
                  case forall(_, factCclWithoutForall) =>
                    thenHave(
                      (
                        isHeight(h),
                        constructorPrecondition,
                        in(n, N),
                        inductionFormulaN,
                        constructorVarsInHN
                      ) |- factCclWithoutForall
                    ) by InstantiateForall(v)

                    factCclWithoutForall match
                      case implies(membership, subformula) => ty match
                          case SelfRef => subformula match
                              case implies(hypothesis, subSubFormula) =>
                                val proofSubSubFormula = thenHave(
                                  (
                                    isHeight(h),
                                    constructorPrecondition,
                                    in(n, N),
                                    inductionFormulaN,
                                    constructorVarsInTerm,
                                    constructorVarsInHN,
                                    P(v)
                                  ) |- subSubFormula
                                ) by Weakening

                                have(inductionFormulaN |- inductionFormulaN) by Hypothesis
                                thenHave(
                                  inductionFormulaN |- in(v, app(h, n)) ==> P(v)
                                ) by InstantiateForall(v)
                                thenHave(
                                  (inductionFormulaN, constructorVarsInHN) |- P(v)
                                ) by Weakening

                                have(
                                  (
                                    isHeight(h),
                                    constructorPrecondition,
                                    in(n, N),
                                    inductionFormulaN,
                                    constructorVarsInTerm,
                                    constructorVarsInHN
                                  ) |- subSubFormula
                                ) by Cut(lastStep, proofSubSubFormula)
                                have(
                                  (
                                    isHeight(h),
                                    constructorPrecondition,
                                    in(n, N),
                                    inductionFormulaN,
                                    constructorVarsInHN
                                  ) |- subSubFormula
                                ) by Cut(constructorQuantVarsInHNToTerm, lastStep)

                              case _ => throw UnreachableException

                          case RegularArg(_) => thenHave(
                              (
                                isHeight(h),
                                constructorPrecondition,
                                in(n, N),
                                inductionFormulaN,
                                constructorVarsInHN
                              ) |- subformula
                            ) by Restate
                      case _ => throw UnreachableException
                  case _ => throw UnreachableException
              )

              thenHave(thesis) by Restate
            }

            have(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN
              ) |- P(c.term)
            ) by Restate.from(constructorVarsInHNImpliesPCTerm)

            // STEP 2.1.3: Prove that if xi, ..., xj ∈ height(n) then P(x).
            thenHave(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN,
                x === c.term
              ) |- P(x)
            ) by RightSubstEq.withParameters(List((x, c.term)), (Seq(x), P(x)))

            thenHave(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN /\ (x === c.term)
              ) |- P(x)
            ) by LeftAnd

            thenHave(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                isConstructor(c, x, app(h, n))
              ) |- P(x)
            ) by QuantifiersIntro(c.variables)
            thenHave(
              (
                isHeight(h),
                structuralInductionPreconditions,
                in(n, N),
                inductionFormulaN,
                isConstructor(c, x, app(h, n))
              ) |- P(x)
            ) by Weakening
          ).toSeq

          have(
            (
              isHeight(h),
              structuralInductionPreconditions,
              in(n, N),
              inductionFormulaN,
              isConstructor(x, app(h, n))
            ) |- P(x)
          ) by LeftOr(orSeq*)
      }

      // STEP 2.2: Prove that if x ∈ height(n + 1) then P(x) holds.
      have(
        (isHeight(h), in(n, N), in(x, app(h, successor(n)))) |-
          isConstructor(x, app(h, n))
      ) by Cut(
        heightSuccessorStrong,
        equivalenceApply of
          (p1 := in(x, app(h, successor(n))), p2 := isConstructor(x, app(h, n)))
      )
      have(
        (
          isHeight(h),
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN,
          in(x, app(h, successor(n)))
        ) |- P(x)
      ) by Cut(lastStep, isConstructorImpliesP)

      // STEP 2.3: Conclude
      thenHave(
        (
          isHeight(h),
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN
        ) |- in(x, app(h, successor(n))) ==> P(x)
      ) by RightImplies

      thenHave(
        (
          isHeight(h),
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN
        ) |- inductionFormula(successor(n))
      ) by RightForall
      thenHave(
        (isHeight(h), structuralInductionPreconditions, in(n, N)) |-
          inductionFormulaN ==> inductionFormula(successor(n))
      ) by RightImplies
      thenHave(
        (isHeight(h), structuralInductionPreconditions) |-
          in(n, N) ==> (inductionFormulaN ==> inductionFormula(successor(n)))
      ) by RightImplies
      thenHave(thesis) by RightForall
    }

    // STEP 3: Conclude

    have(
      (isHeight(h), structuralInductionPreconditions) |-
        forall(n, in(n, N) ==> inductionFormulaN)
    ) by Cut(lastStep, inductiveCaseRemaining)
    thenHave(
      (isHeight(h), structuralInductionPreconditions) |-
        in(n, N) ==> inductionFormulaN
    ) by InstantiateForall(n)
    thenHave(
      (isHeight(h), structuralInductionPreconditions, in(n, N)) |-
        inductionFormulaN
    ) by Restate
    thenHave(
      (isHeight(h), structuralInductionPreconditions, in(n, N)) |-
        in(x, app(h, n)) ==> P(x)
    ) by InstantiateForall(x)
    thenHave(
      (
        isHeight(h),
        structuralInductionPreconditions,
        in(n, N) /\ in(x, app(h, n))
      ) |- P(x)
    ) by Restate
    val exImpliesP = thenHave(
      (
        isHeight(h),
        structuralInductionPreconditions,
        exists(n, in(n, N) /\ in(x, app(h, n)))
      ) |- P(x)
    ) by LeftExists
    have(
      (isHeight(h), in(x, term)) |- exists(n, in(n, N) /\ in(x, app(h, n)))
    ) by Cut(
      termHasHeight,
      equivalenceApply of
        (p1 := in(x, term), p2 := exists(n, in(n, N) /\ in(x, app(h, n))))
    )

    have((isHeight(h), structuralInductionPreconditions, in(x, term)) |- P(x)) by
      Cut(lastStep, exImpliesP)
    thenHave(
      (exists(h, isHeight(h)), structuralInductionPreconditions, in(x, term)) |-
        P(x)
    ) by LeftExists
    have((structuralInductionPreconditions, in(x, term)) |- P(x)) by
      Cut(heightExists, lastStep)
    thenHave(structuralInductionPreconditions |- in(x, term) ==> P(x)) by RightImplies
    thenHave(structuralInductionPreconditions |- forall(x, in(x, term) ==> P(x))) by
      RightForall
    thenHave(thesis) by Restate
  }
}
