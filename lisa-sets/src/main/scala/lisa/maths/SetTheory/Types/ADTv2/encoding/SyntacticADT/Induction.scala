package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.natInduction
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTInduction[N <: Arity] extends SyntacticADTTerm[N] {
  this: SyntacticADT[N] =>

  // ************************
  // * STRUCTURAL INDUCTION *
  // ************************

  lazy val inductiveCase: Map[SyntacticConstructor, Expr[Prop]] = constructors.map(c =>
    c -> c.signature.foldRight[Expr[Prop]](P(c.term))((el, fc) =>
      val (v, ty) = el
      ty match
        case SelfRef => forall(v, in(v, term) ==> (P(v) ==> fc))
        // case RegularArg(tpe) => forall(v, in(v, typeExprToTerm(tpe)) ==> fc)
        case TypeArg(typeName) => forall(v, in(v, typeExprToTerm(typeName)) ==> fc)
    )
  ).toMap

  val induction = Time.measure("ADT induction")(Lemma(using name = s"${name}/induction")(
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
        forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(S(n))))
      ) |- forall(n, in(n, N) ==> inductionFormulaN)
    ) by Cut(zeroCase, natInduction of (P := lam(n, inductionFormulaN)))

    // STEP 2: Prove the inductive case
    have(
      (isHeight(h), structuralInductionPreconditions) |-
        forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormula(S(n))))
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
            val constructorVarsInHN = wellTypedFormula(c.signature2)(app(h, n))
            val constructorVarsInTerm = wellTypedFormula(c.signature2)(term)

            // STEP 2.1.1: Prove that if xi, ..., xj ∈ height(n) then xi, ..., xj ∈ ADT.
            val constructorQuantVarsInHNToTerm = have(
              (isHeight(h), in(n, N), constructorVarsInHN) |-
                constructorVarsInTerm
            ) subproof {
              val andSeq = c.signature2.map((v, ty) =>
                ty match
                  case SelfRef =>
                    val vInHeight =
                      (∃(n, in(n, N) /\ in(x, app(h, n)))).substitute(x := v)
                    val nInN = have(
                      (isHeight(h), in(n, N), in(v, app(h, n))) |- in(n, N)
                    ) by Restate
                    val vInHN = have(
                      (isHeight(h), in(n, N), in(v, app(h, n))) |-
                        in(v, app(h, n))
                    ) by Restate
                    have(
                      (isHeight(h), in(n, N), in(v, app(h, n))) |-
                        in(n, N) /\ in(v, app(h, n))
                    ) by RightAnd(nInN, vInHN)
                    thenHave(
                      (isHeight(h), in(n, N), in(v, app(h, n))) |- vInHeight
                    ) by RightExists
                    have(
                      (isHeight(h), in(n, N), in(v, app(h, n))) |- in(v, term)
                    ) by Tautology.from(termHasHeight of (x := v), lastStep)
                    thenHave(
                      (isHeight(h), in(n, N), constructorVarsInHN) |- in(v, term)
                    ) by Weakening
                  case TypeArg(typeName) =>
                    val t = typeExprToTerm(typeName)
                    have(
                      (isHeight(h), in(n, N), constructorVarsInHN) |- in(v, t)
                    ) by Restate
              )

              if andSeq.isEmpty then have(thesis) by Restate
              else have(thesis) by RightAnd(andSeq*)
            }

            // STEP 2.1.2: Prove that if xi, ..., xj ∈ height(n) then P(c(x1, ..., xn)).
            val constructorVarsInHNImpliesPCTerm = have(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN
              ) |- P(c.term2)
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

              c.signature2.foldLeft(lastStep)((fact, el) =>
                val (v, ty) = el

                fact.statement.right.head match
                  case forall(boundVar, factCclWithoutForall) =>
                    val factCclInstantiated =
                      factCclWithoutForall.substitute(boundVar := v)
                    thenHave(
                      (
                        isHeight(h),
                        constructorPrecondition,
                        in(n, N),
                        inductionFormulaN,
                        constructorVarsInHN
                      ) |- factCclInstantiated
                    ) by InstantiateForall(v)

                    factCclInstantiated match
                      case implies(_, subformula) => ty match
                          case SelfRef => subformula match
                              case implies(_, subSubFormula) =>
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

                          // case RegularArg(_) => thenHave(
                          case TypeArg(_) => thenHave(
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
              ) |- P(c.term2)
            ) by Restate.from(constructorVarsInHNImpliesPCTerm)

            // STEP 2.1.3: Prove that if xi, ..., xj ∈ height(n) then P(x).
            thenHave(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN,
                x === c.term2
              ) |- P(x)
            ) by RightSubstEq.withParameters(List((x, c.term2)), (Seq(x), P(x)))

            thenHave(
              (
                isHeight(h),
                constructorPrecondition,
                in(n, N),
                inductionFormulaN,
                constructorVarsInHN /\ (x === c.term2)
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
            ) by QuantifiersIntro(c.variables2)
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
        (isHeight(h), in(n, N), in(x, app(h, S(n)))) |-
          isConstructor(x, app(h, n))
      ) by Cut(
        heightSuccessorStrong,
        equivalenceApply of
          (p1 := in(x, app(h, S(n))), p2 := isConstructor(x, app(h, n)))
      )
      have(
        (
          isHeight(h),
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN,
          in(x, app(h, S(n)))
        ) |- P(x)
      ) by Cut(lastStep, isConstructorImpliesP)

      // STEP 2.3: Conclude
      thenHave(
        (
          isHeight(h),
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN
        ) |- in(x, app(h, S(n))) ==> P(x)
      ) by RightImplies

      thenHave(
        (
          isHeight(h),
          structuralInductionPreconditions,
          in(n, N),
          inductionFormulaN
        ) |- inductionFormula(S(n))
      ) by RightForall
      thenHave(
        (isHeight(h), structuralInductionPreconditions, in(n, N)) |-
          inductionFormulaN ==> inductionFormula(S(n))
      ) by RightImplies
      thenHave(
        (isHeight(h), structuralInductionPreconditions) |-
          in(n, N) ==> (inductionFormulaN ==> inductionFormula(S(n)))
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
  })
}
