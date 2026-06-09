package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UnionRangeMembership.unionRangeMembership

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.*
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.Integer.ω
import lisa.maths.Quantifiers.existsEpsilon
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate

final class HeightTerms[N <: Arity](
  base: HeightADT[N],
  constructorsTheory: HeightConstructors[N],
  constructors: Seq[HeightConstructorData],
  term: Expr[Ind],
  termSatisfiesDefinition: THM
) {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def constructorVarsInDomain(
      c: HeightConstructorData,
      s: Expr[Ind]
  ): Expr[Prop] = wellTypedFormula(c.signature)(s)

  val termHasHeight = Lemma(
    base.isHeight(h) |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))
  ) {
    val termDefinition = have(
      in(x, term) <=> forall(h, base.isHeight(h) ==> in(x, unionRange(h)))
    ) by InstantiateForall(x)(termSatisfiesDefinition)
    val termDefinitionForward = have(
      in(x, term) |- forall(h, base.isHeight(h) ==> in(x, unionRange(h)))
    ) by Cut(
      termDefinition,
      equivalenceApply of
        (p1 := in(x, term), p2 := forall(h, base.isHeight(h) ==> in(x, unionRange(h))))
    )
    val termDefinitionBackward = have(
      forall(h, base.isHeight(h) ==> in(x, unionRange(h))) |- in(x, term)
    ) by Cut(
      termDefinition,
      equivalenceRevApply of
        (p2 := in(x, term), p1 := forall(h, base.isHeight(h) ==> in(x, unionRange(h))))
    )

    have(base.isHeight(h) |- in(x, term) <=> in(x, unionRange(h))) subproof {
      have(
        forall(h, base.isHeight(h) ==> in(x, unionRange(h))) |- forall(h, base.isHeight(h) ==> in(x, unionRange(h)))
      ) by Hypothesis
      thenHave(
        forall(h, base.isHeight(h) ==> in(x, unionRange(h))) |- base.isHeight(h) ==> in(x, unionRange(h))
      ) by InstantiateForall(h)
      thenHave(
        (forall(h, base.isHeight(h) ==> in(x, unionRange(h))), base.isHeight(h)) |- in(x, unionRange(h))
      ) by Restate

      val forward = have(base.isHeight(h) |- in(x, term) ==> in(x, unionRange(h))) by
        Tautology.from(lastStep, termDefinitionForward)

      have(in(x, unionRange(h)) |- in(x, unionRange(h))) by Hypothesis
      thenHave((f === h, in(x, unionRange(h))) |- in(x, unionRange(f))) by
        RightSubstEq.withParameters(List((f, h)), (Seq(h), in(x, unionRange(h))))
      have(
        (base.isHeight(f), base.isHeight(h), in(x, unionRange(h))) |- in(x, unionRange(f))
      ) by Cut(constructorsTheory.heightUniqueness, lastStep)
      thenHave((base.isHeight(h), in(x, unionRange(h))) |- base.isHeight(f) ==> in(x, unionRange(f))) by
        RightImplies
      thenHave((base.isHeight(h), in(x, unionRange(h))) |- forall(f, base.isHeight(f) ==> in(x, unionRange(f)))) by
        RightForall
      have((base.isHeight(h), in(x, unionRange(h))) |- in(x, term)) by
        Cut(lastStep, termDefinitionBackward)
      val backward = thenHave(base.isHeight(h) |- in(x, unionRange(h)) ==> in(x, term)) by
        RightImplies

      have(thesis) by RightIff(forward, backward)
    }

    have(
      base.isHeight(h) |- (in(x, term) <=> ∃(n, in(n, dom(h)) /\ in(x, app(h, n)))) /\
        (in(x, unionRange(h)) <=> exists(n, in(n, dom(h)) /\ in(x, app(h, n))))
    ) by Tautology.from(lastStep, unionRangeMembership of (z := x), base.heightIsCore)
    have(base.isHeight(h) |- in(x, term) <=> ∃(n, in(n, dom(h)) /\ in(x, app(h, n)))) by
      Tautology.from(
        lastStep,
        equivalenceRewriting of (
          p1 := in(x, term),
          p2 := in(x, unionRange(h)),
          p3 := ∃(n, in(n, dom(h)) /\ in(x, app(h, n)))
        )
      )

    thenHave(
      (base.isHeight(h), dom(h) === ω) |- in(x, term) <=> ∃(n, in(n, ω) /\ in(x, app(h, n)))
    ) by RightSubstEq.withParameters(
      List((dom(h), ω)),
      (Seq(z), in(x, term) <=> ∃(n, in(n, z) /\ in(x, app(h, n))))
    )
    have(thesis) by Tautology.from(lastStep, base.heightIsCore)
  }

  val termsHaveHeight = constructors.map(c =>
    c -> Lemma(
      base.isHeight(h) |-
        (constructorVarsInDomain(c, term) <=>
          ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))
    ) {
      if c.arity == 0 then have(thesis) by Tautology.from(existsNat)
      else
        val backward = have(
          base.isHeight(h) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) ==> constructorVarsInDomain(c, term)
        ) subproof {
          val andSeq = for (v, ty) <- c.signature yield ty match
            case SelfRef =>
              val vInHeight = (∃(n, in(n, N) /\ in(x, app(h, n)))).substitute(x := v)
              val termHasHeightBackward = have((base.isHeight(h), vInHeight) |- in(v, term)) by
                Cut(
                  termHasHeight of (x := v),
                  equivalenceRevApply of (p1 := vInHeight, p2 := in(v, term))
                )

              have((in(n, N) /\ in(v, app(h, n))) |- in(n, N) /\ in(v, app(h, n))) by Restate
              thenHave((in(n, N) /\ in(v, app(h, n))) |- exists(n, in(n, N) /\ in(v, app(h, n)))) by
                RightExists
              have((base.isHeight(h), in(n, N) /\ in(v, app(h, n))) |- in(v, term)) by
                Cut(lastStep, termHasHeightBackward)
              thenHave((base.isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, term)) by
                Weakening
            case TypeArg(typeName) =>
              val t = typeExprToTerm(typeName)
              have((base.isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, t)) by
                Restate

          have((base.isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by
            RightAnd(andSeq*)
          thenHave((base.isHeight(h), exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- constructorVarsInDomain(c, term)) by
            LeftExists
        }

        val forward = have(
          base.isHeight(h) |- constructorVarsInDomain(c, term) ==> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
        ) subproof {
          val constructorVarsInTerm = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- constructorVarsInDomain(c, term)) by
            Hypothesis

          val witnesses = c.signature.map((v, ty) =>
            ty match
              case SelfRef =>
                val inTerm = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(v, term)) by
                  Tautology.from(constructorVarsInTerm)

                val hasSomeHeight = have(
                  (base.isHeight(h), constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ in(v, app(h, n)))
                ) by Tautology.from(
                  inTerm,
                  termHasHeight of (x := v),
                  equivalenceApply of (p1 := in(v, term), p2 := ∃(n, in(n, N) /\ in(v, app(h, n))))
                )

                val witnessHeight = ε(n, in(n, N) /\ in(v, app(h, n)))

                val witnessProperty = have(
                  ∃(n, in(n, N) /\ in(v, app(h, n))) |- in(witnessHeight, N) /\ in(v, app(h, witnessHeight))
                ) by Tautology.from(
                  existsEpsilon of (x := n, P := lam(n, in(n, N) /\ in(v, app(h, n))))
                )

                val inNatAndAtHeight = have(
                  (base.isHeight(h), constructorVarsInDomain(c, term)) |- in(witnessHeight, N) /\ in(v, app(h, witnessHeight))
                ) by Cut(hasSomeHeight, witnessProperty)

                val inNatWitness = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(witnessHeight, N)) by
                  Tautology.from(inNatAndAtHeight)
                val inAtWitness = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(v, app(h, witnessHeight))) by
                  Tautology.from(inNatAndAtHeight)

                (v, ty, witnessHeight, inNatWitness, inAtWitness)

              case TypeArg(typeName) =>
                val t = typeExprToTerm(typeName)
                val inTypeArg = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(v, t)) by
                  Tautology.from(constructorVarsInTerm)
                val inZeroNat = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(∅, N)) by
                  Tautology.from(zeroIsNat)
                val zeroHeight: Expr[Ind] = ∅

                (v, ty, zeroHeight, inZeroNat, inTypeArg)
          )

          val witnessHeights = witnesses.map(_._3)
          val max = witnessHeights.foldLeft[Expr[Ind]](∅)((u, nh) =>
            if u == ∅ then nh else u ∪ nh
          )

          val maxInNatFromSequence = have(
            seqAnd(witnessHeights.map(nh => in(nh, N))) |- in(max, N)
          ) subproof {
            have(True |- in(∅, N)) by Tautology.from(zeroIsNat)
            val u0: Expr[Ind] = ∅
            witnessHeights.foldLeft((lastStep, u0))((acc, nh) =>
              val (thm, u) = acc
              val hyp = thm.statement.left.head

              val newHyp = if hyp == True then in(nh, N) else hyp /\ in(nh, N)
              val newU = if u == ∅ then nh else u ∪ nh

              val newThm = have(newHyp |- in(newU, N)) by
                Tautology.from(thm, unionOfTwoNats of (a := u, b := nh))

              (newThm, newU)
            )
            have(thesis) by Tautology.from(lastStep)
          }

          val allHeightsInNat = have(
            (base.isHeight(h), constructorVarsInDomain(c, term)) |- seqAnd(witnessHeights.map(nh => in(nh, N)))
          ) by Tautology.from(witnesses.map(_._4)*)

          val maxInNat = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(max, N)) by
            Cut(allHeightsInNat, maxInNatFromSequence)

          val constructorVarsAtMax = witnesses.map { case (v, ty, ni, niInNat, inAtHeight) =>
            val niInMax = have(subset(ni, max)) subproof {
              have(True |- True) by Tautology
              val u0: Expr[Ind] = ∅
              val n0: Expr[Ind] = ∅

              witnessHeights.foldLeft((lastStep, u0, n0)) { (acc, nj) =>
                val (thmAcc, u, lastN) = acc
                val curHyp = thmAcc.statement.left.head

                val newU = if u == ∅ then nj else u ∪ nj
                val newN = if nj == ni then nj else lastN

                val stepThm =
                  if u == ∅ && nj == ni then
                    have(curHyp |- subset(newN, newU)) by
                      Tautology.from(thmAcc, Subset.reflexivity of (x := ni))
                  else if nj == ni then
                    have(curHyp |- subset(∅ ∪ ni, newU)) by
                      Tautology.from(thmAcc, Union.leftMonotonic of (x := ∅, y := u, z := ni))
                    have(curHyp |- subset(newN, newU)) by
                      Congruence.from(lastStep, unionNull of (x := ni))
                  else
                    have(curHyp |- subset(newN, newU)) by
                      Tautology.from(
                        thmAcc,
                        subsetOfUnion of (x := newN, y := u, z := nj),
                        Subset.leftEmpty of (x := newU)
                      )

                (stepThm, newU, newN)
              }

              have(thesis) by Tautology.from(lastStep)
            }

            ty match
              case SelfRef =>
                have((base.isHeight(h), in(max, N), in(ni, N), subset(ni, max)) |- subset(app(h, ni), app(h, max))) by
                  Tautology.from(constructorsTheory.heightMonotonic of (m := ni, n := max))

                have((base.isHeight(h), constructorVarsInDomain(c, term)) |- subset(app(h, ni), app(h, max))) by
                  Tautology.from(lastStep, maxInNat, niInNat, niInMax)

                have((base.isHeight(h), constructorVarsInDomain(c, term)) |- forall(z, in(z, app(h, ni)) ==> in(z, app(h, max)))) by
                  Tautology.from(lastStep, subsetAxiom of (x := app(h, ni), y := app(h, max)))

                thenHave((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(v, app(h, ni)) ==> in(v, app(h, max))) by
                  InstantiateForall(v)

                have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(v, app(h, max))) by
                  Tautology.from(lastStep, inAtHeight)

              case TypeArg(_) =>
                have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(v, ty.getOrElse(app(h, max)))) by
                  Restate.from(inAtHeight)
          }

          val typedAtMax = have((base.isHeight(h), constructorVarsInDomain(c, term)) |- constructorVarsInDomain(c, app(h, max))) by
            Tautology.from(constructorVarsAtMax*)

          have((base.isHeight(h), constructorVarsInDomain(c, term)) |- in(max, N) /\ constructorVarsInDomain(c, app(h, max))) by
            RightAnd(maxInNat, typedAtMax)

          thenHave((base.isHeight(h), constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by
            RightExists

          have(thesis) by Tautology.from(lastStep)
        }

        have(thesis) by RightIff(forward, backward)
    }
  ).toMap

}
