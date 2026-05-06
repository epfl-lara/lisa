package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.UnionRangeMembership.unionRangeMembership

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.*
import lisa.maths.SetTheory.Base.Pair.given_Conversion_Expr_Expr_Expr
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.Integer.ω
import lisa.maths.Quantifiers.{existsEpsilon, existsOneEpsilonUniqueness}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate
import scala.annotation.alpha
import lisa.utils.prooflib.BasicStepTactic.RightForall

private[encoding] trait SyntacticADTTerm[N <: Arity] extends SyntacticADTHeight[N] {
  this: SyntacticADT[N] =>

  // ********
  // * TERM *
  // ********

  // The ADT term symbol is defined as the epsilon witness of its characterization.
  val polymorphicTerm = DEF(using name = s"${name}/term")(
    lisa.maths.SetTheory.SetTheory.ε(z, termDefinitionFormula(z))
  )

  polymorphicTerm.printAs(args =>
    if args.isEmpty then s"${name}/term[${typeVariablesSeq.mkString(",")}]"
    else s"${name}/term[${args.mkString(",")}]"
  )

  val term: Expr[Ind] = polymorphicTerm

  private[encoding] def termDefinitionFormula(adt: Expr[Ind]): Expr[Prop] =
    forall(t, t ∈ adt <=> forall(h, isHeight(h) ==> t ∈ unionRange(h)))

  private[encoding] val termDefinition: Expr[Prop] = termDefinitionFormula(term)

  private[encoding] lazy val termSatisfiesDefinition = Lemma(termDefinition) {
    val epsilonWitness = ε(z, termDefinitionFormula(z))

    val epsilonCharacterizationAtTerm = have(
      termDefinitionFormula(term) <=> (term === epsilonWitness)
    ) by Tautology.from(
      termExistence,
      existsOneEpsilonUniqueness of (
        x := z,
        y := term,
        P := lam(z, termDefinitionFormula(z))
      )
    )

    val termIsEpsilon = have(term === epsilonWitness) by Congruence.from(polymorphicTerm.definition)

    have(thesis) by Tautology.from(epsilonCharacterizationAtTerm, termIsEpsilon)
  }
  

  private[encoding] val termExistence = Lemma(existsOne(z, termDefinitionFormula(z))) {

    // STEP 0: Caching
    val termDefinitionRight = forall(h, isHeight(h) ==> in(t, unionRange(h)))
    val inUnionRangeF = in(t, unionRange(f))

    // STEP 1: Prove that there exists a term satisfying the definition of this ADT.
    // Specifically, this term is the union of all the terms with a height.
    val existence = have(exists(z, termDefinitionFormula(z))) subproof {

      // STEP 1.1: Prove the forward implication of the definition, using the uniqueness of the height function
      have(inUnionRangeF |- inUnionRangeF) by Hypothesis
      thenHave((f === h, inUnionRangeF) |- in(t, unionRange(h))) by
        RightSubstEq.withParameters(List((f, h)), (Seq(f), inUnionRangeF))
      have(
        (isHeight(f), isHeight(h), inUnionRangeF) |-
          in(t, unionRange(h))
      ) by Cut(heightFunUniqueEq, lastStep)
      thenHave(
        (isHeight(f), inUnionRangeF) |-
          isHeight(h) ==> in(t, unionRange(h))
      ) by RightImplies
      thenHave((isHeight(f), inUnionRangeF) |- termDefinitionRight) by
        RightForall
      val forward =
        thenHave(isHeight(f) |- inUnionRangeF ==> termDefinitionRight) by
          RightImplies

      // STEP 1.2: Prove the backward implication of the definition
      have(termDefinitionRight |- termDefinitionRight) by Hypothesis
      thenHave(termDefinitionRight |- isHeight(f) ==> inUnionRangeF) by
        InstantiateForall(f)
      val backward =
        thenHave(isHeight(f) |- termDefinitionRight ==> inUnionRangeF) by Restate

      // STEP 1.3: Use the existence of the height function to prove the existence of this ADT
      have(isHeight(f) |- inUnionRangeF <=> termDefinitionRight) by
        RightIff(forward, backward)
      thenHave(
        isHeight(f) |- forall(t, inUnionRangeF <=> termDefinitionRight)
      ) by RightForall

      thenHave(
        isHeight(f) |- exists(z, forall(t, in(t, z) <=> termDefinitionRight))
      ) by RightExists
      thenHave(
        exists(f, isHeight(f)) |-
          exists(z, forall(t, in(t, z) <=> termDefinitionRight))
      ) by LeftExists
      have(exists(z, forall(t, in(t, z) <=> termDefinitionRight))) by Cut(heightExists of (h := f), lastStep)

      thenHave(thesis) by Restate
    }

    // STEP 2: Conclude using the extension by definition

    val uniqueness = have(
      (termDefinitionFormula(x), termDefinitionFormula(y)) |- x === y
    ) subproof {

      have(termDefinitionFormula(x) |- termDefinitionFormula(x)) by Hypothesis
      val xDef = thenHave(termDefinitionFormula(x) |- in(t, x) <=> termDefinitionRight) by
        InstantiateForall(t)

      have(termDefinitionFormula(y) |- termDefinitionFormula(y)) by Hypothesis
      val yDef = thenHave(termDefinitionFormula(y) |- in(t, y) <=> termDefinitionRight) by
        InstantiateForall(t)

      have(
        (termDefinitionFormula(x), termDefinitionFormula(y)) |- in(t, x) <=> in(t, y)
      ) by Tautology.from(xDef, yDef)
      thenHave(
        (termDefinitionFormula(x), termDefinitionFormula(y)) |-
          forall(t, in(t, x) <=> in(t, y))
      ) by RightForall

      have(thesis) by Tautology.from(
        lastStep, extensionalityAxiom of (x := x, y := y, z := t)
      )
    }

    have(termDefinitionFormula(x) /\ termDefinitionFormula(y) |- (x === y)) by
      Tautology.from(uniqueness)
    thenHave(
      termDefinitionFormula(x) /\ termDefinitionFormula(y) ==> (x === y)
    ) by RightImplies
    thenHave(
      forall(y, termDefinitionFormula(x) /\ termDefinitionFormula(y) ==> (x === y))
    ) by RightForall
    val uniquenessAll = thenHave(
      forall(x,
        forall(y, termDefinitionFormula(x) /\ termDefinitionFormula(y) ==> (x === y))
    )) by RightForall

    have(
      exists(z, termDefinitionFormula(z)) /\
        forall(x, forall(y, termDefinitionFormula(x) /\ termDefinitionFormula(y) ==> (x === y)))
    ) by RightAnd(existence, uniquenessAll)

    have(thesis) by Tautology.from(
      lastStep,
      lisa.maths.Quantifiers.existsOneAlternativeDefinition of
        (x := z, P := lam(z, termDefinitionFormula(z)))
    )
  }

  private[encoding] val termHasHeight = Lemma(
    isHeight(h) |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))
  ){
    // STEP 0 : Instantiate the definition of this ADT and recover the forward and backward implications
    val termDefinition = have(in(x, term) <=> forall(h, isHeight(h) ==> in(x, unionRange(h)))) by InstantiateForall(x)(termSatisfiesDefinition)
    val termDefinitionForward = have(in(x, term) |- forall(h, isHeight(h) ==> in(x, unionRange(h)))) by Cut(
      termDefinition,
      equivalenceApply of (p1 := in(x, term), p2 := forall(h, isHeight(h) ==> in(x, unionRange(h))))
    )
    val termDefinitionBackward = have(forall(h, isHeight(h) ==> in(x, unionRange(h))) |- in(x, term)) by Cut(
      termDefinition,
      equivalenceRevApply of (p2 := in(x, term), p1 := forall(h, isHeight(h) ==> in(x, unionRange(h))))
    )

    // STEP 1 : Prove that an element is in this ADT if and only if it is in one of the images of the height function.
    have(isHeight(h) |- in(x, term) <=> in(x, unionRange(h))) subproof {

      // STEP 1.1 : Forward implication
      have(forall(h, isHeight(h) ==> in(x, unionRange(h))) |- forall(h, isHeight(h) ==> in(x, unionRange(h)))) by Hypothesis
      thenHave(forall(h, isHeight(h) ==> in(x, unionRange(h))) |- isHeight(h) ==> in(x, unionRange(h))) by InstantiateForall(h)
      thenHave((forall(h, isHeight(h) ==> in(x, unionRange(h))), isHeight(h)) |- in(x, unionRange(h))) by Restate

      val forward = have(isHeight(h) |- in(x, term) ==> in(x, unionRange(h))) by Tautology.from(lastStep,termDefinitionForward)

      // STEP 1.2 : Backward implication, follows from uniqueness of the height function
      have(in(x, unionRange(h)) |- in(x, unionRange(h))) by Hypothesis
      thenHave((f === h, in(x, unionRange(h))) |- in(x, unionRange(f))) by RightSubstEq.withParameters(List((f, h)), (Seq(h), in(x, unionRange(h))))
      have((isHeight(f), isHeight(h), in(x, unionRange(h))) |- in(x, unionRange(f))) by Cut(heightFunUniqueEq, lastStep)
      thenHave((isHeight(h), in(x, unionRange(h))) |- isHeight(f) ==> in(x, unionRange(f))) by RightImplies
      thenHave((isHeight(h), in(x, unionRange(h))) |- forall(f, isHeight(f) ==> in(x, unionRange(f)))) by RightForall
      have((isHeight(h), in(x, unionRange(h))) |- in(x, term)) by Cut(lastStep, termDefinitionBackward)
      val backward = thenHave(isHeight(h) |- in(x, unionRange(h)) ==> in(x, term)) by RightImplies

      have(thesis) by RightIff(forward, backward)
    }

    // STEP 2: Conclude by instantiating the union range membership lemma
    have( isHeight(h) |- 
      (in(x, term) <=> ∃(n, in(n, dom(h)) /\ in(x, app(h, n)))) /\ 
      (in(x, unionRange(h)) <=> exists(n, in(n, dom(h)) /\ in(x, app(h, n))))
    ) by 
      Tautology.from(lastStep, unionRangeMembership of (z := x), unfoldIsHeight)
    have(isHeight(h) |- in(x, term) <=> ∃(n, in(n, dom(h)) /\ in(x, app(h, n)))) by 
      Tautology.from(lastStep,
        equivalenceRewriting of (
          p1 := in(x, term), 
          p2 := in(x, unionRange(h)), 
          p3 := ∃(n, in(n, dom(h)) /\ in(x, app(h, n)))
        )
      )

    thenHave((isHeight(h), dom(h) === ω) |- in(x, term) <=> ∃(n, in(n, ω) /\ in(x, app(h, n)))) by RightSubstEq.withParameters(
      List((dom(h), ω)),
      (Seq(z), in(x, term) <=> ∃(n, in(n, z) /\ in(x, app(h, n))))
    )
    have(thesis) by Tautology.from(lastStep, unfoldIsHeight)
  }

  private[encoding] val termsHaveHeight = constructors.map(c =>
    c -> Lemma(
      isHeight(h) |-
        (constructorVarsInDomain(c, term) <=>
          ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))
    ){
      if c.variables.isEmpty then have(thesis) by Tautology.from(existsNat)
      else

        // STEP 1: Backward implication

        val backward = have(isHeight(h) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) ==> constructorVarsInDomain(c, term)) subproof {
          val andSeq = for (v, ty) <- c.signature yield ty match
            case SelfRef =>
              val vInHeight = (∃(n, in(n, N) /\ in(x, app(h, n)))).substitute(x := v)
              // TODO: generalize this substitution to avoid name conflicts
              // Use fresh variables is hard
              // We can try to quantify over all variables

              // println(s"thesis: $thesis")
              // println(s"goal: ${(isHeight(h), exists(n, in(n, N) /\ in(v, app(h, n)))) |- in(v, term)}")
              // println(s"vInHeight: $vInHeight")
              val termHasHeightBackward = have((isHeight(h), vInHeight) |- in(v, term)) by Cut(
                termHasHeight of (x := v),
                equivalenceRevApply of (p1 := vInHeight, p2 := in(v, term))
              )

              have((in(n, N) /\ in(v, app(h, n))) |- in(n, N) /\ in(v, app(h, n))) by Restate
              thenHave((in(n, N) /\ in(v, app(h, n))) |- exists(n, in(n, N) /\ in(v, app(h, n)))) by RightExists
              have((isHeight(h), in(n, N) /\ in(v, app(h, n))) |- in(v, term)) by Cut(lastStep, termHasHeightBackward)
              thenHave((isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, term)) by Weakening
            // case RegularArg(t_) =>
            //   val t = typeExprToTerm(t_)
            case TypeArg(typeName) =>
              val t = typeExprToTerm(typeName)
              have((isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, t)) by Restate

          have((isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by RightAnd(andSeq*)
          thenHave((isHeight(h), exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- constructorVarsInDomain(c, term)) by LeftExists
        }

        // STEP 2: Forward implication

        val forward = have(isHeight(h) |- constructorVarsInDomain(c, term) ==> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) subproof {
          val constructorVarsInTerm = have((isHeight(h), constructorVarsInDomain(c, term)) |- constructorVarsInDomain(c, term)) by Hypothesis

          val witnesses = c.signature.map((v, ty) =>
            ty match
              case SelfRef =>
                val inTerm = have((isHeight(h), constructorVarsInDomain(c, term)) |- in(v, term)) by
                  Tautology.from(constructorVarsInTerm)

                val hasSomeHeight = have(
                  (isHeight(h), constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ in(v, app(h, n)))
                ) by Tautology.from(
                  inTerm,
                  termHasHeight of (x := v),
                  equivalenceApply of (p1 := in(v, term), p2 := ∃(n, in(n, N) /\ in(v, app(h, n))))
                )

                val witnessHeight = ε(n, in(n, N) /\ in(v, app(h, n)))

                val witnessProperty = have(
                  ∃(n, in(n, N) /\ in(v, app(h, n))) |- in(witnessHeight, N) /\ in(v, app(h, witnessHeight))
                ) by Tautology.from(
                  existsEpsilon of (
                    x := n,
                    P := lam(n, in(n, N) /\ in(v, app(h, n)))
                  )
                )

                val inNatAndAtHeight = have(
                  (isHeight(h), constructorVarsInDomain(c, term)) |- in(witnessHeight, N) /\ in(v, app(h, witnessHeight))
                ) by Cut(hasSomeHeight, witnessProperty)

                val inNatWitness = have((isHeight(h), constructorVarsInDomain(c, term)) |- in(witnessHeight, N)) by
                  Tautology.from(inNatAndAtHeight)
                val inAtWitness = have((isHeight(h), constructorVarsInDomain(c, term)) |- in(v, app(h, witnessHeight))) by
                  Tautology.from(inNatAndAtHeight)

                (v, ty, witnessHeight, inNatWitness, inAtWitness)

              case TypeArg(typeName) =>
                val t = typeExprToTerm(typeName)
                val inTypeArg = have((isHeight(h), constructorVarsInDomain(c, term)) |- in(v, t)) by
                  Tautology.from(constructorVarsInTerm)
                val inZeroNat = have((isHeight(h), constructorVarsInDomain(c, term)) |- in(∅, N)) by
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
            (isHeight(h), constructorVarsInDomain(c, term)) |- seqAnd(witnessHeights.map(nh => in(nh, N)))
          ) by Tautology.from(witnesses.map(_._4)*)

          val maxInNat = have((isHeight(h), constructorVarsInDomain(c, term)) |- in(max, N)) by
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
                have((isHeight(h), in(max, N), in(ni, N), subset(ni, max)) |- subset(app(h, ni), app(h, max))) by
                  Tautology.from(heightMonotonic of (m := ni, n := max))

                have((isHeight(h), constructorVarsInDomain(c, term)) |- subset(app(h, ni), app(h, max))) by
                  Tautology.from(lastStep, maxInNat, niInNat, niInMax)

                have((isHeight(h), constructorVarsInDomain(c, term)) |- forall(z, in(z, app(h, ni)) ==> in(z, app(h, max)))) by
                  Tautology.from(lastStep, subsetAxiom of (x := app(h, ni), y := app(h, max)))

                thenHave((isHeight(h), constructorVarsInDomain(c, term)) |- in(v, app(h, ni)) ==> in(v, app(h, max))) by
                  InstantiateForall(v)

                have((isHeight(h), constructorVarsInDomain(c, term)) |- in(v, app(h, max))) by
                  Tautology.from(lastStep, inAtHeight)

              case TypeArg(_) =>
                have((isHeight(h), constructorVarsInDomain(c, term)) |- in(v, ty.getOrElse(app(h, max)))) by
                  Restate.from(inAtHeight)
          }

          val typedAtMax = have((isHeight(h), constructorVarsInDomain(c, term)) |- constructorVarsInDomain(c, app(h, max))) by
            Tautology.from(constructorVarsAtMax*)

          have((isHeight(h), constructorVarsInDomain(c, term)) |- in(max, N) /\ constructorVarsInDomain(c, app(h, max))) by
            RightAnd(maxInNat, typedAtMax)

          thenHave((isHeight(h), constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by
            RightExists

          have(thesis) by Tautology.from(lastStep)
        }

        // STEP 3: Conclude
        have(thesis) by RightIff(forward, backward)
    }
  ).toMap

  private[encoding] val heightConstructor = constructors.map(c =>
    c -> Lemma(
      (isHeight(h), in(n, N), constructorVarsInDomain(c, app(h, n))) |-
        in(c.term, app(h, successor(n)))
    ){
      // Caching
      val constructorInIntroFunHeight = inIntroImage(app(h, n))(c.term)

      // Chaining the lemma on the elements of height n + 1 and the one on constructors being in the image of the introduction function
      have((isHeight(h), in(n, N), constructorInIntroFunHeight) |- in(c.term, app(h, successor(n)))) by Cut(
        heightSuccessorWeak of (x := c.term),
        equivalenceRevApply of (p1 := constructorInIntroFunHeight, p2 := in(c.term, app(h, successor(n))))
      )
      have((isHeight(h), in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, app(h, successor(n)))) by Cut(constructorIsInIntroductionFunction(c) of (s := app(h, n)), lastStep)
    }
  ).toMap

  val intro = constructors
    .map(c =>
      c -> Lemma(
        simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))
      ){
        // STEP 0: Instantiate the forward direction of termsHaveHeight.
        val termsHaveHeightForward = have((isHeight(h), constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by Cut(
          termsHaveHeight(c),
          equivalenceApply of (p1 := constructorVarsInDomain(c, term), p2 := exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))
        )

        // STEP 1: Prove that if an instance of a constructor has height n + 1 then it is in this ADT.
        val left = have(in(n, N) |- in(successor(n), N)) by Cut(successorIsNat, equivalenceApply of (p1 := in(n, N), p2 := in(successor(n), N)))
        val right = have(in(c.term, app(h, successor(n))) |- in(c.term, app(h, successor(n)))) by Hypothesis
        have((in(n, N), in(c.term, app(h, successor(n)))) |- in(successor(n), N) /\ in(c.term, app(h, successor(n)))) by RightAnd(left, right)
        thenHave((in(n, N), in(c.term, app(h, successor(n)))) |- exists(m, in(m, N) /\ in(c.term, app(h, m)))) by RightExists
        have((isHeight(h), in(n, N), in(c.term, app(h, successor(n)))) |- in(c.term, term)) by 
          Congruence.from(lastStep, termHasHeight of (x := c.term))

        // STEP 2: Prove that if the inductive arguments of the constructor have height then the instance of the constructor is in the ADT.
        have((isHeight(h), in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, term)) by Cut(heightConstructor(c), lastStep)

        // STEP 3: Prove that if the inductive arguments of the constructor are in the ADT then they have a height and therefore
        // the instance of the constructor is in the ADT.
        thenHave((isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(c.term, term)) by LeftAnd
        thenHave((isHeight(h), exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- in(c.term, term)) by LeftExists
        have((isHeight(h), constructorVarsInDomain(c, term)) |- in(c.term, term)) by Cut(termsHaveHeightForward, lastStep)

        // STEP 4: Remove lingering assumptions
        thenHave((exists(h, isHeight(h)), constructorVarsInDomain(c, term)) |- in(c.term, term)) by LeftExists
        have(constructorVarsInDomain(c, term) |- in(c.term, term)) by Cut(heightExists, lastStep)
      }
    ).toMap
}
