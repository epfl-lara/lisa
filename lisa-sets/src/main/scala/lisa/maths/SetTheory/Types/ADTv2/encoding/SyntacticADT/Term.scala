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
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate
import scala.annotation.alpha

private[encoding] trait SyntacticADTTerm[N <: Arity] extends SyntacticADTHeight[N] {
  this: SyntacticADT[N] =>

  // ********
  // * TERM *
  // ********

  // Temporary placeholder while ADTv2 function-definition integration is finalized.
  // polymorphicTerm = FunctionDefinition[N](name, line.value, file.value)(typeVariablesSeq, z, termDefinition(z), termExistence).label

  // private val polymorphicTermConst = Constant[Ind](s"${name}Polyterm")
  // registerConstant(polymorphicTermConst)
  // val polymorphicTerm: Expr[Ind] = polymorphicTermConst

  // private val termConst = Constant[Ind](s"${name}Term")
  // registerConstant(termConst)
  // val term: Expr[Ind] = termConst

  // DEF-based placeholder replacing the temporary raw Constant.
  val polymorphicTerm = DEF(using name = s"${name}Polyterm")(
    lisa.maths.SetTheory.SetTheory.ε(z, termDefinitionFormula(z))
  )
  val term: Expr[Ind] = appSeq(polymorphicTerm)(typeVariablesSeq)

  private[encoding] def termDefinitionFormula(adt: Expr[Ind]): Expr[Prop] =
    forall(t, t ∈ adt <=> forall(h, isHeight(h) ==> t ∈ unionRange(h)))

  private[encoding] val termDefinition: Expr[Prop] = termDefinitionFormula(term)

  private[encoding] val termSatisfiesDefinition = Lemma(termDefinition) {
    // have(thesis) by InstantiateForall(term)(polymorphicTerm.definition)
    // println(s"Term satisfies definition: $term, $thesis, ${polymorphicTerm.definition.statement}")
    have(thesis) by Sorry
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
      Tautology.from(lastStep, unionRangeMembership of (z := x), isHeight.definition)
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
    have(thesis) by Tautology.from(lastStep, isHeight.definition)
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
              val termHasHeightBackward = have((isHeight(h), exists(n, in(n, N) /\ in(v, app(h, n)))) |- in(v, term)) by Cut(
                termHasHeight of (x := v),
                equivalenceRevApply of (p1 := ∃(n, in(n, N) /\ in(v, app(h, n))), p2 := in(v, term))
              )

              have((in(n, N) /\ in(v, app(h, n))) |- in(n, N) /\ in(v, app(h, n))) by Restate
              thenHave((in(n, N) /\ in(v, app(h, n))) |- exists(n, in(n, N) /\ in(v, app(h, n)))) by RightExists
              have((isHeight(h), in(n, N) /\ in(v, app(h, n))) |- in(v, term)) by Cut(lastStep, termHasHeightBackward)
              thenHave((isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, term)) by Weakening
            case RegularArg(t_) =>
              val t = typeExprToTerm(t_)
              have((isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, t)) by Restate

          have((isHeight(h), in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by RightAnd(andSeq*)
          thenHave((isHeight(h), exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- constructorVarsInDomain(c, term)) by LeftExists
        }

        // STEP 2: Forward implication

        val forward = have(isHeight(h) |- constructorVarsInDomain(c, term) ==> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) subproof {
          val nSeq: Seq[Variable[Ind]] = (0 until c.variables.size).map(i => Variable[Ind](s"n$i"))
          val max = if c.arity == 0 then ∅ else nSeq.reduce((a: Expr[Ind], b: Expr[Ind]) => a ∪ b)

          
          val maxInN = have(seqAnd(nSeq.map(n => in(n, N))) |- in(max, N)) subproof { 
            have( True |- in(∅, N)) by Tautology.from(zeroIsNat)
            val u0: Expr[Ind] = ∅
            nSeq.foldLeft((lastStep, u0))((acc, n) => 
              val (thm, u) = acc
              val hyp = thm.statement.left.head

              val newHyp = if hyp == True then in(n, N) else hyp /\ in(n, N)
              val newU = if u == ∅ then n else u ∪ n

              val newThm = have( newHyp |- in(newU, N)) by 
                Tautology.from(thm, unionOfTwoNats of (a := u, b := n))
              (newThm, newU)
            )
            have(thesis) by Tautology.from(lastStep)
          }


          val andSeq = for ((v, ty), ni) <- c.signature.zip(nSeq) yield
            
            val niInMax = have(subset(ni, max)) subproof {

              have( True |- True ) by Tautology
              val u0: Expr[Ind] = ∅
              val n0: Expr[Ind] = ∅
              nSeq.foldLeft((lastStep, u0, n0)) { (acc, nj) =>
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
                      Congruence.from(lastStep, unionNull of (x := ni) )
                  else
                    have((curHyp) |- subset(newN, newU)) by Tautology.from(thmAcc, 
                      subsetOfUnion of (x := newN, y := u, z := nj), 
                      Subset.leftEmpty of (x := newU)
                    )

                (stepThm, newU, newN)
              }

              have(thesis) by Tautology.from(lastStep)
            }

            ty match
              case SelfRef =>
                have((isHeight(h), in(max, N), subset(ni, max)) |- subset(app(h, ni), app(h, max))) by 
                  Restate.from(heightMonotonic of (m := ni, n := max))
                have((isHeight(h), seqAnd(nSeq.map(n => in(n, N)))) |- subset(app(h, ni), app(h, max))) by 
                  Tautology.from(lastStep, maxInN, niInMax)
                have((isHeight(h), seqAnd(nSeq.map(n => in(n, N)))) |- forall(z, in(z, app(h, ni)) ==> in(z, app(h, max)))) by 
                  Tautology.from(lastStep, subsetAxiom of (x := app(h, ni), y := app(h, max)))
                thenHave((isHeight(h), seqAnd(nSeq.map(n => in(n, N)))) |- in(v, app(h, ni)) ==> in(v, app(h, max))) by InstantiateForall(v)
                thenHave((isHeight(h), seqAnd(nSeq.map(n => in(n, N))), in(v, app(h, ni))) |- in(v, app(h, max))) by Restate
              case RegularArg(t_) =>
                val t = typeExprToTerm(t_)
                have((seqAnd(nSeq.map(n => in(n, N))), isHeight(h), in(v, t)) |- in(v, t)) by Restate

            have((seqAnd(nSeq.map(n => in(n, N))), isHeight(h), in(v, ty.getOrElse(app(h, ni)))) |- in(max, N) /\ in(v, ty.getOrElse(app(h, max)))) by RightAnd(maxInN, lastStep)
            thenHave(nSeq.map(n => in(n, N) /\ in(v, ty.getOrElse(app(h, n)))).toSet + isHeight(h) |- in(max, N) /\ in(v, ty.getOrElse(app(h, max)))) by Weakening
            thenHave(nSeq.map(n => in(n, N) /\ in(v, ty.getOrElse(app(h, n)))).toSet + isHeight(h) |- ∃(n, in(n, N) /\ in(v, ty.getOrElse(app(h, n))))) by RightExists

          // println(s"name : $name (${c})")
          // println(s"andSeq: ${andSeq.map(_.statement)}")
          // println(s"thesis: ${thesis}")
          // println(s"term: ${term}, $polymorphicTerm ${polymorphicTerm.definition.statement}")

          thenHave(thesis) by Sorry
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
