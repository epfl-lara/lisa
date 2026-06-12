package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.height.HeightTerms
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UnionRangeMembership.unionRangeMembership
import lisa.maths.SetTheory.Types.ADTv2.support.UniqueDefinedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.Time

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.*
import lisa.maths.SetTheory.Base.Pair.given_Conversion_Expr_Expr_Expr
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.Integer.ω
import lisa.maths.Quantifiers.existsEpsilon
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate
import scala.annotation.alpha
import lisa.utils.prooflib.BasicStepTactic.RightForall

private[encoding] trait SyntacticADTTerm[N <: Arity] extends SyntacticADTHeight[N] {
  this: SyntacticADT[N] =>

  // ********
  // * TERM *
  // ********

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
      ) by Cut(heightUniqueness, lastStep)
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

  private val definedClassFunction = UniqueDefinedSymbol(
    name = s"${name}/term",
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = z,
    definitionAt = termDefinitionFormula
  )(termExistence)

  val polymorphicTerm: Constant[?] = definedClassFunction.symbol

  polymorphicTerm.printAs(args =>
    if args.isEmpty then s"${name}/term[${typeVariablesSeq.mkString(",")}]"
    else s"${name}/term[${args.mkString(",")}]"
  )

  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)

  val term: Expr[Ind] = termAt(typeVariablesSeq)

  private[encoding] def termDefinitionFormula(adt: Expr[Ind]): Expr[Prop] =
    forall(t, t ∈ adt <=> forall(h, isHeight(h) ==> t ∈ unionRange(h)))

  private[encoding] val termDefinition: Expr[Prop] = termDefinitionFormula(term)

  private[encoding] lazy val termSatisfiesDefinition: THM = definedClassFunction.definitionFact

  private val constructorInIntroductionFunction = constructors.map(c =>
    val constructorVarsInDomainCS = constructorVarsInDomain(c, s)

    c -> Lemma(constructorVarsInDomainCS |- inIntroImage(s)(c.term)) {
      have(constructorVarsInDomainCS |- constructorVarsInDomainCS /\ (c.term === c.term)) by Restate

      c.variables2.foldRight((c.variables1, List[Variable[Ind]]()))((v, acc) =>
        val oldVariables = acc._1.init
        val newVariables = v :: acc._2
        val vars = oldVariables ++ newVariables

        thenHave(
          constructorVarsInDomainCS |- existsSeq(
            newVariables,
            wellTypedFormula(vars.zip(c.specification))(s) /\ (c.term(vars) === c.term)
          )
        ) by RightExists

        (oldVariables, newVariables)
      )

      thenHave(constructorVarsInDomainCS |- inIntroImage(s)(c.term)) by Weakening
    }
  ).toMap

  private val heightTermsTHY = Time.measure("ADT HeightTerms")(HeightTerms[N](
    heightTHY,
    heightConstructorsTHY,
    heightConstructorData,
    term,
    termSatisfiesDefinition
  ))

  val termHasHeight = heightTermsTHY.termHasHeight
  val termsHaveHeight =
    constructors.zip(heightConstructorData).map((c, d) =>
      c -> {
        val substitution = c.variables2.zip(c.variables).map((from, to) => from := to)
        val fact = heightTermsTHY.termsHaveHeight(d)
        Lemma(fact.statement.substitute(substitution*)) {
          have(thesis) by Restate.from(fact.of(substitution*))
        }
      }
    ).toMap
    
  private val heightConstructor = constructors.map(c =>
    c -> Lemma(
      (isHeight(h), in(n, N), constructorVarsInDomain(c, app(h, n))) |-
        in(c.term, app(h, successor(n)))
    ) {
      val constructorInIntroFunHeight = inIntroImage(app(h, n))(c.term)

      have((isHeight(h), in(n, N), constructorInIntroFunHeight) |- in(c.term, app(h, successor(n)))) by Cut(
        heightSuccessorWeak of (x := c.term),
        equivalenceRevApply of (p1 := constructorInIntroFunHeight, p2 := in(c.term, app(h, successor(n))))
      )
      have((isHeight(h), in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, app(h, successor(n)))) by Cut(
        constructorInIntroductionFunction(c) of (s := app(h, n)),
        lastStep
      )
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
