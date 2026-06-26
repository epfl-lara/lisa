package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Ordinals.Integer.successorInOmega
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.height.HeightTerms
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts._
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.UniqueDefinedSymbol
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTTerm[N <: Arity] extends SyntacticADTBase[N] {
  this: SyntacticADT[N] =>

  private[encoding] def termDefinitionFormula(adt: Expr[Ind]): Expr[Prop] =
    forall(t, t ∈ adt <=> forall(h, isHeight(h) ==> t ∈ unionRange(h)))

  private[encoding] val termExistence = Lemma(existsOne(z, termDefinitionFormula(z))) {
    // `termDefinitionFormula(adt)` reads: t ∈ adt iff t belongs to the union of every height
    // approximation. The witness is the union of the range of a height function; because that
    // function is unique, "belongs to every height" collapses to "belongs to this one".
    val belongsToEveryHeight = forall(h, isHeight(h) ==> in(t, unionRange(h)))
    val inUnionRangeF = in(t, unionRange(f))

    // STEP 1: existence — `unionRange(f)` satisfies the definition for any height function `f`.
    val existence = have(exists(z, termDefinitionFormula(z))) subproof {
      // Forward: membership in f's union implies membership in every height's union (heights are equal).
      have(inUnionRangeF |- inUnionRangeF) by Hypothesis
      thenHave((f === h, inUnionRangeF) |- in(t, unionRange(h))) by
        RightSubstEq.withParameters(List((f, h)), (Seq(f), inUnionRangeF))
      have((isHeight(f), isHeight(h), inUnionRangeF) |- in(t, unionRange(h))) by Cut(heightUniqueness, lastStep)
      thenHave((isHeight(f), inUnionRangeF) |- isHeight(h) ==> in(t, unionRange(h))) by RightImplies
      thenHave((isHeight(f), inUnionRangeF) |- belongsToEveryHeight) by RightForall
      val forward = thenHave(isHeight(f) |- inUnionRangeF ==> belongsToEveryHeight) by RightImplies

      // Backward: membership in every height's union specializes to f's union.
      have(belongsToEveryHeight |- belongsToEveryHeight) by Hypothesis
      thenHave(belongsToEveryHeight |- isHeight(f) ==> inUnionRangeF) by InstantiateForall(f)
      val backward = thenHave(isHeight(f) |- belongsToEveryHeight ==> inUnionRangeF) by Restate

      // Some height function exists, so the witness exists.
      have(isHeight(f) |- inUnionRangeF <=> belongsToEveryHeight) by RightIff(forward, backward)
      thenHave(isHeight(f) |- forall(t, inUnionRangeF <=> belongsToEveryHeight)) by RightForall
      thenHave(isHeight(f) |- exists(z, forall(t, in(t, z) <=> belongsToEveryHeight))) by RightExists
      thenHave(exists(f, isHeight(f)) |- exists(z, forall(t, in(t, z) <=> belongsToEveryHeight))) by LeftExists
      have(exists(z, forall(t, in(t, z) <=> belongsToEveryHeight))) by Cut(heightExists of (h := f), lastStep)
      thenHave(thesis) by Restate
    }

    // STEP 2: uniqueness — two sets satisfying the definition have the same members, so by
    // extensionality they are equal.
    val uniqueness = have((termDefinitionFormula(x), termDefinitionFormula(y)) |- x === y) subproof {
      assume(termDefinitionFormula(x), termDefinitionFormula(y))
      have(termDefinitionFormula(x)) by Restate
      val xDef = thenHave(in(t, x) <=> belongsToEveryHeight) by InstantiateForall(t)
      have(termDefinitionFormula(y)) by Restate
      val yDef = thenHave(in(t, y) <=> belongsToEveryHeight) by InstantiateForall(t)

      have(in(t, x) <=> in(t, y)) by Congruence.from(xDef, yDef)
      thenHave(forall(t, in(t, x) <=> in(t, y))) by RightForall
      have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x := x, y := y, z := t))
    }

    // STEP 3: package existence and uniqueness into ∃!.
    have(termDefinitionFormula(x) /\ termDefinitionFormula(y) ==> (x === y)) by Restate.from(uniqueness)
    thenHave(forall(y, termDefinitionFormula(x) /\ termDefinitionFormula(y) ==> (x === y))) by RightForall
    val uniquenessAll = thenHave(forall(x, forall(y, termDefinitionFormula(x) /\ termDefinitionFormula(y) ==> (x === y)))) by RightForall

    have(thesis) by Tautology.from(
      existence,
      uniquenessAll,
      lisa.maths.Quantifiers.existsOneAlternativeDefinition of (x := z, P := lam(z, termDefinitionFormula(z)))
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

  private[encoding] val termDefinition: Expr[Prop] = termDefinitionFormula(term)

  private[encoding] lazy val termSatisfiesDefinition: THM = definedClassFunction.definitionFact

  private val heightTermsTHY = HeightTerms[N](
    heightTHY,
    heightConstructorsTHY,
    heightConstructorData,
    term,
    termSatisfiesDefinition
  )

  val termHasHeight = heightTermsTHY.termHasHeight
  private[encoding] val termsHaveHeight =
    constructors
      .zip(heightConstructorData)
      .map((c, d) =>
        c -> {
          val substitution = c.variables2.zip(c.variables).map((from, to) => from := to)
          val fact = heightTermsTHY.termsHaveHeight(d)
          Lemma(fact.statement.substitute(substitution*)) {
            have(thesis) by Restate.from(fact.of(substitution*))
          }
        }
      )
      .toMap

  val intro = constructors
    .map(c =>
      c -> Lemma(
        simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))
      ) {
        val argsInTerm = constructorVarsInDomain(c, term)
        val argsInStageN = constructorVarsInDomain(c, app(h, n))

        // If the arguments all live in the ADT, they share a common height `n`.
        val argsShareHeight = have((isHeight(h), argsInTerm) |- ∃(n, in(n, N) /\ argsInStageN)) by Cut(
          termsHaveHeight(c),
          equivalenceApply of (p1 := argsInTerm, p2 := exists(n, in(n, N) /\ argsInStageN))
        )

        // An instance sitting in approximation `S(n)` has a height, hence lies in the ADT.
        val succInN = have(in(n, N) |- in(S(n), N)) by Cut(successorInOmega, equivalenceApply of (p1 := in(n, N), p2 := in(S(n), N)))
        have((in(n, N), in(c.term, app(h, S(n)))) |- in(S(n), N) /\ in(c.term, app(h, S(n)))) by RightAnd(succInN, have(in(c.term, app(h, S(n))) |- in(c.term, app(h, S(n)))) by Hypothesis)
        thenHave((in(n, N), in(c.term, app(h, S(n)))) |- exists(m, in(m, N) /\ in(c.term, app(h, m)))) by RightExists
        val instanceInTerm = have((isHeight(h), in(n, N), in(c.term, app(h, S(n)))) |- in(c.term, term)) by
          Congruence.from(lastStep, termHasHeight of (x := c.term))

        // An element of the introduction image over approximation `n` sits in approximation `S(n)`.
        val instanceInIntroImage = inIntroImage(app(h, n))(c.term)
        val imageInSuccessor = have((isHeight(h), in(n, N), instanceInIntroImage) |- in(c.term, app(h, S(n)))) by Cut(
          heightSuccessorWeak of (x := c.term),
          equivalenceRevApply of (p1 := instanceInIntroImage, p2 := in(c.term, app(h, S(n))))
        )

        // Height-`n` arguments witness that the instance is in that introduction image.
        have(argsInStageN |- argsInStageN /\ (c.term === c.term)) by Restate
        c.variables2.foldRight((c.variables1, List[Variable[Ind]]()))((v, acc) =>
          val oldVariables = acc._1.init
          val newVariables = v :: acc._2
          val vars = oldVariables ++ newVariables
          thenHave(
            argsInStageN |- existsSeq(newVariables, wellTypedFormula(vars.zip(c.specification))(app(h, n)) /\ (c.term(vars) === c.term))
          ) by RightExists
          (oldVariables, newVariables)
        )
        thenHave(argsInStageN |- instanceInIntroImage) by Weakening
        have((isHeight(h), in(n, N), argsInStageN) |- in(c.term, app(h, S(n)))) by Cut(lastStep, imageInSuccessor)

        // Chain everything: height-`n` arguments ⟹ instance in the ADT, then discharge the
        // existential height witness and the existence of a height function.
        have((isHeight(h), in(n, N), argsInStageN) |- in(c.term, term)) by Cut(lastStep, instanceInTerm)
        thenHave((isHeight(h), in(n, N) /\ argsInStageN) |- in(c.term, term)) by LeftAnd
        thenHave((isHeight(h), exists(n, in(n, N) /\ argsInStageN)) |- in(c.term, term)) by LeftExists
        have((isHeight(h), argsInTerm) |- in(c.term, term)) by Cut(argsShareHeight, lastStep)
        thenHave((exists(h, isHeight(h)), argsInTerm) |- in(c.term, term)) by LeftExists
        have(argsInTerm |- in(c.term, term)) by Cut(heightExists, lastStep)
      }
    )
    .toMap
}
