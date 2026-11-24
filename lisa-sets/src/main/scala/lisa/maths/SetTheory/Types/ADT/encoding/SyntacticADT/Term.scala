package lisa.maths.SetTheory.Types.ADT.encoding

import lisa.maths.SetTheory.Functions.Predef.range
import lisa.maths.SetTheory.Ordinals.Integer.successorInOmega
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.height.HeightTerms
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiate
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.proofs.PropositionalFacts._
import lisa.maths.SetTheory.Types.ADT.support.semantics.DefinedSymbol
import lisa.utils.fol.FOL.SubstPair
import lisa.utils.prooflib.BasicStepTactic.Restate

private[encoding] trait SyntacticADTTerm extends SyntacticADTBase {
  this: SyntacticADT =>

  private val definedClassFunction = new DefinedSymbol(
    name = s"${name}/term",
    parametersSeq = typeVariablesSeq,
    body = ⋃(range(height))
  )

  val polymorphicTerm: Constant[?] = definedClassFunction.symbol

  polymorphicTerm.printAs(args =>
    if args.isEmpty then s"${name}/term[${typeVariablesSeq.mkString(",")}]"
    else s"${name}/term[${args.mkString(",")}]"
  )

  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)

  val term: Expr[Ind] = termAt(typeVariablesSeq)

  /**
   * The carrier is the union of the stages of any valid height function.
   */
  private val termEqualsUnion: THM = Lemma(isHeight(h) |- term === ⋃(range(h))) {
    val sameHeight = have(isHeight(h) |- height === h) by Cut(heightValid, heightUniqueness.of(f := height))
    have(thesis) by Congruence.from(sameHeight, definedClassFunction.definition)
  }

  private val heightTermsTHY = HeightTerms(
    heightTHY,
    heightConstructorsTHY,
    heightConstructorData,
    term,
    termEqualsUnion
  )

  val termHasHeight = heightTermsTHY.termHasHeight
  private val commonHeightTheorems = constructors
    .zip(heightConstructorData)
    .map((c, data) => c -> heightTermsTHY.termsHaveHeight(data))
    .toMap

  /**
   * Instantiates common height with a separate height function, composing argument and parameter substitutions.
   */
  private[encoding] def termsHaveHeight(c: SyntacticConstructor, heightFunction: Expr[Ind], substitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact = {
    val renaming = c.variables2.zip(c.variables).map((from, to) => from := to.substitute(substitutions*))
    // The schema's h denotes the height function; a field named h is handled by argument renaming.
    val remaining = substitutions.filterNot(substitution => c.variables2.contains(substitution._1) || substitution._1 == h)
    instantiate(commonHeightTheorems(c), remaining ++ renaming :+ (h := heightFunction))
  }

  val intro = constructors
    .map(c =>
      c -> Lemma(
        simplify(constructorVarsInDomain(c, term)) |- simplify(c.term ∈ term)
      ) {
        val context = typeVariablesSeq ++ c.variables1 ++ c.variables2 :+ term
        val heightFunction = Variable[Ind](freshId(context, "h"))
        val stage = Variable[Ind](freshId(context :+ heightFunction, "n"))
        val otherStage = Variable[Ind](freshId(context ++ Seq(heightFunction, stage), "m"))
        val argsInTerm = constructorVarsInDomain(c, term)
        val argsInStageN = constructorVarsInDomain(c, app(heightFunction, stage))

        // If the arguments all live in the ADT, they share a common height `stage`.
        val argsShareHeight = have((isHeight(heightFunction), argsInTerm) |- ∃(stage, stage ∈ N /\ argsInStageN)) by Cut(
          termsHaveHeight(c, heightFunction),
          equivalenceApply of (p1 := argsInTerm, p2 := exists(stage, stage ∈ N /\ argsInStageN))
        )

        // An instance sitting in approximation `S(stage)` has a height, hence lies in the ADT.
        val succInN = have(stage ∈ N |- S(stage) ∈ N) by Cut(successorInOmega.of(n := stage), equivalenceApply of (p1 := stage ∈ N, p2 := S(stage) ∈ N))
        have((stage ∈ N, c.term ∈ app(heightFunction, S(stage))) |- S(stage) ∈ N /\ c.term ∈ app(heightFunction, S(stage))) by RightAnd(
          succInN,
          have(c.term ∈ app(heightFunction, S(stage)) |- c.term ∈ app(heightFunction, S(stage))) by Hypothesis
        )
        thenHave((stage ∈ N, c.term ∈ app(heightFunction, S(stage))) |- exists(otherStage, otherStage ∈ N /\ c.term ∈ app(heightFunction, otherStage))) by RightExists
        val instanceInTerm = have((isHeight(heightFunction), stage ∈ N, c.term ∈ app(heightFunction, S(stage))) |- c.term ∈ term) by
          Congruence.from(lastStep, termHasHeight of (x := c.term, h := heightFunction))

        // An element of the introduction image over approximation `stage` sits in approximation `S(stage)`.
        val instanceInIntroImage = inIntroImage(app(heightFunction, stage))(c.term)
        val imageInSuccessor = have((isHeight(heightFunction), stage ∈ N, instanceInIntroImage) |- c.term ∈ app(heightFunction, S(stage))) by Cut(
          heightSuccessorWeak of (x := c.term, h := heightFunction, n := stage),
          equivalenceRevApply of (p1 := instanceInIntroImage, p2 := c.term ∈ app(heightFunction, S(stage)))
        )

        // Height-`stage` arguments witness that the instance is in that introduction image.
        have(argsInStageN |- argsInStageN /\ (c.term === c.term)) by Restate
        c.variables2.foldRight((c.variables1, List[Variable[Ind]]()))((v, acc) =>
          val oldVariables = acc._1.init
          val newVariables = v :: acc._2
          val vars = oldVariables ++ newVariables
          thenHave(
            argsInStageN |- existsSeq(newVariables, wellTypedFormula(vars.zip(c.specification))(app(heightFunction, stage)) /\ (c.term(vars) === c.term))
          ) by RightExists
          (oldVariables, newVariables)
        )
        thenHave(argsInStageN |- instanceInIntroImage) by Weakening
        have((isHeight(heightFunction), stage ∈ N, argsInStageN) |- c.term ∈ app(heightFunction, S(stage))) by Cut(lastStep, imageInSuccessor)

        // Chain everything: height-`stage` arguments ⟹ instance in the ADT, then discharge the
        // existential height witness and the existence of a height function.
        have((isHeight(heightFunction), stage ∈ N, argsInStageN) |- c.term ∈ term) by Cut(lastStep, instanceInTerm)
        thenHave((isHeight(heightFunction), stage ∈ N /\ argsInStageN) |- c.term ∈ term) by LeftAnd
        thenHave((isHeight(heightFunction), exists(stage, stage ∈ N /\ argsInStageN)) |- c.term ∈ term) by LeftExists
        have((isHeight(heightFunction), argsInTerm) |- c.term ∈ term) by Cut(argsShareHeight, lastStep)
        thenHave((exists(heightFunction, isHeight(heightFunction)), argsInTerm) |- c.term ∈ term) by LeftExists
        have(argsInTerm |- c.term ∈ term) by Cut(heightExists, lastStep)
      }
    )
    .toMap
}
