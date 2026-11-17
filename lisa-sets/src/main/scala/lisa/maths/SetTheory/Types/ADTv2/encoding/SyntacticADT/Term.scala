package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Functions.Predef.range
import lisa.maths.SetTheory.Ordinals.Integer.successorInOmega
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.height.HeightTerms
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiate
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts._
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.DefinedSymbol
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
   * Instantiates common height, composing argument renaming with the caller's simultaneous substitution.
   */
  private[encoding] def termsHaveHeight(c: SyntacticConstructor, substitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact = {
    val renaming = c.variables2.zip(c.variables).map((from, to) => from := to.substitute(substitutions*))
    val remaining = substitutions.filterNot(substitution => c.variables2.contains(substitution._1))
    instantiate(commonHeightTheorems(c), remaining ++ renaming)
  }

  val intro = constructors
    .map(c =>
      c -> Lemma(
        simplify(constructorVarsInDomain(c, term)) |- simplify(c.term ∈ term)
      ) {
        val argsInTerm = constructorVarsInDomain(c, term)
        val argsInStageN = constructorVarsInDomain(c, app(h, n))

        // If the arguments all live in the ADT, they share a common height `n`.
        val argsShareHeight = have((isHeight(h), argsInTerm) |- ∃(n, n ∈ N /\ argsInStageN)) by Cut(
          termsHaveHeight(c),
          equivalenceApply of (p1 := argsInTerm, p2 := exists(n, n ∈ N /\ argsInStageN))
        )

        // An instance sitting in approximation `S(n)` has a height, hence lies in the ADT.
        val succInN = have(n ∈ N |- S(n) ∈ N) by Cut(successorInOmega, equivalenceApply of (p1 := n ∈ N, p2 := S(n) ∈ N))
        have((n ∈ N, c.term ∈ app(h, S(n))) |- S(n) ∈ N /\ c.term ∈ app(h, S(n))) by RightAnd(succInN, have(c.term ∈ app(h, S(n)) |- c.term ∈ app(h, S(n))) by Hypothesis)
        thenHave((n ∈ N, c.term ∈ app(h, S(n))) |- exists(m, m ∈ N /\ c.term ∈ app(h, m))) by RightExists
        val instanceInTerm = have((isHeight(h), n ∈ N, c.term ∈ app(h, S(n))) |- c.term ∈ term) by
          Congruence.from(lastStep, termHasHeight of (x := c.term))

        // An element of the introduction image over approximation `n` sits in approximation `S(n)`.
        val instanceInIntroImage = inIntroImage(app(h, n))(c.term)
        val imageInSuccessor = have((isHeight(h), n ∈ N, instanceInIntroImage) |- c.term ∈ app(h, S(n))) by Cut(
          heightSuccessorWeak of (x := c.term),
          equivalenceRevApply of (p1 := instanceInIntroImage, p2 := c.term ∈ app(h, S(n)))
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
        have((isHeight(h), n ∈ N, argsInStageN) |- c.term ∈ app(h, S(n))) by Cut(lastStep, imageInSuccessor)

        // Chain everything: height-`n` arguments ⟹ instance in the ADT, then discharge the
        // existential height witness and the existence of a height function.
        have((isHeight(h), n ∈ N, argsInStageN) |- c.term ∈ term) by Cut(lastStep, instanceInTerm)
        thenHave((isHeight(h), n ∈ N /\ argsInStageN) |- c.term ∈ term) by LeftAnd
        thenHave((isHeight(h), exists(n, n ∈ N /\ argsInStageN)) |- c.term ∈ term) by LeftExists
        have((isHeight(h), argsInTerm) |- c.term ∈ term) by Cut(argsShareHeight, lastStep)
        thenHave((exists(h, isHeight(h)), argsInTerm) |- c.term ∈ term) by LeftExists
        have(argsInTerm |- c.term ∈ term) by Cut(heightExists, lastStep)
      }
    )
    .toMap
}
