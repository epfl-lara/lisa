package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.UsefullTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTTerm[N <: Arity]
    extends SyntacticADTHeight[N] {
  this: SyntacticADT[N] =>

  // ********
  // * TERM *
  // ********

  private[encoding] def termDefinitionFormula(adt: Expr[Ind]): Expr[Prop] =
    forall(t, in(t, adt) <=> forall(h, hIsTheHeightFunction ==> in(t, unionRange(h))))

  private[encoding] val termExistence = Lemma(existsOne(z, termDefinitionFormula(z))) {
    have(thesis) by Sorry
  }

  // Temporary placeholder while ADTv2 function-definition integration is finalized.
  val polymorphicTerm: Expr[Ind] = Constant[Ind](s"${name}_poly_term")

  val term: Expr[Ind] = Constant[Ind](s"${name}_term")

  private[encoding] val termDefinition: Expr[Prop] = termDefinitionFormula(term)

  private[encoding] val termSatisfiesDefinition = Lemma(termDefinition) {
    // have(thesis) by InstantiateForall(term)(polymorphicTerm.definition)
    println(s"termDefinition: $termDefinition")
    have(thesis) by Sorry
  }

  private[encoding] val termHasHeight =
    Lemma(hIsTheHeightFunction |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) {
      have(thesis) by Sorry
    }

  private[encoding] val termsHaveHeight = constructors.map(c =>
    c -> Lemma(
      hIsTheHeightFunction |- (constructorVarsInDomain(c, term) <=> ∃(
        n,
        in(n, N) /\ constructorVarsInDomain(c, app(h, n))
      ))
    ) {
      have(thesis) by Sorry
    }
  ).toMap

  private[encoding] val heightConstructor = constructors.map(c =>
    c -> Lemma(
      (hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(
        c.term,
        app(h, successor(n))
      )
    ) {
      have(thesis) by Sorry
    }
  ).toMap

  val intro = constructors.map(c =>
    c -> Lemma(simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))) {
      have(thesis) by Sorry
    }
  ).toMap
}
