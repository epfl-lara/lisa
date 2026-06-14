package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Base.Pair.fst
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base._
import lisa.maths.SetTheory.Functions.BasicTheorems.appTyping
import lisa.maths.SetTheory.Functions.BasicTheorems.funcBetweenEqInFuncSpace
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts.disjunctionsImplies
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts.equivalenceApply
import lisa.maths.SetTheory.Types.TypingHelpers._

/**
 * Generic lemmas about subsets, unions, ranges and (restricted) functions,
 * split out of the former `UsefulTheorems` grab-bag.
 */
object FunctionFacts {

  val unionPreimageMonotonic =
    Lemma((subset(s, t), P(s) ==> P(t)) |- (P(s) \/ in(x, s)) ==> (P(t) \/ in(x, t))) {
      have(subset(s, t) |- forall(z, in(z, s) ==> in(z, t))) by Cut(
        subsetAxiom of (x := s, y := t),
        equivalenceApply of (p1 := subset(s, t), p2 := forall(z, in(z, s) ==> in(z, t)))
      )
      thenHave(subset(s, t) |- in(x, s) ==> in(x, t)) by InstantiateForall(x)
      have(thesis) by Cut(
        lastStep,
        disjunctionsImplies of (p1 := in(x, s), p2 := in(x, t), q1 := P(s), q2 := P(t))
      )
    }

  val unionMonotonic = Lemma(subset(x, y) |- subset(⋃(x), ⋃(y))) {
    have(z ∈ b /\ b ∈ x |- z ∈ b /\ b ∈ x) by Hypothesis
    thenHave(subset(x, y) /\ z ∈ b /\ b ∈ x |- b ∈ x) by Weakening

    // Extract the forall version from the subset equivalence
    have(subset(x, y) |- forall(b, in(b, x) ==> in(b, y))) by Cut(
      subsetAxiom of (x := x, y := y),
      equivalenceApply of (p1 := subset(x, y), p2 := forall(b, in(b, x) ==> in(b, y)))
    )

    // Instantiate the universal quantifier with b
    thenHave(subset(x, y) |- in(b, x) ==> in(b, y)) by InstantiateForall(b)

    // Apply modus ponens
    have(subset(x, y) /\ in(b, x) |- in(b, y)) by Tautology.from(lastStep)
    have(subset(x, y) /\ z ∈ b /\ b ∈ x |- b ∈ y) by Tautology.from(lastStep)

    have(subset(x, y) /\ z ∈ b /\ b ∈ x |- z ∈ b /\ b ∈ y) by Tautology.from(lastStep)
    thenHave(subset(x, y) /\ z ∈ b /\ b ∈ x |- exists(a, z ∈ a /\ a ∈ y)) by RightExists
    thenHave(z ∈ b /\ b ∈ x |- subset(x, y) ==> exists(a, z ∈ a /\ a ∈ y)) by Tautology
    thenHave(exists(b, z ∈ b /\ b ∈ x) |- subset(x, y) ==> exists(a, z ∈ a /\ a ∈ y)) by
      LeftExists
    have(z ∈ ⋃(x) |- subset(x, y) ==> exists(a, z ∈ a /\ a ∈ y)) by
      Tautology.from(lastStep, ⋃.definition of (x := x, y := b, z := z))
    have(z ∈ ⋃(x) |- subset(x, y) ==> z ∈ ⋃(y)) by
      Tautology.from(lastStep, ⋃.definition of (x := y, y := b, z := z))
    have(subset(x, y) |- z ∈ ⋃(x) ==> z ∈ ⋃(y)) by Tautology.from(lastStep)
    thenHave(subset(x, y) |- forall(z, z ∈ ⋃(x) ==> z ∈ ⋃(y))) by RightForall
    have(thesis) by Tautology.from(lastStep, Subset.definition of (x := ⋃(x), y := ⋃(y)))
  }

  val rangeMonotonic = Lemma(
    subset(f, g) |- subset(Relation.range(f), Relation.range(g))
  )(
    have(thesis) by Restate.from(
      lisa.maths.SetTheory.Functions.BasicTheorems.rangeMonotonic of
        (g := f, f := g)
    )
  )

  val unionRangeMonotonic =
    Lemma(subset(f, g) |- subset(⋃(Relation.range(f)), ⋃(Relation.range(g)))) {

      val rf = Relation.range(f)
      val rg = Relation.range(g)

      have(subset(rf, rg) ==> subset(⋃(rf), ⋃(rg))) by
        Tautology.from(unionMonotonic of (x := rf, y := rg))
      have(subset(f, g) |- subset(⋃(rf), ⋃(rg))) by
        Tautology.from(lastStep, rangeMonotonic)
      thenHave(thesis) by Restate
    }

  val subsetNotEmpty = Lemma((subset(x, y), !(x === ∅)) |- !(y === ∅)) {
    val subst = have(y === ∅ |- y === ∅) by Hypothesis
    have((subset(x, ∅), y === ∅) |- (x === ∅)) by
      Tautology.from(equivalenceApply of (p1 := subset(x, ∅)), Subset.rightEmpty)
    have((subset(x, y), y === ∅) |- (x === ∅)) by Congruence.from(subst, lastStep)
  }

  val restrictedFunctionEmptyDomain =
    Lemma(restrictedFunction(h, ∅) === ∅)(
      have(thesis) by Restate.from(
        lisa.maths.SetTheory.Functions.Operations.Restriction.emptyRestriction of
          (f := h)
      )
    )

  val restrictedFunctionNotEmpty = Lemma(
    (function(h), in(x, dom(h)), in(x, d)) |- !(restrictedFunction(h, d) === ∅)
  ) {

    val pairTerm = lisa.maths.SetTheory.Base.Pair.pair(x)(app(h)(x))

    val pairInH = have((function(h), in(x, dom(h))) |- in(pairTerm, h)) by
      Tautology.from(
        lisa.maths.SetTheory.Functions.BasicTheorems.appDefinition of
          (f := h, x := x, y := app(h)(x))
      )

    val pairInRestriction = have(
      (function(h), in(x, dom(h)), in(x, d)) |- in(pairTerm, restrictedFunction(h, d))
    ) by Tautology.from(
      pairInH,
      lisa.maths.SetTheory.Functions.Operations.Restriction.pairMembership of
        (f := h, A := d, x := x, y := app(h)(x))
    )

    have(thesis) by Tautology.from(
      pairInRestriction,
      EmptySet.setWithElementNonEmpty of (x := pairTerm, y := restrictedFunction(h, d))
    )
  }

  val nonEmptyDomain =
    Lemma(!(dom(h) === ∅) |- !(h === ∅)) {
      val domEmpty =
        have(dom(∅) === ∅) by Restate.from(
          lisa.maths.SetTheory.Relations.Examples.EmptyRelation.emptyDomain
        )
      have(h === ∅ |- dom(h) === ∅) by Congruence.from(domEmpty)
      have(thesis) by Tautology.from(lastStep)
    }

  val restrictedFunctionDomainMonotonic = Lemma(
    subset(x, y) |- subset(restrictedFunction(f, x), restrictedFunction(f, y))
  ) {
    val subsetAsForall = have(subset(x, y) |- forall(z, in(z, x) ==> in(z, y))) by Cut(
      subsetAxiom of (x := x, y := y),
      equivalenceApply of
        (p1 := subset(x, y), p2 := forall(z, in(z, x) ==> in(z, y)))
    )
    val subsetAtFst = have(subset(x, y) |- in(fst(z), x) ==> in(fst(z), y)) by
      InstantiateForall(fst(z))(subsetAsForall)

    have((subset(x, y), in(z, f ↾ x)) |- in(z, f ↾ y)) by Tautology.from(
      subsetAtFst,
      lisa.maths.SetTheory.Functions.Operations.Restriction.membership of
        (f := f, A := x, z := z),
      lisa.maths.SetTheory.Functions.Operations.Restriction.membership of
        (f := f, A := y, z := z)
    )
    thenHave(subset(x, y) |- in(z, f ↾ x) ==> in(z, f ↾ y)) by Tautology
    thenHave(subset(x, y) |- forall(z, in(z, f ↾ x) ==> in(z, f ↾ y))) by
      RightForall
    have(thesis) by Tautology.from(
      lastStep,
      Subset.definition of (x := f ↾ x, y := f ↾ y)
    )
  }

  val subsetOfUnion = Lemma(subset(x, y) |- subset(x, y ∪ z)) {
    have(subset(y, y ∪ z)) by Tautology.from(Union.leftSubset of (x := y, y := z))
    have(subset(x, y) |- subset(x, y ∪ z)) by Tautology.from(lastStep, Subset.transitivity of (x := x, y := y, z := y ∪ z))
    thenHave(thesis) by Restate
  }

  val unionNull = Lemma( ∅ ∪ x === x) {
    have(∅ ⊆ x) by Tautology.from(Subset.leftEmpty of (x := x))
    val incl1 = have(∅ ∪ x ⊆ x) by Tautology.from(
      lastStep,
      Subset.reflexivity of (x := x),
      Union.leftUnionSubset of (x := ∅, y := x, z := x)
    )

    have(x ⊆ (∅ ∪ x)) by Tautology.from(Union.rightSubset of (x := ∅, y := x))

    have(thesis) by Tautology.from(incl1, lastStep, Subset.antisymmetry of (x := ∅ ∪ x, y := x))
  }

  val funEqDef = Lemma( f :: a ->: b |- x :: a ==> (f * x) :: b ) {

    val fInArrow = assume(f :: a ->: b)
    val fBetween = have(functionBetween(f)(a)(b)) by Tautology.from(
      funcBetweenEqInFuncSpace of (f := f, A := a, B := b),
      fInArrow
    )
    have(x :: a ==> (f * x) :: b) by Tautology.from(
      appTyping of (f := f, A := a, B := b, x := x),
      fBetween
    )
    thenHave(thesis) by Restate
  }

}
