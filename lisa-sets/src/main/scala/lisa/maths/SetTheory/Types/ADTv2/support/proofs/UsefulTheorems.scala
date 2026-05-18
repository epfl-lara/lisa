package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.Quantifiers.∃!

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.{
  omegaInduction,
  omegaPredecessor,
  omegaSuccessor,
  omegaCharacterization,
  integerIsOrdinal
}

import lisa.maths.SetTheory.Functions.Pi.{->:}
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}
import lisa.maths.SetTheory.Types.TypingHelpers.{::, *}
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Base.*
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base.Intersection.∩
import lisa.maths.SetTheory.Base.Pair.fst
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Ordinals.*
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.utils.prooflib.SimpleDeducedSteps.Generalize
import lisa.utils.prooflib.BasicStepTactic.*

import lisa.maths.Quantifiers.{
  existentialConjunctionWithClosedFormula,
  existentialEquivalenceDistribution,
  onePointRule
}

object UsefulTheorems {

  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2){
    have(thesis) by Tautology
  }

  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2){
    have(thesis) by Tautology
  }

  val equivalenceToRevApply = Lemma(p1 <=> p2 |- p2 ==> p1){
    have(thesis) by Tautology
  }

  val equivalenceAnd =
    Lemma((p2, p1 <=> (p2 /\ p3)) |- p1 <=> p3)(have(thesis) by Tautology)

  val disjunctionsImplies = Lemma((p1 ==> p2, q1 ==> q2) |- (p1 \/ q1) ==> (p2 \/ q2)) {

    val right = have((p1 ==> p2, q1 ==> q2, p1) |- p2 \/ q2) by Restate
    val left = have((p1 ==> p2, q1 ==> q2, q1) |- p2 \/ q2) by Restate

    have((p1 ==> p2, q1 ==> q2, p1 \/ q1) |- p2 \/ q2) by LeftOr(left, right)
  }

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

  val nInSuccN = Lemma(n ∈ successor(n)) {
    val sn = ∪(n)(Singleton.singleton(n))
    have(n ∈ Singleton.singleton(n)) by
      Tautology.from(Singleton.membership of (x := n, y := n))
    have(n ∈ sn) by
      Tautology
        .from(lastStep, Union.membership of (x := n, y := Singleton.singleton(n), z := n))
    have(thesis) by Congruence.from(lastStep, successor.definition of (x := n))
  }

  val successorInjectivity = Lemma((n === m) <=> (successor(n) === successor(m))) {

    val forward = have(n === m |- successor(n) === successor(m)) by Congruence

    val hyp = successor(n) === successor(m)
    val eq = have(hyp |- successor(n) === successor(m)) by Hypothesis

    val inSuccN = have(in(z, successor(n)) <=> in(z, n) \/ (z === n)) subproof {
      val succDef = have(successor(n) === (n ∪ Singleton.singleton(n))) by
        Tautology.from(successor.definition of (x := n))
      val unionMem = have(
        in(z, n ∪ Singleton.singleton(n)) <=> (in(z, n) \/ in(z, Singleton.singleton(n)))
      ) by
        Tautology.from(Union.membership of (x := n, y := Singleton.singleton(n), z := z))
      val singletonMem = have(in(z, Singleton.singleton(n)) <=> (z === n)) by
        Tautology.from(Singleton.membership of (x := n, y := z))

      val forward = have(in(z, successor(n)) ==> (in(z, n) \/ (z === n))) subproof {
        assume(in(z, successor(n)))
        have(in(z, n ∪ Singleton.singleton(n))) by Congruence.from(succDef)
        have(in(z, n) \/ in(z, Singleton.singleton(n))) by Tautology.from(lastStep, unionMem)
        have(in(z, n) \/ (z === n)) by Tautology.from(lastStep, singletonMem)
        thenHave(thesis) by Tautology
      }

      val backward = have((in(z, n) \/ (z === n)) ==> in(z, successor(n))) subproof {
        assume(in(z, n) \/ (z === n))
        have(in(z, n) \/ in(z, Singleton.singleton(n))) by Tautology.from(lastStep, singletonMem)
        have(in(z, n ∪ Singleton.singleton(n))) by Tautology.from(lastStep, unionMem)
        have(in(z, successor(n))) by Congruence.from(lastStep, succDef)
        thenHave(thesis) by Tautology
      }

      have(thesis) by Tautology.from(forward, backward)
    }
    val inSuccM = have(in(z, successor(m)) <=> in(z, m) \/ (z === m)) by
      Restate.from(inSuccN of (n := m))
    val nInSuccMChar = have(in(n, successor(m)) <=> in(n, m) \/ (n === m)) by
      Restate.from(inSuccN of (n := m, z := n))

    have(hyp /\ in(z, n) |- in(z, successor(n))) by Tautology.from(inSuccN)
    have(hyp /\ in(z, n) |- in(z, successor(m))) by Congruence.from(lastStep, eq)
    val zInMSplit = have(hyp /\ in(z, n) |- in(z, m) \/ (z === m)) by
      Tautology.from(lastStep, inSuccM)

    val zEqMCase = have((hyp /\ in(z, n), z === m) |- in(z, m)) subproof {
      assume(hyp /\ in(z, n))
      assume(z === m)

      val zInN = have(in(z, n)) by Tautology
      val zEqM = have(z === m) by Hypothesis
      val mInN = have(m ∈ n) by Congruence.from(zInN, zEqM)

      val nInSuccM = have(hyp |- in(n, successor(m))) by Congruence.from(nInSuccN of (n := n), eq)
      have(in(n, successor(m))) by Tautology.from(nInSuccM)
      val nInMSplit = have(in(n, m) \/ (n === m)) by Tautology.from(lastStep, nInSuccMChar)

      val cycleContradiction = have((m ∈ n, n ∈ m) |- ()) by Tautology.from(
        FoundationAxiom.membershipAsymmetric of (x := m, y := n)
      )
      val eqContradiction = have((m ∈ n, n === m) |- ()) subproof {
        assume(m ∈ n)
        assume(n === m)
        have(n ∈ n) by Congruence
        thenHave(thesis) by Tautology.fromLastStep(FoundationAxiom.selfNonInclusion of (x := n))
      }

      val contradiction = have((hyp /\ in(z, n), z === m) |- ()) by
        Tautology.from(mInN, nInMSplit, cycleContradiction, eqContradiction)
      have(thesis) by Tautology.from(contradiction)
    }

    val zInMCase = have((hyp /\ in(z, n), in(z, m)) |- in(z, m)) by Hypothesis
    val splitToInM = have((hyp /\ in(z, n), in(z, m) \/ (z === m)) |- in(z, m)) by
      LeftOr(zInMCase, zEqMCase)

    have(hyp /\ in(z, n) |- in(z, m)) by Cut(zInMSplit, splitToInM)
    have(hyp |- in(z, n) ==> in(z, m)) by Tautology.from(lastStep)
    thenHave(hyp |- forall(z, in(z, n) ==> in(z, m))) by RightForall
    val incl = have(hyp |- subset(n, m)) by
      Tautology.from(lastStep, subsetAxiom of (x := n, y := m))

    thenHave(hyp ==> subset(n, m)) by Restate
    thenHave(forall(n, forall(m, hyp ==> subset(n, m)))) by Generalize
    val revIncl = thenHave(hyp |- subset(m, n)) by InstantiateForall(m, n)

    val backward = have(hyp |- n === m) by
      Tautology.from(Subset.doubleInclusion of (x := n, y := m), incl, revIncl)

    have(thesis) by Tautology.from(forward, backward)
  }

  val zeroIsNotSucc = Lemma(!(successor(n) === ∅)) {
    val sn = ∪(n)(Singleton.singleton(n))
    have(n ∈ Singleton.singleton(n)) by
      Tautology.from(Singleton.membership of (x := n, y := n))
    have(n ∈ sn) by
      Tautology
        .from(lastStep, Union.membership of (x := n, y := Singleton.singleton(n), z := n))
    have(sn =/= ∅) by
      Tautology.from(lastStep, EmptySet.setWithElementNonEmpty of (x := n, y := sn))
    have(successor(n) =/= ∅) by
      Congruence.from(lastStep, successor.definition of (x := n))
  }

  def constructorTagDisequality(
      tagTerm1: Expr[Ind],
      tagTerm2: Expr[Ind],
      minTag: Int,
      maxTag: Int
  ): THM = {
    require(minTag >= 0, "minTag must be non-negative.")
    require(maxTag >= minTag, "maxTag must be at least minTag.")
    Lemma(!(tagTerm1 === tagTerm2)) {
      val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Congruence
      (1 to minTag).foldLeft(start)((fact, i) =>
        val midMaxTag = toTerm(maxTag - i)
        val midMinTag = toTerm(minTag - i)
        have(
          successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag
        ) by Cut(
          successorInjectivity of (n := midMaxTag, m := midMinTag),
          equivalenceApply of (
            p1 := successor(midMaxTag) === successor(midMinTag),
            p2 := midMaxTag === midMinTag
          )
        )
        have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
      )
      val chainInjectivity =
        thenHave(!(toTerm(maxTag - minTag) === ∅) |- !(tagTerm1 === tagTerm2)) by Restate
      have(toTerm(maxTag - minTag) =/= ∅) by Restate.from(
        zeroIsNotSucc of (n := toTerm(maxTag - minTag - 1))
      )
      have(thesis) by Cut(lastStep, chainInjectivity)
    }
  }

  val zeroIsNat = Lemma(in(∅, N)){
    import Ordinal.{<=, successorOrdinal}

    val nullCharacterization = have((∅ ∈ N) <=> Integer.integer(∅)) by
      InstantiateForall(∅)(omegaCharacterization)

    val leqSplit = have((b <= ∅) |- ((b ∈ ∅) \/ (b === ∅))) by Tautology
    val inEmptyCase = have((b ∈ ∅) |- (b === ∅) \/ successorOrdinal(b)) by
      Tautology.from(EmptySet.definition of (x := b))
    val eqEmptyCase = have((b === ∅) |- (b === ∅) \/ successorOrdinal(b)) by Tautology
    val fromSplit = have(((b ∈ ∅) \/ (b === ∅)) |- (b === ∅) \/ successorOrdinal(b)) by
      LeftOr(inEmptyCase, eqEmptyCase)
    have((b <= ∅) |- (b === ∅) \/ successorOrdinal(b)) by Cut(leqSplit, fromSplit)
    thenHave((b <= ∅) ==> (b === ∅) \/ successorOrdinal(b)) by RightImplies
    thenHave(forall(b, (b <= ∅) ==> (b === ∅) \/ successorOrdinal(b))) by
      lisa.utils.prooflib.BasicStepTactic.RightForall

    have(Integer.integer(∅)) by Tautology.from(lastStep, Integer.integer.definition of (α := ∅, β := b))
    have(in(∅, N)) by Tautology.from(lastStep, nullCharacterization)
    have(thesis) by Restate.from(lastStep)
  }

  val natNotEmpty = Lemma(!(N === ∅))(
    have(thesis) by Tautology.from(
      zeroIsNat,
      EmptySet.setWithElementNonEmpty of (x := ∅, y := N)
    )
  )

  val successorIsNat = Lemma(in(n, N) <=> in(successor(n), N)) {

    val eqSucc = have(S(n) === successor(n)) by
      Congruence.from(S.definition of (α := n), successor.definition of (x := n))

    val toS = have(in(n, N) |- in(S(n), N)) by Restate.from(omegaSuccessor of (α := n))
    val fromS = have(in(S(n), N) |- in(n, N)) by
      Restate.from(omegaPredecessor of (α := n))

    val toSuccConv = have(in(S(n), N) |- in(successor(n), N)) by Congruence.from(eqSucc)
    val fromSuccConv = have(in(successor(n), N) |- in(S(n), N)) by Congruence.from(eqSucc)

    val toSucc = have(in(n, N) |- in(successor(n), N)) by Cut(toS, toSuccConv)
    val fromSucc = have(in(successor(n), N) |- in(n, N)) by Cut(fromSuccConv, fromS)

    have(thesis) by Tautology.from(toSucc, fromSucc)
  }

  val natInduction = Lemma(
    (P(∅), forall(m, in(m, N) ==> (P(m) ==> P(successor(m))))) |-
      forall(n, in(n, N) ==> P(n))
  ) {
    val eqSucc = have(S(m) === successor(m)) by
      Congruence.from(S.definition of (α := m), successor.definition of (x := m))

    val stepS = have(
      forall(m, in(m, N) ==> (P(m) ==> P(successor(m)))) |-
        forall(m, in(m, N) ==> (P(m) ==> P(S(m))))
    ) subproof {
      assume(forall(m, in(m, N) ==> (P(m) ==> P(successor(m)))))
      thenHave(in(m, N) ==> (P(m) ==> P(successor(m)))) by InstantiateForall(m)
      have(in(m, N) ==> (P(m) ==> P(S(m)))) by Congruence.from(lastStep, eqSucc)
      thenHave(forall(m, in(m, N) ==> (P(m) ==> P(S(m))))) by RightForall
    }

    have(thesis) by Tautology.from(omegaInduction, stepS)
  }

  val subsetIsNat = Lemma(in(y, N) |- in(x, y) ==> in(x, N)) {

    val Q = lam(y, in(x, y) ==> in(x, N))

    val zeroCase = have(Q(∅)) subproof {
      have(in(x, ∅) |- ()) by Tautology.from(EmptySet.definition of (x := x))
      thenHave(in(x, ∅) ==> in(x, N)) by Tautology
      thenHave(thesis) by Restate
    }

    val recCase = have(in(y, N) /\ Q(y) |- Q(successor(y))) subproof {
      assume(in(y, N) /\ Q(y))
      val yInN = have(in(y, N)) by Tautology
      val ih = have(in(x, y) ==> in(x, N)) by Tautology

      val inSuccY = have(in(x, successor(y)) ==> in(x, y) \/ (x === y)) subproof {
        assume(in(x, successor(y)))
        val succDef = have(successor(y) === (y ∪ Singleton.singleton(y))) by
          Tautology.from(successor.definition of (x := y))
        val unionMem = have(in(x, y ∪ Singleton.singleton(y)) <=> in(x, y) \/ in(x, Singleton.singleton(y))) by
          Tautology.from(Union.membership of (x := y, y := Singleton.singleton(y), z := x))
        val singletonMem = have(in(x, Singleton.singleton(y)) <=> (x === y)) by
          Tautology.from(Singleton.membership of (x := y, y := x))

        have(in(x, y ∪ Singleton.singleton(y))) by Congruence.from(succDef)
        have(in(x, y) \/ in(x, Singleton.singleton(y))) by Tautology.from(lastStep, unionMem)
        have(in(x, y) \/ (x === y)) by Tautology.from(lastStep, singletonMem)
        thenHave(thesis) by Tautology
      }

      val inCase = have(in(x, y) |- in(x, N)) by Tautology.from(ih)
      val eqCase = have(x === y |- in(x, N)) by Congruence.from(yInN)

      have(in(x, successor(y)) |- in(x, N)) by Tautology.from(inSuccY, inCase, eqCase)
      thenHave(in(x, successor(y)) ==> in(x, N)) by RightImplies
      thenHave(thesis) by Restate
    }

    have(in(y, N) ==> (Q(y) ==> Q(successor(y)))) by Tautology.from(recCase)
    thenHave(forall(y, in(y, N) ==> (Q(y) ==> Q(successor(y))))) by RightForall
    have(Q(∅) /\ forall(y, in(y, N) ==> (Q(y) ==> Q(successor(y))))) by
      Tautology.from(zeroCase, lastStep)

    have(forall(k, in(k, N) ==> Q(k))) by
      Tautology.from(lastStep, natInduction of (P := Q, m := y, n := k))
    thenHave(in(y, N) ==> Q(y)) by InstantiateForall(y)
    thenHave(thesis) by Tautology
  }

  val subsetSuccessor = Lemma(subset(n, successor(n))) {
    val succExpanded = ∪(n)(Singleton.singleton(n))

    have(subset(n, succExpanded)) by
      Tautology.from(Union.leftSubset of (x := n, y := Singleton.singleton(n)))
    have(subset(n, n) |- subset(n, successor(n))) by
      Congruence.from(lastStep, successor.definition of (x := n))
    have(thesis) by Cut(Subset.reflexivity of (x := n), lastStep)
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


  val existsOneUniqueness =
    Lemma((∃!(x, P(x)), P(x), P(y)) |- x === y) {
      have(∃!(x, P(x)) |- ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) by
        Restate.from(lisa.maths.Quantifiers.existsOneUniqueness)
      thenHave(∃!(x, P(x)) |- P(x) /\ P(y) ==> (x === y)) by
        InstantiateForall(x, y)
      have(thesis) by Tautology.from(lastStep)
    }

  val altEqualityTransitivity =
    Lemma((x === y, y === z) |- x === z)(have(thesis) by Congruence)

  val equivalenceRewriting =
    Lemma((p1 <=> p2, p2 <=> p3) |- (p1 <=> p3))(have(thesis) by Tautology)

  val impliesEquivalence = Lemma((p1 <=> p2, p3 <=> p4) |- (p1 ==> p3) <=> (p2 ==> p4)) {
    have(thesis) by Tautology
  }

  val leftImpliesEquivalenceWeak =
    Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2))(have(thesis) by Tautology)

  val leftImpliesEquivalenceStrong =
    Lemma(p ==> (p1 <=> p2) |- (p ==> p1) <=> (p ==> p2))(have(thesis) by Tautology)

  val existsNeg = Lemma(∃(x, !P(x)) |- !forall(x, P(x)))(have(thesis) by Tautology)


  // helper: union of two ω-members is in ω
  val unionOfTwoNats = Lemma((in(a, N) /\ in(b, N)) |- in(a ∪ b, N)) {

    import Ordinal.<
    import TransitiveSet.transitiveSet

    // get ordinals from ω-membership
    have(in(a, N) <=> Integer.integer(a)) by InstantiateForall(a)(omegaCharacterization)
    val aIsOrdinal = have(in(a, N) |- Ordinal.ordinal(a)) by 
      Tautology.from(integerIsOrdinal of (α := a), lastStep)
    have(in(b, N) <=> Integer.integer(b)) by InstantiateForall(b)(omegaCharacterization)
    val bIsOrdinal = have(in(b, N) |- Ordinal.ordinal(b)) by 
      Tautology.from(integerIsOrdinal of (α := b), lastStep)

    // comparability: either a = b or a ∈ b or b ∈ a
    val comp = have((Ordinal.ordinal(a), Ordinal.ordinal(b)) |- (a === b) \/ (a < b) \/ (b < a)) by
      Tautology.from(Ordinal.comparability of (α := a, β := b))

    // case analysis on the disjunction
    // Case a === b
    val caseEq = have((a === b, in(a, N), in(b, N)) |- in(a ∪ b, N)) subproof {
      have((a === b, a ∪ b === b) |- a ∪ b === b) by Hypothesis
      have((a === b, b ∪ b === b) |- a ∪ b === b) by Congruence.from(lastStep)
      have((a === b) |- a ∪ b === b) by Congruence.from(lastStep, Union.idempotence of (x := b))
      have((a === b, b ∈ N) |- a ∪ b ∈ N) by Congruence.from(lastStep)
      have(thesis) by Tautology.from(lastStep)
    }

    // Case a < b  (i.e. a ∈ b)
    val caseALtB = have((a < b, in(a, N), in(b, N)) |- in(a ∪ b, N)) subproof {

      assume((a < b) /\ in(a, N) /\ in(b, N))

      have(TransitiveSet.transitiveSet(b)) by 
        Tautology.from(bIsOrdinal, Ordinal.ordinal.definition of (α := b))
      have(a ⊆ b) by 
        Tautology.from(lastStep, TransitiveSet.elementIsSubset of (x := a, A := b))
      have((a ∪ b) ⊆ (b ∪ b)) by 
        Tautology.from(lastStep, Union.leftMonotonic of (x := a, y := b, z := b))
      val unionSubset = have(a ∪ b ⊆ b) by 
        Congruence.from(lastStep, Union.idempotence of (x := b))
      
      have(b ⊆ (a ∪ b)) by 
        Tautology.from(Union.rightSubset of (x := a, y := b))
      have((a ∪ b) === b) by 
        Tautology.from(unionSubset, lastStep, Subset.antisymmetry of (x := a ∪ b, y := b))
      have(thesis) by Congruence.from(lastStep)
    }

    // Symmetric case b < a
    val caseBLtA = have((b < a, in(a, N), in(b, N)) |- in(a ∪ b, N)) subproof {
      have(thesis) by Congruence.from(
        caseALtB of (a := b, b := a), 
        Union.commutativity of (x := a, y := b)
      )
    }

    // Combine the cases coming from comparability
    have((in(a, N), in(b, N)) |- in(a ∪ b, N)) by 
      Tautology.from(comp, caseEq, caseALtB, caseBLtA, aIsOrdinal, bIsOrdinal)
    thenHave(thesis) by Restate
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

  val existsNat = Lemma(exists(n, in(n, N))) {
    have(thesis) by RightExists(zeroIsNat)
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
