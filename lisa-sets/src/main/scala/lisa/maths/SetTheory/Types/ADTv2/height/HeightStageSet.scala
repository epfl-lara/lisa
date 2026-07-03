package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.Comprehension
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base.CartesianProduct
import lisa.maths.SetTheory.Base.CartesianProduct.×
import lisa.maths.SetTheory.Functions.Predef.range
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.CoreFacts
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ConstructorArg
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.QuantifiersIntro

final class HeightStageSet[N <: Arity](
    base: HeightADT[N],
    constructors: Seq[HeightConstructorData],
    isConstructor: Expr[Ind >>: Ind >>: Prop]
) {
  private val φ = variable[Ind >>: Prop]

  private[height] def constructorPredicate(
      c: HeightConstructorData,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables, wellTypedFormula(c.signature)(s) /\ (x === c.term))

  // ── Finite-union helpers (plain ZF), used to assemble the bounding set for Separation. ──
  // (Mirror of the helpers in `HeightTerms`; kept local to avoid a cross-file dependency.)

  /** Left-nested union of a finite sequence of sets, seeded with `∅`. */
  private def unionList(elems: Seq[Expr[Ind]]): Expr[Ind] =
    elems.foldLeft[Expr[Ind]](∅)(_ ∪ _)

  private val subsetOfUnion = Lemma(x ⊆ y |- x ⊆ (y ∪ z)) {
    val yInUnion = have(y ⊆ (y ∪ z)) by Restate.from(Union.leftSubset of (x := y, y := z))
    have(thesis) by Cut(yInUnion, Subset.transitivity of (x := x, y := y, z := y ∪ z))
  }

  /** Every member of a finite sequence is a subset of its union [[unionList]].
    * Produces `|- subset(ni, unionList(elems))` (assuming `ni` occurs in `elems`).
    */
  private def memberSubsetOfUnionList(elems: Seq[Expr[Ind]], ni: Expr[Ind])(using
      proof: lisa.SetTheoryLibrary.Proof
  ): proof.Fact = {
    val seed = have(True |- True) by Restate
    elems
      .foldLeft[(proof.Fact, Expr[Ind], Expr[Ind])]((seed, ∅, ∅)) { case ((thmAcc, u, lastN), nj) =>
        val curHyp = thmAcc.statement.left.head
        val newU = u ∪ nj
        val newN = if nj == ni then nj else lastN

        val stepThm =
          if nj == ni then
            // We reach `ni`: `ni ⊆ u ∪ ni` (covers the first element, where `u == ∅`).
            have(curHyp |- newN ⊆ newU) by Restate.from(Union.rightSubset of (x := u, y := ni))
          else if newN == ∅ then
            // `ni` not seen yet (tracked subset is `∅`): `∅ ⊆ newU`.
            have(curHyp |- newN ⊆ newU) by Restate.from(Subset.leftEmpty of (x := newU))
          else
            // Extend the established `ni ⊆ u` by another union member.
            have(curHyp |- newN ⊆ newU) by Cut(thmAcc, subsetOfUnion of (x := newN, y := u, z := nj))

        (stepThm, newU, newN)
      }
      ._1
  }

  private val stageSetExistsCtor = Lemma(
    ∃(s, ∀(x, x ∈ s <=> base.inExtIntroImage(f)(x)))
  ) {
    val unionRangeF = ⋃(range(f))

    // Bounding strategy (plain ZF, no Tarski universe): every constructor term
    //   c.term = (tagTerm, (v₁, (… , (vₖ, ∅))))
    // lies in the iterated cartesian product matching its pairing shape,
    //   ctorProduct(c) = {tagTerm} × (D₁ × (… × (Dₖ × {∅}))),  Dᵢ = ty.getOrElse(⋃range f),
    // which is a set by Replacement/Union (no large-cardinal assumption). The stage is then
    // carved out of  bound = ⋃range f ∪ ctorProduct(c₁) ∪ … ∪ ctorProduct(cₘ)  by Separation.
    def domainOf(ty: ConstructorArg): Expr[Ind] = ty.getOrElse(unionRangeF)

    def subProduct(sig: Seq[(Variable[Ind], ConstructorArg)]): Expr[Ind] =
      sig.foldRight[Expr[Ind]](Singleton.singleton(∅)) { case ((_, ty), acc) => domainOf(ty) × acc }

    def ctorProduct(c: HeightConstructorData): Expr[Ind] =
      Singleton.singleton(c.tagTerm) × subProduct(c.signature)

    // Each constructor term lives in its product, given its arguments are well-typed in ⋃range f.
    def constructorTermInProduct(c: HeightConstructorData)(using
        proof: lisa.SetTheoryLibrary.Proof
    ): proof.Fact = {
      val typedArgs = wellTypedFormula(c.signature)(unionRangeF)
      val emptyInSeed = have(∅ ∈ Singleton.singleton(∅)) by
        Restate.from(Singleton.membership of (x := ∅, y := ∅))
      // Build the nested-pair subterm right-to-left, threading membership in the matching product.
      val emptySet: Expr[Ind] = ∅
      val subBuild = c.signature.reverse.foldLeft((emptySet, Singleton.singleton(∅), emptyInSeed)) {
        case ((curSub, curProd, curFact), (v, ty)) =>
          val d = domainOf(ty)
          val vInD = have(typedArgs |- v ∈ d) by Restate
          val pairFact = have(typedArgs |- pair(v, curSub) ∈ (d × curProd)) by
            Cuts(CartesianProduct.membershipSufficientCondition of (x := v, A := d, y := curSub, B := curProd))(vInD, curFact)
          (pair(v, curSub), d × curProd, pairFact)
      }
      val subtermInProduct = have(typedArgs |- c.subterm ∈ subProduct(c.signature)) by
        Restate.from(subBuild._3)

      val tagInSingleton = have(c.tagTerm ∈ Singleton.singleton(c.tagTerm)) by
        Restate.from(Singleton.membership of (x := c.tagTerm, y := c.tagTerm))
      // `c.term == (tagTerm, subterm)`; pair them inside `{tagTerm} × subProduct`.
      have(typedArgs |- c.term ∈ ctorProduct(c)) by Cuts(
        CartesianProduct.membershipSufficientCondition of
          (x := c.tagTerm, A := Singleton.singleton(c.tagTerm), y := c.subterm, B := subProduct(c.signature))
      )(tagInSingleton, subtermInProduct)
    }

    val products = constructors.map(ctorProduct)
    val seedElems = unionRangeF +: products
    val bound = unionList(seedElems)

    val unionRangeSubsetBound = have(unionRangeF ⊆ bound) by
      Restate.from(memberSubsetOfUnionList(seedElems, unionRangeF))

    val constructorOnlyCase =
      if constructors.isEmpty then
        // With no constructors `isConstructor(x)(·)` is `False`, so the implication holds vacuously.
        have(isConstructor(x)(unionRangeF) |- x ∈ bound) by Restate
      else
        val branches = constructors.map(c =>
          val typedEq = wellTypedFormula(c.signature)(unionRangeF) /\ (x === c.term)
          val termInProductFact = constructorTermInProduct(c)
          val prodSubsetBound = have(ctorProduct(c) ⊆ bound) by
            Restate.from(memberSubsetOfUnionList(seedElems, ctorProduct(c)))
          val branch = have(typedEq |- x ∈ bound) subproof {
            val xEqTerm = have(typedEq |- x === c.term) by Restate
            val typedArgsFact = have(typedEq |- wellTypedFormula(c.signature)(unionRangeF)) by Restate
            // The constructor term lives in its product, itself a subset of `bound`; rewrite `x` to it.
            val termInProd = have(typedEq |- c.term ∈ ctorProduct(c)) by Cut(typedArgsFact, termInProductFact)
            val termInBound = have(typedEq |- c.term ∈ bound) by Tautology.from(
              termInProd,
              prodSubsetBound,
              Subset.membership of (x := ctorProduct(c), y := bound, z := c.term)
            )
            have(typedEq |- x ∈ bound <=> c.term ∈ bound) by Congruence.from(xEqTerm)
            have(thesis) by Substitute(lastStep)(termInBound)
          }
          have(constructorPredicate(c, x, unionRangeF) |- x ∈ bound) by
            QuantifiersIntro(c.variables)(branch)
        )
        have(isConstructor(x)(unionRangeF) |- x ∈ bound) by
          LeftOr(branches*)

    val constructorCaseToBound = have(
      (base.inExtIntroImage(f)(x), isConstructor(x)(unionRangeF)) |- x ∈ bound
    ) by Weakening(constructorOnlyCase)

    val membershipInBound = have(x ∈ unionRangeF |- x ∈ bound) by Tautology.from(
      unionRangeSubsetBound,
      Subset.membership of (x := unionRangeF, y := bound, z := x)
    )
    val membershipCaseToBound = have(
      (base.inExtIntroImage(f)(x), x ∈ unionRangeF) |- x ∈ bound
    ) by Weakening(membershipInBound)

    val extIntroInBound = have(base.inExtIntroImage(f)(x) |- x ∈ bound) subproof {
      // `inExtIntroImage` unfolds to `(f ≠ ∅) ∧ (isConstructor(x)(⋃f) ∨ x ∈ ⋃f)`; split the disjunction.
      val introBranch = have(base.inExtIntroImage(f)(x) |- isConstructor(x)(unionRangeF) \/ (x ∈ unionRangeF)) by Restate
      have((base.inExtIntroImage(f)(x), isConstructor(x)(unionRangeF) \/ (x ∈ unionRangeF)) |- x ∈ bound) by
        LeftOr(constructorCaseToBound, membershipCaseToBound)
      have(thesis) by Cut(introBranch, lastStep)
    }

    // `stageBody = { x ∈ bound | inExtIntroImage(f)(x) }`; its membership unfolds by comprehension.
    val stageBody = { x ∈ bound | base.inExtIntroImage(f)(x) }
    val stageBodyMembership = have(x ∈ stageBody <=> x ∈ bound /\ base.inExtIntroImage(f)(x)) by
      Restate.from(
        Comprehension.membership of (x := x, y := bound, φ := λ(x, base.inExtIntroImage(f)(x)))
      )

    have(x ∈ stageBody |- x ∈ bound /\ base.inExtIntroImage(f)(x)) by
      Substitute(stageBodyMembership)(have(x ∈ stageBody |- x ∈ stageBody) by Hypothesis)
    have(x ∈ stageBody |- base.inExtIntroImage(f)(x)) by Weakening(lastStep)
    val forward = thenHave(x ∈ stageBody ==> base.inExtIntroImage(f)(x)) by Restate

    have(base.inExtIntroImage(f)(x) |- x ∈ bound /\ base.inExtIntroImage(f)(x)) by RightAnd(
      extIntroInBound,
      have(base.inExtIntroImage(f)(x) |- base.inExtIntroImage(f)(x)) by Hypothesis
    )
    thenHave(base.inExtIntroImage(f)(x) |- x ∈ stageBody) by Substitute(stageBodyMembership)
    val backward = thenHave(base.inExtIntroImage(f)(x) ==> x ∈ stageBody) by Restate

    have(x ∈ stageBody <=> base.inExtIntroImage(f)(x)) by RightIff(forward, backward)
    thenHave(∀(x, x ∈ stageBody <=> base.inExtIntroImage(f)(x))) by RightForall
    thenHave(thesis) by RightExists
  }

  private val stageSetTerm: Expr[Ind >>: Ind] =
    λ(f, ε(s, ∀(x, x ∈ s <=> base.inExtIntroImage(f)(x))))

  private lazy val stageSetSpecInst: THM = Lemma(
    CoreFacts.stageSetSpec.substitute(
      CoreFacts.stageSet := stageSetTerm,
      CoreFacts.isConstructor := isConstructor
    )
  ) {
    val body = ∀(x, x ∈ s <=> base.inExtIntroImage(f)(x))
    have(∃(s, body)) by Restate.from(stageSetExistsCtor)
    have(body.substitute(s := ε(s, body))) by
      Cut(lastStep, existsEpsilon of (x := s, P := λ(s, body)))
    thenHave(∀(x, x ∈ stageSetTerm(f) <=> base.inExtIntroImage(f)(x))) by Restate
    thenHave(∀(f, ∀(x, x ∈ stageSetTerm(f) <=> base.inExtIntroImage(f)(x)))) by
      RightForall
    thenHave(thesis) by Restate
  }

  val heightExists = Lemma(∃(h, base.isHeight(h))) {
    val coreForm = CoreFacts.isHeightCore(h).substitute(CoreFacts.isConstructor := isConstructor)
    val existsCore = have(∃(h, coreForm)) by Cut(
      stageSetSpecInst,
      CoreFacts.heightExistsAt(stageSetTerm, isConstructor)
    )
    have(coreForm |- ∃(h, base.isHeight(h))) by RightExists(base.coreIsHeight)
    thenHave(∃(h, coreForm) |- ∃(h, base.isHeight(h))) by LeftExists
    have(thesis) by Cut(existsCore, lastStep)
  }

}
