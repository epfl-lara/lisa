package lisa.maths.SetTheory.Types.ADT.height

import lisa.maths.SetTheory.Base.CartesianProduct
import lisa.maths.SetTheory.Base.CartesianProduct.×
import lisa.maths.SetTheory.Base.Comprehension
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Functions.Predef.range
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.height.FiniteUnion.memberSubsetOfUnionList
import lisa.maths.SetTheory.Types.ADT.height.FiniteUnion.unionList
import lisa.maths.SetTheory.Types.ADT.height.proofs.CoreFacts
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.semantics.DefinedSymbol
import lisa.maths.SetTheory.Types.ADT.support.tactics.Cuts
import lisa.maths.SetTheory.Types.ADT.syntax.AST.ConstructorArg
import lisa.utils.prooflib.QuantifiersIntro
import lisa.utils.prooflib.Thm

/**
 * Builds finite unions and proves inclusion of their components.
 */
private[height] object FiniteUnion {

  /**
   * Forms a left-nested union, starting with the empty set.
   */
  def unionList(elems: Seq[Expr[Ind]]): Expr[Ind] =
    elems.foldLeft[Expr[Ind]](∅)(_ ∪ _)

  private lazy val subsetOfUnion = Lemma.generated(x ⊆ y |- x ⊆ (y ∪ z)) {
    val yInUnion = have(y ⊆ (y ∪ z)) by Restate.from(Union.leftSubset of (x := y, y := z))
    have(thesis) by Cut(yInUnion, Subset.transitivity of (x := x, y := y, z := y ∪ z))
  }

  /**
   * Proves that a listed component is included in the union, rejecting absent components.
   */
  def memberSubsetOfUnionList(elems: Seq[Expr[Ind]], member: Expr[Ind])(using proof: lisa.SetTheoryLibrary.Proof): Thm = {
    val index = elems.indexOf(member)
    require(index >= 0, s"Finite union does not contain the requested component $member.")
    val prefix = unionList(elems.take(index))
    val initialUnion = prefix ∪ member
    val initial = have(member ⊆ initialUnion) by Weakening(Union.rightSubset of (x := prefix, y := member))
    elems.iterator
      .drop(index + 1)
      .foldLeft[(Expr[Ind], Thm)]((initialUnion, initial)) { case ((union, inclusion), next) =>
        val extended = union ∪ next
        val step = have(member ⊆ extended) by Cut(inclusion, subsetOfUnion of (x := member, y := union, z := next))
        (extended, step)
      }
      ._2
  }
}

final class HeightStageSet(
    name: String,
    typeVariablesSeq: Seq[Variable[Ind]],
    base: HeightADT,
    constructors: Seq[HeightConstructorData],
    isConstructor: Expr[Ind >>: Ind >>: Prop]
) {
  private val φ = variable[Ind >>: Prop]
  private val predicateSubject = Variable[Ind](freshId(constructors.flatMap(_.variables) :+ isConstructor, "constructorSubject"))
  private val predicateDomain = Variable[Ind](freshId(constructors.flatMap(_.variables) ++ Seq(isConstructor, predicateSubject), "constructorDomain"))
  private val constructorPredicates = constructors.map(c => c -> existsSeq(c.variables, wellTypedFormula(c.signature)(predicateDomain) /\ (predicateSubject === c.term))).toMap

  /**
   * Describes one constructor branch without capturing the supplied subject or domain.
   */
  private[height] def constructorPredicate(
      c: HeightConstructorData,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    constructorPredicates(c).substitute(predicateSubject := x, predicateDomain := s)

  private val unionRangeF = ⋃(range(f))

  private def domainOf(ty: ConstructorArg): Expr[Ind] = ty.getOrElse(unionRangeF)

  private def subProduct(sig: Seq[(Variable[Ind], ConstructorArg)]): Expr[Ind] =
    sig.foldRight[Expr[Ind]](Singleton.singleton(∅)) { case ((_, ty), acc) => domainOf(ty) × acc }

  private def ctorProduct(c: HeightConstructorData): Expr[Ind] =
    Singleton.singleton(c.tagTerm) × subProduct(c.signature)

  private val seedElems = unionRangeF +: constructors.map(ctorProduct)
  private val bound = unionList(seedElems)
  private val stageBody = { x ∈ bound | base.inExtIntroImage(f)(x) }
  private val definedStage = new DefinedSymbol(
    name = s"$name/stageSet",
    parametersSeq = typeVariablesSeq,
    body = λ(f, stageBody)
  )
  private val stageSetTerm: Expr[Ind >>: Ind] = definedStage.term

  private val stageSetSpecInst: Theorem = Lemma.generated(
    CoreFacts.stageSetSpec.substitute(CoreFacts.stageSet := stageSetTerm, CoreFacts.isConstructor := isConstructor)
  ) {

    // Bounding strategy (plain ZF, no Tarski universe): every constructor term
    //   c.term = (tagTerm, (v₁, (… , (vₖ, ∅))))
    // lies in the iterated cartesian product matching its pairing shape,
    //   ctorProduct(c) = {tagTerm} × (D₁ × (… × (Dₖ × {∅}))),  Dᵢ = ty.getOrElse(⋃range f),
    // which is a set by Replacement/Union (no large-cardinal assumption). The stage is then
    // carved out of  bound = ⋃range f ∪ ctorProduct(c₁) ∪ … ∪ ctorProduct(cₘ)  by Separation.
    // Each constructor term lives in its product, given its arguments are well-typed in ⋃range f.
    def constructorTermInProduct(c: HeightConstructorData)(using
        proof: lisa.SetTheoryLibrary.Proof
    ): Thm = {
      val typedArgs = wellTypedFormula(c.signature)(unionRangeF)
      val emptyInSeed = have(∅ ∈ Singleton.singleton(∅)) by
        Restate.from(Singleton.membership of (x := ∅, y := ∅))
      // Build the nested-pair subterm right-to-left, threading membership in the matching product.
      val emptySet: Expr[Ind] = ∅
      val subBuild = c.signature.reverse.foldLeft((emptySet, Singleton.singleton(∅), emptyInSeed)) { case ((curSub, curProd, curFact), (v, ty)) =>
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
          LeftOr((branches).map(_.kernel))

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

    val stageBodyMembership = have(x ∈ stageBody <=> x ∈ bound /\ base.inExtIntroImage(f)(x)) by
      Restate.from(
        Comprehension.membership of (x := x, y := bound, φ := λ(x, base.inExtIntroImage(f)(x)))
      )

    val stageMembership = have(x ∈ stageBody <=> base.inExtIntroImage(f)(x)) by
      Tautology.from(stageBodyMembership, extIntroInBound)
    val stageEquality = have(stageBody === stageSetTerm(f)) by Restate.from(definedStage.definition)
    val replacement = Variable[Ind](freshId(Seq(stageBody, stageSetTerm, base.inExtIntroImage(f)(x)), "stageReplacement"))
    val namedMembership = have((stageBody === stageSetTerm(f)) |- (x ∈ stageSetTerm(f) <=> base.inExtIntroImage(f)(x))) by
      RightSubst(
        Seq(stageBody -> stageSetTerm(f)),
        Seq(replacement) -> (x ∈ replacement <=> base.inExtIntroImage(f)(x))
      )(stageMembership)
    have(x ∈ stageSetTerm(f) <=> base.inExtIntroImage(f)(x)) by Cut(stageEquality, namedMembership)
    thenHave(∀(x, x ∈ stageSetTerm(f) <=> base.inExtIntroImage(f)(x))) by RightForall
    thenHave(∀(f, ∀(x, x ∈ stageSetTerm(f) <=> base.inExtIntroImage(f)(x)))) by
      RightForall
    thenHave(thesis) by Restate
  }

  /**
   * The height function built from the explicit stage operation.
   */
  val height: Expr[Ind] = CoreFacts.heightFunctionAt(stageSetTerm)

  /**
   * The constructed function satisfies the height recurrence.
   */
  val heightValid: Theorem = Lemma.generated(base.isHeight(height)) {
    val coreForm = CoreFacts.isHeightCore(height).substitute(CoreFacts.isConstructor := isConstructor)
    val core = have(coreForm) by Cut(
      stageSetSpecInst,
      CoreFacts.heightFunctionSpecAt(stageSetTerm, isConstructor)
    )
    have(thesis) by Cut(core, base.coreIsHeight.of(h := height))
  }

  /**
   * A height function exists, witnessed by the constructed function.
   */
  val heightExists: Theorem = Lemma.generated(∃(h, base.isHeight(h))) {
    have(base.isHeight(height)) by Restate.from(heightValid)
    thenHave(thesis) by RightExists
  }

}
