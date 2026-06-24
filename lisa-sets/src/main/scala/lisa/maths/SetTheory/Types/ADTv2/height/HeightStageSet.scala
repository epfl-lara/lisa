package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.Comprehension
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Base.Union
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Cardinal.Universe
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.CoreFacts
import lisa.utils.prooflib.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts
import lisa.utils.prooflib.ProofTacticLib.Arity

final class HeightStageSet[N <: Arity](
    base: HeightADT[N],
    constructors: Seq[HeightConstructorData],
    isConstructor: Expr[Ind >>: Ind >>: Prop]
) {
  private val U = variable[Ind]
  private val φ = variable[Ind >>: Prop]

  private[height] def constructorPredicate(
      c: HeightConstructorData,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables, wellTypedFormula(c.signature)(s) /\ (x === c.term))

  private val stageSetExistsCtor = Lemma(
    ∃(s, ∀(x, in(x, s) <=> base.inExtIntroImage(f)(x)))
  ) {
    val unionRangeF = unionRange(f)

    def finiteSet(elems: Seq[Expr[Ind]]): Expr[Ind] =
      elems match
        case Seq(e) => Singleton.singleton(e)
        case e +: rest => Singleton.singleton(e) ∪ finiteSet(rest)
        case Seq() => Singleton.singleton(∅)

    def elementInFiniteSet(elems: Seq[Expr[Ind]], target: Expr[Ind]): THM =
      elems match
        case Seq(e) =>
          require(e == target, s"Target $target not found in finite set seed.")
          Lemma(in(target, finiteSet(elems))) {
            // `finiteSet(Seq(e))` is `{e}` and `e == target`, so membership is reflexivity.
            have(thesis) by Restate.from(Singleton.membership of (x := e, y := target))
          }
        case e +: rest =>
          if e == target then
            Lemma(in(target, finiteSet(elems))) {
              // `target ∈ {e}`, hence `target` is in the left disjunct of the union.
              have(in(target, Singleton.singleton(e))) by Restate.from(Singleton.membership of (x := e, y := target))
              thenHave(in(target, Singleton.singleton(e)) \/ in(target, finiteSet(rest))) by Weakening
              thenHave(thesis) by
                Substitute(Union.membership of (x := Singleton.singleton(e), y := finiteSet(rest), z := target))
            }
          else
            val rec = elementInFiniteSet(rest, target)
            Lemma(in(target, finiteSet(elems))) {
              // `target ∈ finiteSet(rest)` by recursion, hence in the right disjunct of the union.
              have(in(target, finiteSet(rest))) by Restate.from(rec)
              thenHave(in(target, Singleton.singleton(e)) \/ in(target, finiteSet(rest))) by Weakening
              thenHave(thesis) by
                Substitute(Union.membership of (x := Singleton.singleton(e), y := finiteSet(rest), z := target))
            }
        case Seq() =>
          throw IllegalArgumentException("Empty finite seed.")

    val seedElems =
      unionRangeF +: (
        constructors.flatMap(_.signature.map(_._2.getOrElse(unionRangeF))) ++
          constructors.map(_.tagTerm)
      )
    val seed = finiteSet(seedElems)
    val stageBound = Universe.universeOf(seed)
    val stageBody = { x ∈ stageBound | base.inExtIntroImage(f)(x) }

    val universeFact = have(
      Universe.isUniverse(stageBound) /\ in(seed, stageBound)
    ) by Restate.from(Universe.universeOfIsUniverse of (x := seed))
    val isUniverseBound = have(Universe.isUniverse(stageBound)) by Weakening(universeFact)
    val seedInBound = have(in(seed, stageBound)) by Weakening(universeFact)

    def memberOfUniverse(container: Expr[Ind], elem: Expr[Ind]): THM = Lemma(
      (Universe.isUniverse(stageBound), in(container, stageBound), in(elem, container)) |- in(elem, stageBound)
    ) {
      // A universe is transitive: members of `container` are members of the universe.
      val containerSubset = have(
        (Universe.isUniverse(stageBound), in(container, stageBound)) |- subset(container, stageBound)
      ) by Restate.from(Universe.universeTransitivity of (U := stageBound, x := container))
      have(
        (Universe.isUniverse(stageBound), in(container, stageBound)) |- in(elem, container) ==> in(elem, stageBound)
      ) by Cut(containerSubset, Subset.membership of (x := container, y := stageBound, z := elem))
      thenHave(thesis) by Restate
    }

    def seedElementInUniverse(elem: Expr[Ind]): THM = {
      val inSeed = elementInFiniteSet(seedElems, elem)
      Lemma((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(elem, stageBound)) {
        have(thesis) by Cut(inSeed, memberOfUniverse(seed, elem))
      }
    }

    val emptyInUniverse = Lemma((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(∅, stageBound)) {
      val emptySubsetSeed = have(subset(∅, seed)) by Restate.from(Subset.leftEmpty of (x := seed))
      have(thesis) by Cuts(
        Universe.universeSubsetClosure of (U := stageBound, A := seed, B := ∅)
      )(emptySubsetSeed)
    }

    def orderedPairInUniverse(a0: Expr[Ind], b0: Expr[Ind]): THM = Lemma(
      (Universe.isUniverse(stageBound), in(a0, stageBound), in(b0, stageBound)) |- in(pair(a0, b0), stageBound)
    ) {
      val singletonA = have(
        (Universe.isUniverse(stageBound), in(a0, stageBound)) |- in(Singleton.singleton(a0), stageBound)
      ) subproof {
        have(
          (Universe.isUniverse(stageBound), in(a0, stageBound)) |- in(unorderedPair(a0, a0), stageBound)
        ) by Restate.from(
          Universe.universePairingClosure of (U := stageBound, x := a0, y := a0)
        )
        thenHave(thesis) by Substitute(Singleton.singleton.definition of (x := a0))
      }
      val pairXY = have(
        (Universe.isUniverse(stageBound), in(a0, stageBound), in(b0, stageBound)) |- in(unorderedPair(a0, b0), stageBound)
      ) by Restate.from(Universe.universePairingClosure of (U := stageBound, x := a0, y := b0))
      // The ordered pair `(a0, b0)` is the Kuratowski pair `{{a0}, {a0, b0}}`; build it by pairing closure.
      val nestedPair = have(
        (
          Universe.isUniverse(stageBound),
          in(Singleton.singleton(a0), stageBound),
          in(unorderedPair(a0, b0), stageBound)
        ) |- in(unorderedPair(Singleton.singleton(a0), unorderedPair(a0, b0)), stageBound)
      ) by Restate.from(
        Universe.universePairingClosure of (
          U := stageBound,
          x := Singleton.singleton(a0),
          y := unorderedPair(a0, b0)
        )
      )
      have(
        (
          Universe.isUniverse(stageBound),
          in(a0, stageBound),
          in(b0, stageBound)
        ) |- in(unorderedPair(Singleton.singleton(a0), unorderedPair(a0, b0)), stageBound)
      ) by Cuts(nestedPair)(singletonA, pairXY)
      thenHave(thesis) by Substitute(lisa.maths.SetTheory.Base.Pair.pair.definition of (x := a0, y := b0))
    }

    def constructorTermInUniverse(c: HeightConstructorData): THM = {
      val typedArgs = wellTypedFormula(c.signature)(unionRangeF)
      Lemma((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.term, stageBound)) {
        // Each constructor variable `v` lives in its declared domain `d`, itself a seed element of the universe.
        def variableInUniverse(v: Variable[Ind], d: Expr[Ind]): THM = Lemma(
          (typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(v, stageBound)
        ) {
          val vInD = have(typedArgs |- in(v, d)) by Restate
          val dInU = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(d, stageBound)) by
            Restate.from(seedElementInUniverse(d))
          have(thesis) by Cuts(memberOfUniverse(d, v))(dInU, vInD)
        }

        val initialSubtermFact = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(∅, stageBound)) by
          Weakening(emptyInUniverse)
        val emptySet: Expr[Ind] = ∅
        // Build the nested-pair subterm right-to-left, keeping each prefix inside the universe.
        val subtermBuild = c.signature.reverse.foldLeft((emptySet, initialSubtermFact)) { (acc, sig) =>
          val (currentSubterm, currentFact) = acc
          val (v, ty) = sig
          val d = ty.getOrElse(unionRangeF)
          val vInU = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(v, stageBound)) by
            Restate.from(variableInUniverse(v, d))
          val pairInU = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(pair(v, currentSubterm), stageBound)) by
            Cuts(orderedPairInUniverse(v, currentSubterm))(vInU, currentFact)
          (pair(v, currentSubterm), pairInU)
        }
        val subtermInUniverse = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.subterm, stageBound)) by
          Restate.from(subtermBuild._2)

        val tagInUniverse = have(
          (Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.tagTerm, stageBound)
        ) by Restate.from(seedElementInUniverse(c.tagTerm))
        val tagInUniverseFull = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.tagTerm, stageBound)) by
          Weakening(tagInUniverse)
        // `c.term == (tagTerm, subterm)`; pair them inside the universe. When `tagTerm` and
        // `subterm` coincide (nullary constructor: both `∅`), the pairing lemma has a single
        // membership hypothesis, so one discharge suffices.
        if c.tagTerm == c.subterm then
          have(thesis) by Cuts(orderedPairInUniverse(c.tagTerm, c.subterm))(subtermInUniverse)
        else
          have(thesis) by Cuts(orderedPairInUniverse(c.tagTerm, c.subterm))(tagInUniverseFull, subtermInUniverse)
      }
    }

    val unionRangeInUniverse = have(
      (Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(unionRangeF, stageBound)
    ) by Restate.from(seedElementInUniverse(unionRangeF))

    val constructorOnlyCase =
      if constructors.isEmpty then
        // With no constructors `isConstructor(x)(·)` is `False`, so the implication holds vacuously.
        have(isConstructor(x)(unionRangeF) |- in(x, stageBound)) by Restate
      else
        val branches = constructors.map(c =>
          val typedEq = wellTypedFormula(c.signature)(unionRangeF) /\ (x === c.term)
          val termInU = constructorTermInUniverse(c)
          val branch = have(typedEq |- in(x, stageBound)) subproof {
            val xEqTerm = have(typedEq |- x === c.term) by Restate
            val typedArgsFact = have(typedEq |- wellTypedFormula(c.signature)(unionRangeF)) by Restate
            // The constructor term lives in the universe; rewrite `x` to it via the equality.
            val termInUFact = have(typedEq |- in(c.term, stageBound)) by
              Cuts(termInU)(typedArgsFact, isUniverseBound, seedInBound)
            have(typedEq |- in(x, stageBound) <=> in(c.term, stageBound)) by Congruence.from(xEqTerm)
            have(thesis) by Substitute(lastStep)(termInUFact)
          }
          have(constructorPredicate(c, x, unionRangeF) |- in(x, stageBound)) by
            QuantifiersIntro(c.variables)(branch)
        )
        have(isConstructor(x)(unionRangeF) |- in(x, stageBound)) by
          LeftOr(branches*)

    val constructorCaseToUniverse = have(
      (base.inExtIntroImage(f)(x), isConstructor(x)(unionRangeF)) |- in(x, stageBound)
    ) by Weakening(constructorOnlyCase)

    val membershipInUniverse = have(in(x, unionRangeF) |- in(x, stageBound)) by
      Cuts(memberOfUniverse(unionRangeF, x))(unionRangeInUniverse, isUniverseBound, seedInBound)
    val membershipCaseToUniverse = have(
      (base.inExtIntroImage(f)(x), in(x, unionRangeF)) |- in(x, stageBound)
    ) by Weakening(membershipInUniverse)

    val extIntroInUniverse = have(base.inExtIntroImage(f)(x) |- in(x, stageBound)) subproof {
      // `inExtIntroImage` unfolds to `(f ≠ ∅) ∧ (isConstructor(x)(⋃f) ∨ x ∈ ⋃f)`; split the disjunction.
      val introBranch = have(base.inExtIntroImage(f)(x) |- isConstructor(x)(unionRangeF) \/ in(x, unionRangeF)) by Restate
      have((base.inExtIntroImage(f)(x), isConstructor(x)(unionRangeF) \/ in(x, unionRangeF)) |- in(x, stageBound)) by
        LeftOr(constructorCaseToUniverse, membershipCaseToUniverse)
      have(thesis) by Cut(introBranch, lastStep)
    }

    // `stageBody = { x ∈ stageBound | inExtIntroImage(f)(x) }`; its membership unfolds by comprehension.
    val stageBodyMembership = have(in(x, stageBody) <=> in(x, stageBound) /\ base.inExtIntroImage(f)(x)) by
      Restate.from(
        Comprehension.membership of (x := x, y := stageBound, φ := λ(x, base.inExtIntroImage(f)(x)))
      )

    have(in(x, stageBody) |- in(x, stageBound) /\ base.inExtIntroImage(f)(x)) by
      Substitute(stageBodyMembership)(have(in(x, stageBody) |- in(x, stageBody)) by Hypothesis)
    have(in(x, stageBody) |- base.inExtIntroImage(f)(x)) by Weakening(lastStep)
    val forward = thenHave(in(x, stageBody) ==> base.inExtIntroImage(f)(x)) by Restate

    have(base.inExtIntroImage(f)(x) |- in(x, stageBound) /\ base.inExtIntroImage(f)(x)) by RightAnd(
      extIntroInUniverse,
      have(base.inExtIntroImage(f)(x) |- base.inExtIntroImage(f)(x)) by Hypothesis
    )
    thenHave(base.inExtIntroImage(f)(x) |- in(x, stageBody)) by Substitute(stageBodyMembership)
    val backward = thenHave(base.inExtIntroImage(f)(x) ==> in(x, stageBody)) by Restate

    have(in(x, stageBody) <=> base.inExtIntroImage(f)(x)) by RightIff(forward, backward)
    thenHave(∀(x, in(x, stageBody) <=> base.inExtIntroImage(f)(x))) by RightForall
    thenHave(thesis) by RightExists
  }

  private val stageSetTerm: Expr[Ind >>: Ind] =
    λ(f, ε(s, ∀(x, in(x, s) <=> base.inExtIntroImage(f)(x))))

  private lazy val stageSetSpecInst: THM = Lemma(
    CoreFacts.stageSetSpec.substitute(
      CoreFacts.stageSet := stageSetTerm,
      CoreFacts.isConstructor := isConstructor
    )
  ) {
    val body = ∀(x, in(x, s) <=> base.inExtIntroImage(f)(x))
    have(∃(s, body)) by Restate.from(stageSetExistsCtor)
    have(body.substitute(s := ε(s, body))) by
      Cut(lastStep, existsEpsilon of (x := s, P := λ(s, body)))
    thenHave(∀(x, in(x, stageSetTerm(f)) <=> base.inExtIntroImage(f)(x))) by Restate
    thenHave(∀(f, ∀(x, in(x, stageSetTerm(f)) <=> base.inExtIntroImage(f)(x)))) by
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
