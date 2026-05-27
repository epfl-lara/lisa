package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.maths.Quantifiers.existsEpsilon

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.{Comprehension, Singleton, Subset, Union}
import lisa.maths.SetTheory.Base.Comprehension.{|}
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Cardinal.Universe
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*

final class HeightStageSet[N <: Arity](
  base: HeightADT[N],
  constructors: Seq[HeightStageConstructorData],
  isConstructor: Expr[Ind >>: Ind >>: Prop]
) {
  private val U = variable[Ind]
  private val φ = variable[Ind >>: Prop]

  private def constructorPredicate(
      c: HeightStageConstructorData,
      x: Expr[Ind],
      s: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(c.variables, wellTypedFormula(c.signature)(s) /\ (x === c.term))

  private val stageSetExistsCtor = Lemma(
    exists(s, ∀(x, in(x, s) <=> base.inExtIntroImage(f)(x)))
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
            have(thesis) by Tautology.from(Singleton.membership of (x := e, y := target))
          }
        case e +: rest =>
          if e == target then
            Lemma(in(target, finiteSet(elems))) {
              val inSingleton = have(in(target, Singleton.singleton(e))) by
                Tautology.from(Singleton.membership of (x := e, y := target))
              have(thesis) by Tautology.from(
                inSingleton,
                Union.membership of (x := Singleton.singleton(e), y := finiteSet(rest), z := target)
              )
            }
          else
            val rec = elementInFiniteSet(rest, target)
            Lemma(in(target, finiteSet(elems))) {
              have(in(target, finiteSet(rest))) by Restate.from(rec)
              have(thesis) by Tautology.from(
                lastStep,
                Union.membership of (x := Singleton.singleton(e), y := finiteSet(rest), z := target)
              )
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
    ) by Tautology.from(Universe.universeOfIsUniverse of (x := seed))
    val isUniverseBound = have(Universe.isUniverse(stageBound)) by Tautology.from(universeFact)
    val seedInBound = have(in(seed, stageBound)) by Tautology.from(universeFact)

    def memberOfUniverse(container: Expr[Ind], elem: Expr[Ind]): THM = Lemma(
      (Universe.isUniverse(stageBound), in(container, stageBound), in(elem, container)) |- in(elem, stageBound)
    ) {
      val containerSubset = have(
        (Universe.isUniverse(stageBound), in(container, stageBound)) |- subset(container, stageBound)
      ) by Tautology.from(Universe.universeTransitivity of (U := stageBound, x := container))
      have(thesis) by Tautology.from(
        containerSubset,
        Subset.membership of (x := container, y := stageBound, z := elem)
      )
    }

    def seedElementInUniverse(elem: Expr[Ind]): THM = {
      val inSeed = elementInFiniteSet(seedElems, elem)
      Lemma((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(elem, stageBound)) {
        val isUB = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- Universe.isUniverse(stageBound)) by Hypothesis
        val seedInB = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(seed, stageBound)) by Hypothesis
        have(in(elem, seed)) by Restate.from(inSeed)
        have(thesis) by Tautology.from(
          isUB,
          seedInB,
          lastStep,
          memberOfUniverse(seed, elem)
        )
      }
    }

    val emptyInUniverse = Lemma((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(∅, stageBound)) {
      val isUB = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- Universe.isUniverse(stageBound)) by Hypothesis
      val seedInB = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(seed, stageBound)) by Hypothesis
      have(subset(∅, seed)) by Tautology.from(Subset.leftEmpty of (x := seed))
      have(thesis) by Tautology.from(
        isUB,
        seedInB,
        lastStep,
        Universe.universeSubsetClosure of (U := stageBound, A := seed, B := ∅)
      )
    }

    def orderedPairInUniverse(a0: Expr[Ind], b0: Expr[Ind]): THM = Lemma(
      (Universe.isUniverse(stageBound), in(a0, stageBound), in(b0, stageBound)) |- in(pair(a0, b0), stageBound)
    ) {
      val singletonA = have(
        (Universe.isUniverse(stageBound), in(a0, stageBound)) |- in(Singleton.singleton(a0), stageBound)
      ) subproof {
        have(
          (Universe.isUniverse(stageBound), in(a0, stageBound)) |- in(unorderedPair(a0, a0), stageBound)
        ) by Tautology.from(
          Universe.universePairingClosure of (U := stageBound, x := a0, y := a0)
        )
        thenHave(thesis) by Substitute(Singleton.singleton.definition of (x := a0))
      }
      val pairXY = have(
        (Universe.isUniverse(stageBound), in(a0, stageBound), in(b0, stageBound)) |- in(unorderedPair(a0, b0), stageBound)
      ) by Tautology.from(Universe.universePairingClosure of (U := stageBound, x := a0, y := b0))
      val kuratowskiPair = have(
        (
          Universe.isUniverse(stageBound),
          in(a0, stageBound),
          in(b0, stageBound)
        ) |- in(unorderedPair(Singleton.singleton(a0), unorderedPair(a0, b0)), stageBound)
      ) by Tautology.from(
        Universe.universePairingClosure of (
          U := stageBound,
          x := Singleton.singleton(a0),
          y := unorderedPair(a0, b0)
        ),
        singletonA,
        pairXY
      )
      thenHave(thesis) by Substitute(lisa.maths.SetTheory.Base.Pair.pair.definition of (x := a0, y := b0))
    }

    def constructorTermInUniverse(c: HeightStageConstructorData): THM = {
      val typedArgs = wellTypedFormula(c.signature)(unionRangeF)
      Lemma((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.term, stageBound)) {
        val typedHyp = have(typedArgs |- typedArgs) by Hypothesis

        def domainInUniverse(d: Expr[Ind]): THM = Lemma(
          (Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(d, stageBound)
        ) {
          val isUB = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- Universe.isUniverse(stageBound)) by Hypothesis
          val seedInB = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(seed, stageBound)) by Hypothesis
          have(in(d, seed)) by Restate.from(elementInFiniteSet(seedElems, d))
          have(thesis) by Tautology.from(
            isUB,
            seedInB,
            lastStep,
            memberOfUniverse(seed, d)
          )
        }

        def variableInUniverse(v: Variable[Ind], d: Expr[Ind]): THM = Lemma(
          (typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(v, stageBound)
        ) {
          val vInD = have(typedArgs |- in(v, d)) by Tautology
          val dInU = have((Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(d, stageBound)) by
            Restate.from(domainInUniverse(d))
          val universeBound = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- Universe.isUniverse(stageBound)) by Hypothesis
          val seedBound = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(seed, stageBound)) by Hypothesis
          have(thesis) by Tautology.from(
            vInD,
            universeBound,
            seedBound,
            dInU,
            memberOfUniverse(d, v)
          )
        }

        val universeBound = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- Universe.isUniverse(stageBound)) by Hypothesis
        val seedBound = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(seed, stageBound)) by Hypothesis
        val initialSubtermFact = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(∅, stageBound)) by
          Tautology.from(universeBound, seedBound, emptyInUniverse)
        val emptySet: Expr[Ind] = ∅
        val subtermBuild = c.signature.reverse.foldLeft((emptySet, initialSubtermFact)) { (acc, sig) =>
          val (currentSubterm, currentFact) = acc
          val (v, ty) = sig
          val d = ty.getOrElse(unionRangeF)
          val vInU = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(v, stageBound)) by
            Restate.from(variableInUniverse(v, d))
          val pairInU = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(pair(v, currentSubterm), stageBound)) by
            Tautology.from(
              vInU,
              currentFact,
              orderedPairInUniverse(v, currentSubterm)
            )
          (pair(v, currentSubterm), pairInU)
        }
        val subtermInUniverse = have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.subterm, stageBound)) by
          Restate.from(subtermBuild._2)

        val tagInUniverse = have(
          (Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.tagTerm, stageBound)
        ) by Restate.from(seedElementInUniverse(c.tagTerm))
        have((typedArgs, Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(c.tagTerm, stageBound)) by Tautology.from(
          universeBound,
          seedBound,
          tagInUniverse
        )
        have(thesis) by Tautology.from(
          lastStep,
          subtermInUniverse,
          orderedPairInUniverse(c.tagTerm, c.subterm)
        )
      }
    }

    val unionRangeInUniverse = have(
      (Universe.isUniverse(stageBound), in(seed, stageBound)) |- in(unionRangeF, stageBound)
    ) by Restate.from(seedElementInUniverse(unionRangeF))

    val constructorOnlyCase =
      if constructors.isEmpty then
        have(isConstructor(x)(unionRangeF) |- in(x, stageBound)) by Tautology
      else
        val branches = constructors.map(c =>
          val typedEq = wellTypedFormula(c.signature)(unionRangeF) /\ (x === c.term)
          val termInU = constructorTermInUniverse(c)
          val branch = have(typedEq |- in(x, stageBound)) subproof {
            val xEqTerm = have(typedEq |- x === c.term) by Tautology
            val termInUFact = have(typedEq |- in(c.term, stageBound)) by Tautology.from(
              termInU,
              have(typedEq |- wellTypedFormula(c.signature)(unionRangeF)) by Tautology,
              isUniverseBound,
              seedInBound
            )
            have(typedEq |- in(x, stageBound) <=> in(c.term, stageBound)) by Congruence.from(xEqTerm)
            have(thesis) by Tautology.from(lastStep, termInUFact)
          }
          have(constructorPredicate(c, x, unionRangeF) |- in(x, stageBound)) by
            QuantifiersIntro(c.variables)(branch)
        )
        have(isConstructor(x)(unionRangeF) |- in(x, stageBound)) by
          LeftOr(branches*)

    val constructorCaseToUniverse = have(
      (base.inExtIntroImage(f)(x), isConstructor(x)(unionRangeF)) |- in(x, stageBound)
    ) by Tautology.from(constructorOnlyCase)

    val membershipCaseToUniverse = have(
      (base.inExtIntroImage(f)(x), in(x, unionRangeF)) |- in(x, stageBound)
    ) by Tautology.from(
      isUniverseBound,
      seedInBound,
      unionRangeInUniverse,
      memberOfUniverse(unionRangeF, x)
    )

    val extIntroInUniverse = have(base.inExtIntroImage(f)(x) |- in(x, stageBound)) subproof {
      val introBranch = have(base.inExtIntroImage(f)(x) |- isConstructor(x)(unionRangeF) \/ in(x, unionRangeF)) by Tautology
      have((base.inExtIntroImage(f)(x), isConstructor(x)(unionRangeF) \/ in(x, unionRangeF)) |- in(x, stageBound)) by
        LeftOr(constructorCaseToUniverse, membershipCaseToUniverse)
      have(thesis) by Cut(introBranch, lastStep)
    }

    val stageBodyMembership = have(in(x, stageBody) <=> in(x, stageBound) /\ base.inExtIntroImage(f)(x)) by
      Tautology.from(
        Comprehension.membership of (x := x, y := stageBound, φ := λ(x, base.inExtIntroImage(f)(x)))
      )
    val forward = have(in(x, stageBody) ==> base.inExtIntroImage(f)(x)) by Tautology.from(stageBodyMembership)
    val backward = have(base.inExtIntroImage(f)(x) ==> in(x, stageBody)) by Tautology.from(
      extIntroInUniverse,
      stageBodyMembership
    )
    have(in(x, stageBody) <=> base.inExtIntroImage(f)(x)) by Tautology.from(forward, backward)
    thenHave(∀(x, in(x, stageBody) <=> base.inExtIntroImage(f)(x))) by RightForall
    thenHave(thesis) by RightExists
  }

  private val stageSetTerm: Expr[Ind >>: Ind] =
    λ(f, ε(s, ∀(x, in(x, s) <=> base.inExtIntroImage(f)(x))))

  private lazy val stageSetSpecInst: THM = Lemma(
    HeightKernel.stageSetSpec.substitute(
      HeightKernel.stageSet := stageSetTerm,
      HeightKernel.isConstructor := isConstructor
    )
  ) {
    val body = ∀(x, in(x, s) <=> base.inExtIntroImage(f)(x))
    have(∃(s, body)) by Restate.from(stageSetExistsCtor)
    have(body.substitute(s := ε(s, body))) by
      Cut(lastStep, existsEpsilon of (x := s, P := λ(s, body)))
    thenHave(∀(x, in(x, stageSetTerm(f)) <=> base.inExtIntroImage(f)(x))) by Tautology
    thenHave(∀(f, ∀(x, in(x, stageSetTerm(f)) <=> base.inExtIntroImage(f)(x)))) by
      RightForall
    thenHave(thesis) by Restate
  }

  val heightExists = Lemma(exists(h, base.isHeight(h))) {
    val existsCore = have(
      exists(h, HeightKernel.isHeightCore(h).substitute(HeightKernel.isConstructor := isConstructor))
    ) by Cut(
      stageSetSpecInst,
      HeightKernel.heightExists.of(
        HeightKernel.stageSet := stageSetTerm,
        HeightKernel.isConstructor := isConstructor
      )
    )
    have(thesis) by Restate.from(existsCore)
  }

}
