package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.successorInjectivity
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.zeroIsNotSucc

/**
 * Backwards-compatibility facade for the former `UsefulTheorems` grab-bag.
 *
 * The generic lemmas have been split out into:
 *   - [[PropositionalFacts]] — propositional / equivalence / equality lemmas
 *   - [[FunctionFacts]] — subset / union / range / (restricted) function lemmas
 *   - [[ExtendedInteger]] — ω / S facts
 *
 * They are re-exported here so existing imports keep resolving. Only the
 * ADT-specific [[constructorTagDisequality]] still lives in this file.
 */
object UsefulTheorems {

  export PropositionalFacts.*
  export FunctionFacts.*

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
          S(midMaxTag) === S(midMinTag) |- midMaxTag === midMinTag
        ) by Cut(
          successorInjectivity of (n := midMaxTag, m := midMinTag),
          equivalenceApply of (
            p1 := S(midMaxTag) === S(midMinTag),
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

}
