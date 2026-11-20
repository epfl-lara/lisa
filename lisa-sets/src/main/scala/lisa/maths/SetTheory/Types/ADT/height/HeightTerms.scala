package lisa.maths.SetTheory.Types.ADT.height

import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base._
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Functions.UnionRange.unionRangeMembership
import lisa.maths.SetTheory.Ordinals.Integer.emptyInOmega
import lisa.maths.SetTheory.Ordinals.Integer.unionInOmega
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.height.FiniteUnion.memberSubsetOfUnionList
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.tactics.Cuts
import lisa.maths.SetTheory.Types.ADT.syntax.AST._
import lisa.utils.prooflib.Thm

/**
 * Relates carrier membership and constructor argument typing to finite height stages.
 */
final class HeightTerms(
    base: HeightADT,
    constructorsTheory: HeightConstructors,
    constructors: Seq[HeightConstructorData],
    term: Expr[Ind],
    termEqualsUnion: Theorem
) {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def constructorVarsInDomain(
      c: HeightConstructorData,
      s: Expr[Ind]
  ): Expr[Prop] = wellTypedFormula(c.signature)(s)

  /**
   * Characterizes carrier membership by membership in some finite stage.
   */
  val termHasHeight = Lemma.generated(
    base.isHeight(h) |- x ∈ term <=> ∃(n, n ∈ N /\ x ∈ app(h, n))
  ) {
    // Unfold isHeight(h) to extract function(h) and dom(h) === N.
    val hFunction = have(base.isHeight(h) |- function(h)) by Weakening(base.heightIsCore)
    val hDom = have(base.isHeight(h) |- dom(h) === N) by Weakening(base.heightIsCore)

    // Membership in ⋃range(h) unfolds to an existential over the domain of h.
    val unionMem =
      have(base.isHeight(h) |- x ∈ ⋃(range(h)) <=> ∃(n, n ∈ dom(h) /\ x ∈ app(h, n))) by
        Cut(hFunction, unionRangeMembership of (z := x))

    // Rewrite the carrier and the domain using their defining equalities.
    val termExistsDom =
      have(base.isHeight(h) |- x ∈ term <=> ∃(n, n ∈ dom(h) /\ x ∈ app(h, n))) by
        Substitute(termEqualsUnion)(unionMem)
    have(thesis) by Substitute(hDom)(termExistsDom)
  }

  /**
   * Gives every constructor's arguments a common stage, keeping payload typing unchanged.
   */
  val termsHaveHeight = constructors.map { c =>
    c -> Lemma.generated(
      base.isHeight(h) |-
        (constructorVarsInDomain(c, term) <=>
          ∃(n, n ∈ N /\ constructorVarsInDomain(c, app(h, n))))
    ) {
      val recursiveArgs = c.signature.collect { case (v, SelfRef) => v }
      val payloadTyping = seqAnd(c.signature.collect { case (v, ty: TypeArg) => v ∈ ty.getOrElse(term) })
      val atTerm = constructorVarsInDomain(c, term)
      val atStage = n ∈ N /\ constructorVarsInDomain(c, app(h, n))

      val backward = have(base.isHeight(h) |- ∃(n, atStage) ==> atTerm) subproof {
        val recursiveAtTerm = recursiveArgs.map { v =>
          have((base.isHeight(h), atStage) |- n ∈ N /\ v ∈ app(h, n)) by Restate
          thenHave((base.isHeight(h), atStage) |- ∃(n, n ∈ N /\ v ∈ app(h, n))) by RightExists
          have((base.isHeight(h), atStage) |- v ∈ term) by
            Substitute(termHasHeight of (x := v))(lastStep)
        }
        val payloads = have((base.isHeight(h), atStage) |- payloadTyping) by Restate
        have((base.isHeight(h), atStage) |- atTerm) by RightAnd(((payloads +: recursiveAtTerm)).map(_.kernel))
        thenHave((base.isHeight(h), ∃(n, atStage)) |- atTerm) by LeftExists
      }

      val forward = have(base.isHeight(h) |- atTerm ==> ∃(n, atStage)) subproof { sp ?=>
        // Only recursive fields need stage witnesses. Payload types do not depend on the stage.
        val witnesses = recursiveArgs.map { v =>
          val exStage = ∃(n, n ∈ N /\ v ∈ app(h, n))
          val existsStage = have((base.isHeight(h), atTerm) |- exStage) by
            Substitute(termHasHeight of (x := v))(have((base.isHeight(h), atTerm) |- v ∈ term) by Restate)
          val wh = ε(n, n ∈ N /\ v ∈ app(h, n))
          val whProp = have(exStage |- wh ∈ N /\ v ∈ app(h, wh)) by
            Restate.from(existsEpsilon of (x := n, P := λ(n, n ∈ N /\ v ∈ app(h, n))))
          val whBoth = have((base.isHeight(h), atTerm) |- wh ∈ N /\ v ∈ app(h, wh)) by Cut(existsStage, whProp)
          val whInNat = have((base.isHeight(h), atTerm) |- wh ∈ N) by Weakening(whBoth)
          val whBody = have((base.isHeight(h), atTerm) |- v ∈ app(h, wh)) by Weakening(whBoth)
          (v, wh, whInNat, whBody)
        }

        // The empty union gives stage zero for constructors with no recursive fields.
        val stages = witnesses.map(_._2)
        val zeroInNat = have((base.isHeight(h), atTerm) |- ∅ ∈ N) by Weakening(emptyInOmega)
        val (commonStage, commonInNat) = witnesses.foldLeft[(Expr[Ind], Thm)]((∅, zeroInNat)) { case ((previous, previousInNat), (_, wh, whInNat, _)) =>
          val next = previous ∪ wh
          val unionStep = have((previous ∈ N, wh ∈ N) |- next ∈ N) by
            Restate.from(unionInOmega of (a := previous, b := wh))
          val step = have((base.isHeight(h), atTerm, wh ∈ N) |- next ∈ N) by
            Cut(previousInNat, unionStep)
          val nextInNat = have((base.isHeight(h), atTerm) |- next ∈ N) by Cut(whInNat, step)
          (next, nextInNat)
        }

        val recursiveAtCommon = witnesses.map { (v, wh, whInNat, whBody) =>
          val included = have(wh ⊆ commonStage) by Restate.from(memberSubsetOfUnionList(stages, wh))
          have((base.isHeight(h), atTerm) |- v ∈ app(h, commonStage)) by
            Cuts(constructorsTheory.heightMembershipMonotonic of (x := v, m := wh, n := commonStage))(
              commonInNat,
              whInNat,
              included,
              whBody
            )
        }
        val payloads = have((base.isHeight(h), atTerm) |- payloadTyping) by Restate
        have((base.isHeight(h), atTerm) |- commonStage ∈ N /\ constructorVarsInDomain(c, app(h, commonStage))) by
          RightAnd(((commonInNat +: payloads +: recursiveAtCommon)).map(_.kernel))
        thenHave((base.isHeight(h), atTerm) |- ∃(n, atStage)) by RightExists
      }

      have(thesis) by RightIff(forward, backward)
    }
  }.toMap

}
