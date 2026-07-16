package lisa.maths.SetTheory.Relations
package Operations

import lisa.maths.SetTheory.Base.Predef.{_, given}

import Relation._

/**
 * The converse of a relation `R` is the relation `R^T` such that `(x, y) ∈ R^T`
 * if and only if `(y, x) ∈ R`.
 */
object Converse extends lisa.Main {

  /**
   * Definition --- The converse of a relation `R` is the relation `R^T` such that
   * `(x, y) ∈ R^T` if `(y, x) ∈ R`.
   */
  val converse = DEF(λ(R, { (snd(z), fst(z)) | z ∈ R })).printAs(args => {
    val R = args(0)
    s"${R}^T"
  })

  /**
   * Theorem --- The converse operation is involutive, i.e., `(R^T)^T = R`,
   * provided that `R` is a relation.
   */
  val involution = Theorem(
    relation(R) |- converse(converse(R)) === R
  ) {
    assume(relation(R))

    // Membership in converse(R): x ∈ converse(R) <=> ∃(z ∈ R, (snd(z), fst(z)) === x)
    have(x ∈ { (snd(z), fst(z)) | z ∈ R } <=> ∃(z ∈ R, (snd(z), fst(z)) === x)) by Replacement.apply
    val innerMemb = thenHave(x ∈ converse(R) <=> ∃(z ∈ R, (snd(z), fst(z)) === x)) by Substitute(converse.definition)

    // Membership in converse(converse(R)): a ∈ converse(converse(R)) <=> ∃(x ∈ converse(R), (snd(x), fst(x)) === a)
    have(a ∈ { (snd(x), fst(x)) | x ∈ converse(R) } <=> ∃(x ∈ converse(R), (snd(x), fst(x)) === a)) by Replacement.apply
    val outerMemb = thenHave(a ∈ converse(converse(R)) <=> ∃(x ∈ converse(R), (snd(x), fst(x)) === a)) by Substitute(converse.definition)

    // === Forward: a ∈ converse(converse(R)) → a ∈ R ===
    // Given witnesses z ∈ R, (snd(z), fst(z)) === x, (snd(x), fst(x)) === a:
    //   fst(x) = fst((snd(z), fst(z))) = snd(z)
    //   snd(x) = snd((snd(z), fst(z))) = fst(z)
    //   (snd(x), fst(x)) = (fst(z), snd(z)) = z (by inversion) = a
    have((z ∈ R, (snd(z), fst(z)) === x, (snd(x), fst(x)) === a) |- a ∈ R) by Congruence.from(
      Pair.pairFst of (x := snd(z), y := fst(z)),
      Pair.pairSnd of (x := snd(z), y := fst(z)),
      BasicTheorems.inversion
    )
    thenHave((z ∈ R /\ ((snd(z), fst(z)) === x), (snd(x), fst(x)) === a) |- a ∈ R) by Restate
    thenHave((∃(z, z ∈ R /\ ((snd(z), fst(z)) === x)), (snd(x), fst(x)) === a) |- a ∈ R) by LeftExists
    thenHave((x ∈ converse(R), (snd(x), fst(x)) === a) |- a ∈ R) by Tautology.fromLastStep(innerMemb)
    thenHave(x ∈ converse(R) /\ ((snd(x), fst(x)) === a) |- a ∈ R) by Restate
    thenHave(∃(x, x ∈ converse(R) /\ ((snd(x), fst(x)) === a)) |- a ∈ R) by LeftExists
    val fwd = thenHave(a ∈ converse(converse(R)) ==> (a ∈ R)) by Tautology.fromLastStep(outerMemb)

    // === Backward: a ∈ R → a ∈ converse(converse(R)) ===

    // Step 1: a ∈ R |- (snd(a), fst(a)) ∈ converse(R)
    // Witness z := a gives: a ∈ R /\ (snd(a), fst(a)) === (snd(a), fst(a))
    have(a ∈ R |- a ∈ R /\ ((snd(a), fst(a)) === (snd(a), fst(a)))) by Restate
    thenHave(a ∈ R |- ∃(z, z ∈ R /\ ((snd(z), fst(z)) === (snd(a), fst(a))))) by RightExists
    val inConv = thenHave(a ∈ R |- (snd(a), fst(a)) ∈ converse(R)) by Tautology.fromLastStep(
      innerMemb of (x := (snd(a), fst(a)))
    )

    // Step 2: (snd(a), fst(a)) ∈ converse(R) |- (fst(a), snd(a)) ∈ converse(converse(R))
    // Witness x := (snd(a), fst(a)), and (snd(x), fst(x)) = (fst(a), snd(a)) by pairSnd/pairFst
    val pairSwap = have((snd((snd(a), fst(a))), fst((snd(a), fst(a)))) === (fst(a), snd(a))) by Congruence.from(
      Pair.pairSnd of (x := snd(a), y := fst(a)),
      Pair.pairFst of (x := snd(a), y := fst(a))
    )
    have(
      (snd(a), fst(a)) ∈ converse(R) |-
        (snd(a), fst(a)) ∈ converse(R) /\ ((snd((snd(a), fst(a))), fst((snd(a), fst(a)))) === (fst(a), snd(a)))
    ) by Tautology.from(pairSwap)
    thenHave(
      (snd(a), fst(a)) ∈ converse(R) |-
        ∃(x, x ∈ converse(R) /\ ((snd(x), fst(x)) === (fst(a), snd(a))))
    ) by RightExists
    val step2 = thenHave(
      (snd(a), fst(a)) ∈ converse(R) |-
        (fst(a), snd(a)) ∈ converse(converse(R))
    ) by Tautology.fromLastStep(outerMemb of (a := (fst(a), snd(a))))

    // Step 3: a = (fst(a), snd(a)) by inversion
    val invA = have(a ∈ R |- a === (fst(a), snd(a))) by Restate.from(BasicTheorems.inversion of (z := a))

    // Step 4: Chain to get a ∈ converse(converse(R))
    have(a ∈ R |- (fst(a), snd(a)) ∈ converse(converse(R))) by Tautology.from(inConv, step2)
    thenHave(a ∈ R |- a ∈ converse(converse(R))) by Substitute(invA)
    val bwd = thenHave(a ∈ R ==> (a ∈ converse(converse(R)))) by Restate

    // Combine both directions
    have(a ∈ converse(converse(R)) <=> a ∈ R) by Tautology.from(fwd, bwd)
    thenHave(thesis) by Extensionality
  }
}
