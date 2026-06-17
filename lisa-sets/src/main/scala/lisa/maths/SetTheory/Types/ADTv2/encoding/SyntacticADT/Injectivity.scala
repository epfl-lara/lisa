package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.constructorTagDisequality
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTInjectivity[N <: Arity] extends SyntacticADTBase[N] {
  this: SyntacticADT[N] =>

  // ***************
  // * INJECTIVITY *
  // ***************

  /**
   *  Theorem --- Injectivity of constructors.
   *
   *  Two instances of different construcors are always different.
   *
   *  e.g. Nil != Cons(head, tail)
   */
  def injectivity(c1: SyntacticConstructor, c2: SyntacticConstructor) =
    require(c1.tag != c2.tag, "The given constructors must be different.")

    Lemma(using name = s"ADT_${name}_disjointness")(c1.term1 =/= c2.term2) {

      // STEP 0: Caching
      val tagTerm1 = c1.tagTerm
      val tagTerm2 = c2.tagTerm

      // STEP 1: Prove that the tags are different
      val diffTag = constructorTagDisequality(tagTerm1, tagTerm2, Math.min(c1.tag, c2.tag), Math.max(c1.tag, c2.tag))

      // STEP 2: Prove that the terms are different if the tags are different

      have(
        ((c1.tagTerm, c1.subterm) === (c2.tagTerm, c2.subterm2)) |- (c1.tagTerm === c2.tagTerm) /\ (c1.subterm === c2.subterm2)
      ) by Tautology.from(
        Pair.extensionality of (
          a := c1.tagTerm,
          b := c1.subterm,
          c := c2.tagTerm,
          d := c2.subterm2
        )
      )
      thenHave(
        c1.term1 === c2.term2 |- tagTerm1 === tagTerm2
      ) by Tautology
      thenHave(
        !(tagTerm1 === tagTerm2) |- !(c1.term1 === c2.term2)
      ) by Tautology

      // STEP 3: Conclude
      have(!(c1.term1 === c2.term2)) by Cut(diffTag, lastStep)
    }
}
