package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.UsefullTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*

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
      val diffTag = have(!(tagTerm1 === tagTerm2)) subproof {

        // STEP 1.1: Order the tags
        val minTag: Int = Math.min(c1.tag, c2.tag)
        val maxTag: Int = Math.max(c1.tag, c2.tag)

        val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by
          Congruence //.from(tagTerm1.definition, tagTerm2.definition)

        // STEP 1.2: Apply successor injectivity to both tags until one becomes 0
        (1 to minTag).foldLeft(start)((fact, i) =>
          val midMaxTag = toTerm(maxTag - i)
          val midMinTag = toTerm(minTag - i)
          have(
            successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag
          ) by Cut(
            successorInjectivity of (n := midMaxTag, m := midMinTag),
            equivalenceApply of
              (
                p1 := successor(midMaxTag) === successor(midMinTag),
                p2 := midMaxTag === midMinTag
              )
          )
          have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
        )

        val chainInjectivity =
          thenHave(!(toTerm(maxTag - minTag) === ∅) |- !(tagTerm1 === tagTerm2)) by
            Restate

        // STEP 1.3: Conclude using the fact that 0 is not the successor of any number
        have(toTerm(maxTag - minTag) =/= ∅) by Restate.from(
          zeroIsNotSucc of (n := toTerm(maxTag - minTag - 1))
        )
        have(thesis) by Cut(lastStep, chainInjectivity)
      }

      // STEP 2: Prove that the terms are different if the tags are different

      have(
        ((c1.tagTerm, c1.subterm) === (c2.tagTerm, c2.subterm)) |- (c1.tagTerm === c2.tagTerm) /\ (c1.subterm === c2.subterm)
      ) by Tautology.from(
        Pair.extensionality of (
          a := c1.tagTerm,
          b := c1.subterm,
          c := c2.tagTerm,
          d := c2.subterm2
      ))
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
