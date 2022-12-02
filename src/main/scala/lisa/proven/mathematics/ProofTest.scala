package lisa.proven.mathematics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.utils.Printer.*
import lisa.automation.kernel.Destructors.*
import lisa.automation.kernel.ProofTactics.*
import lisa.proven.mathematics.ProofTest.unorderedPair
import lisa.utils.tactics.*

object ProofTest extends lisa.Main {

  /**
   * val pr1 = SC.InstFunSchema(() |- in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z), -1, Map(x -> LambdaTermTerm(Seq(), y), y -> LambdaTermTerm(Seq(), x)))
   * val pr2 = SC.RightSubstIff(
   * Sequent(pr1.bot.right, Set(in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))),
   * -1,
   * List(((x === z) \/ (y === z), in(z, unorderedPair(y, x)))),
   * LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h)
   * )
   * val pr3 = SC.Cut(Sequent(pr1.bot.left, pr2.bot.right), 0, 1, pr2.bot.left.head)
   * val pr4 = SC.RightForall(Sequent(Set(), Set(forall(z, pr2.bot.right.head))), 2, pr2.bot.right.head, z)
   * SCProof(steps( pr1, pr2, pr3, pr4), imports(ax"pairAxiom"))* */
THEOREM("unorderedPair_symmetry") of
    "⊢ ∀'y. ∀'x. unordered_pair('x, 'y) = unordered_pair('y, 'x)" PROOF {
      val x = VariableLabel("x")
      val y = VariableLabel("y")
      val z = VariableLabel("z")
      val h = VariableFormulaLabel("h")

      val objectiveA : Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))
      val objectiveB : Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x))
      assume(ax"extensionalityAxiom")
      assume(ax"pairAxiom")

      have(objectiveA) by SUBPROOF {
          assume(ax"pairAxiom")
          have(() |- in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z)) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), y), y -> LambdaTermTerm(Seq(), x)))(ax"pairAxiom")
          have(in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z) |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by RightSubstIff(List(((x === z) \/ (y === z), in(z, unorderedPair(y, x)))),
          LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h))(-1)
          andThen(() |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by Cut(in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z))
          andThen(() |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))) by RightForall
      }

      have(objectiveB) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), unorderedPair(x, y)), y -> LambdaTermTerm(Seq(), unorderedPair(y, x))))(ax"extensionalityAxiom")
      andThen(unorderedPair(x, y) === unorderedPair(y, x)) by ByEquiv(objectiveB.right.head, objectiveA.right.head)
      andThen(forall(y, forall(x, unorderedPair(x, y) === unorderedPair(y, x)))) by GeneralizeToForall(x, y)
    }
  show

    
}