package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.show
import lisa.utils.Helpers.{_, given}
import lisa.utils.Printer.*
import lisa.utils.tactics.ProofStepLib.ProofStep
import lisa.automation.kernel.Destructors.*
import lisa.automation.kernel.ProofTactics.*


object ProofTest extends lisa.Main {
  

THEOREM("unorderedPair_symmetry") of
    "⊢ ∀'y. ∀'x. unordered_pair('x, 'y) = unordered_pair('y, 'x)" PROOF2 {
      val x = VariableLabel("x")
      val y = VariableLabel("y")
      val z = VariableLabel("z")
      val h = VariableFormulaLabel("h")
      val fin = SC.SCSubproof(
        {
          val pr0 = have(() |- pairAxiom) by Rewrite(-1)
          
          val pr1 = have(() |- in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z)) by Rewrite(pr0)
          val pr2 = have(Sequent(pr1.bot.right, Set(in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))))) by RightSubstIff(

            List(((x === z) \/ (y === z), in(z, unorderedPair(y, x)))),
            LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h)
         )

          val pr3 = SC.Cut(Sequent(pr1.bot.left, pr2.bot.right), 1, 2, pr2.bot.left.head)
          val pr4 = SC.RightForall(Sequent(Set(), Set(forall(z, pr2.bot.right.head))), 3, pr2.bot.right.head, z)
          SCProof(steps(pr0, pr1, pr2, pr3, pr4), imports(ax"pairAxiom"))
        },
        Seq(-2)
      )
      val pairExt = SC.SCSubproof(
        {
          val pairExt1 = instantiateForall(SCProof(steps(), imports(ax"extensionalityAxiom")), ax"extensionalityAxiom", unorderedPair(x, y))
          instantiateForall(pairExt1, pairExt1.conclusion.right.head, unorderedPair(y, x))
        },
        Seq(-1)
      )
      val fin2 = byEquiv(
        pairExt.bot.right.head,
        fin.bot.right.head
      )(pairExt, fin)
      val fin3 = generalizeToForall(fin2, fin2.conclusion.right.head, x)
      val fin4 = generalizeToForall(fin3, fin3.conclusion.right.head, y)
      fin4.copy(imports = imports(ax"extensionalityAxiom", ax"pairAxiom"))
    } using (ax"extensionalityAxiom", AxiomaticSetTheory.pairAxiom)
  show

    
}