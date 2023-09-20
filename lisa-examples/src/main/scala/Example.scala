import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.mathematics.settheory.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.Substitution
import lisa.prooflib.Substitution.ApplyRules
import lisa.utils.FOLPrinter.*
import lisa.utils.KernelHelpers.checkProof
import lisa.utils.unification.UnificationUtils.*


object Example extends lisa.Main {

  val x = variable
  val y = variable
  val P = predicate[1]
  val f = function[1]

  // Simple Theorem with LISA's DSL
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    assume(∀(x, P(x) ==> P(f(x))))
    assume(P(x))
    val step1 = have(P(x) ==> P(f(x))) by InstantiateForall
    val step2 = have(P(f(x)) ==> P(f(f(x)))) by InstantiateForall
    have(thesis) by Tautology.from(step1, step2)
  }

  //Example of set theoretic development

  /**
   * Theorem --- If a set has an element, then it is not the empty set.
   *
   *    `y ∈ x ⊢ ! x = ∅`
   */
  val setWithElementNonEmpty = Theorem(
    in(y, x) |- !(x === ∅)
  ) {
    have((x === ∅) |- !in(y, x)) by Substitution.ApplyRules(x === ∅)(emptySetAxiom of (x := y))
  }


  /**
   * Theorem --- The empty set is a subset of every set.
   *
   *    `∅ ⊆ x`
   */
  val emptySetIsASubset = Theorem(
    subset(∅, x)
  ) {
    have(in(y, ∅) ==> in(y, x)) by Weakening(emptySetAxiom of (x:= y))
    val rhs = thenHave(∀(y, in(y, ∅) ==> in(y, x))) by RightForall
    have(thesis) by Tautology.from(subsetAxiom of (x := ∅, y := x), rhs)
  }


  /**
   * Theorem --- A power set is never empty.
   *
   *    `!P(x) = ∅`
   */
  val powerSetNonEmpty = Theorem(
    !(powerSet(x) === ∅)
  ) {
    have(thesis) by Tautology.from(setWithElementNonEmpty of (y := ∅, x := powerSet(x)), powerAxiom of (x:= ∅, y:=x), emptySetIsASubset)
  }









  // Examples of definitions
  val succ = DEF(x) --> union(unorderedPair(x, singleton(x)))
  show

  val inductiveSet = DEF(x) --> in(∅, x) /\ forall(y, in(y, x) ==> in(succ(y), x))
  show


  // Simple tactic definition for LISA DSL
  import lisa.automation.kernel.OLPropositionalSolver.*

  // object SimpleTautology extends ProofTactic {
  //   def solveFormula(using proof: library.Proof)(f: Formula, decisionsPos: List[Formula], decisionsNeg: List[Formula]): proof.ProofTacticJudgement = {
  //     val redF = reducedForm(f)
  //     if (redF == ⊤) {
  //       Restate(decisionsPos |- f :: decisionsNeg)
  //     } else if (redF == ⊥) {
  //       proof.InvalidProofTactic("Sequent is not a propositional tautology")
  //     } else {
  //       val atom = findBestAtom(redF).get
  //       def substInRedF(f: Formula) = redF.substituted(atom -> f)
  //       TacticSubproof {
  //         have(solveFormula(substInRedF(⊤), atom :: decisionsPos, decisionsNeg))
  //         val step2 = thenHave(atom :: decisionsPos |- redF :: decisionsNeg) by Substitution2(⊤ <=> atom)
  //         have(solveFormula(substInRedF(⊥), decisionsPos, atom :: decisionsNeg))
  //         val step4 = thenHave(decisionsPos |- redF :: atom :: decisionsNeg) by Substitution2(⊥ <=> atom)
  //         have(decisionsPos |- redF :: decisionsNeg) by Cut(step4, step2)
  //         thenHave(decisionsPos |- f :: decisionsNeg) by Restate
  //       }
  //     }
  //   }
  //   def solveSequent(using proof: library.Proof)(bot: Sequent) =
  //     TacticSubproof { // Since the tactic above works on formulas, we need an extra step to convert an arbitrary sequent to an equivalent formula
  //       have(solveFormula(sequentToFormula(bot), Nil, Nil))
  //       thenHave(bot) by Restate.from
  //     }
  // }

  // val a = formulaVariable()
  // val b = formulaVariable()
  // val c = formulaVariable()
  // val testTheorem = Lemma((a /\ (b \/ c)) <=> ((a /\ b) \/ (a /\ c))) {
  //   have(thesis) by SimpleTautology.solveSequent
  // }
  // show

}
