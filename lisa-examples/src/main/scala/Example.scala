import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.mathematics.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.utils.FOLPrinter.*
import lisa.utils.KernelHelpers.checkProof
import lisa.utils.unification.UnificationUtils.*

/**
 * Discover some of the elements of LISA to get started.
 */
object Example {

  import lisa.kernel.proof.SequentCalculus.*

  def main(args: Array[String]): Unit = {
    val phi = formulaVariable()
    val psi = formulaVariable()
    val PierceLaw = SCProof(
      Hypothesis(phi |- phi, phi),
      Weakening(phi |- (phi, psi), 0),
      RightImplies(() |- (phi, phi ==> psi), 1, phi, psi),
      LeftImplies((phi ==> psi) ==> phi |- phi, 2, 0, (phi ==> psi), phi),
      RightImplies(() |- ((phi ==> psi) ==> phi) ==> phi, 3, (phi ==> psi) ==> phi, phi)
    )

    checkProof(PierceLaw)

    val theory = new RunningTheory
    val pierceThm: theory.Theorem = theory.makeTheorem("Pierce's Law", () |- ((phi ==> psi) ==> phi) ==> phi, PierceLaw, Seq.empty).get
  }

}

object ExampleDSL extends lisa.Main {

  //Simple Theorem with Scala DSL
  val x = variable
  val P = predicate(1)
  val f = function(1)
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    assume(∀(x, P(x) ==> P(f(x))))
    assume(P(x))
    val step1 = have(P(x) ==> P(f(x))) by InstantiateForall
    val step2 = have(P(f(x)) ==> P(f(f(x)))) by InstantiateForall
    have(thesis) by Tautology.from(step1, step2)
  }
  show

  //More complicated example of a proof with LISA DSL
  val y = variable
  val z = variable
  val unionOfSingleton = Theorem(union(singleton(x)) === x) {
    val X = singleton(x)
    val forward = have(in(z, x) ==> in(z, union(X))) subproof {
      have(in(z, x) |- in(z, x) /\ in(x, X)) by Tautology.from(pairAxiom of (y -> x, z -> x))
      val step2 = thenHave(in(z, x) |- ∃(y, in(z, y) /\ in(y, X))) by RightExists
      have(thesis) by Tautology.from(step2, unionAxiom of (x -> X))
    }

    val backward = have(in(z, union(X)) ==> in(z, x)) subproof {
      have(in(z, y) |- in(z, y)) by Restate
      val step2 = thenHave((y === x, in(z, y)) |- in(z, x)) by Substitution
      have(in(z, y) /\ in(y, X) |- in(z, x)) by Tautology.from(pairAxiom of (y -> x, z -> y), step2)
      val step4 = thenHave(∃(y, in(z, y) /\ in(y, X)) |- in(z, x)) by LeftExists
      have(in(z, union(X)) ==> in(z, x)) by Tautology.from(unionAxiom of (x -> X), step4)
    }

    have(in(z, union(X)) <=> in(z, x)) by RightIff(forward, backward)
    thenHave(forall(z, in(z, union(X)) <=> in(z, x))) by RightForall
    andThen(Substitution(extensionalityAxiom of (x -> union(X), y -> x)))
  }
  show

  //Examples of definitions
  val succ = DEF(x) --> union(unorderedPair(x, singleton(x)))
  show

  val inductiveSet = DEF(x) --> in(∅, x) /\ forall(y, in(y, x) ==> in(succ(y), x))
  show

  val defineNonEmptySet = Lemma(" |- ∃!'x. !('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet)") {
    val subst = have("|- False <=> elem(emptySet, emptySet)") by Rewrite(emptySetAxiom of (x -> emptySet()))
    have(" elem(emptySet, unorderedPair(emptySet, emptySet))<=>False |- ") by Rewrite(pairAxiom of (x -> emptySet(), y -> emptySet(), z -> emptySet()))
    andThen(applySubst(subst))
    thenHave(" ∀'z. elem('z, unorderedPair(emptySet, emptySet)) ⇔ elem('z, emptySet) |- ") by LeftForall
    andThen(applySubst(extensionalityAxiom of (x -> unorderedPair(emptySet(), emptySet()), y -> emptySet())))
    andThen(applySubst(x === unorderedPair(emptySet(), emptySet())))
    thenHave(" |- (!('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet)) <=> ('x=unorderedPair(emptySet, emptySet))") by Tautology
    thenHave(" |- ∀'x. ('x=unorderedPair(emptySet, emptySet)) <=> (!('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet))") by RightForall
    thenHave(" |- ∃'y. ∀'x. ('x='y) <=> (!('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet))") by RightExists
  }
  show

  //This definition is underspecified
  val nonEmpty = DEF() --> The(x, !(x === ∅))(defineNonEmptySet)
  show


  //Simple tactic definition for LISA DSL
  import lisa.automation.kernel.OLPropositionalSolver.*

  object SimpleTautology extends ProofTactic {
    def solveFormula(using proof: library.Proof)(f: Formula, decisionsPos: List[Formula], decisionsNeg: List[Formula]): proof.ProofTacticJudgement = {
      val redF = reducedForm(f)
      if (redF == ⊤) {
        Restate(decisionsPos |- f :: decisionsNeg)
      } else if (redF == ⊥) {
        proof.InvalidProofTactic("Sequent is not a propositional tautology")
      } else {
        val atom = findBestAtom(redF).get
        def substInRedF(f: Formula) = redF.substituted(atom -> f)
        TacticSubproof {
          have(solveFormula(substInRedF(⊤), atom :: decisionsPos, decisionsNeg))
          val step2 = thenHave(atom :: decisionsPos |- redF :: decisionsNeg) by Substitution(⊤ <=> atom)
          have(solveFormula(substInRedF(⊥), decisionsPos, atom :: decisionsNeg))
          val step4 = thenHave(decisionsPos |- redF :: atom :: decisionsNeg) by Substitution(⊥ <=> atom)
          have(decisionsPos |- redF :: decisionsNeg) by Cut(step4, step2)
          thenHave(decisionsPos |- f :: decisionsNeg) by Restate.from
        }
      }
    }
    def solveSequent(using proof: library.Proof)(bot: Sequent) =
      TacticSubproof { // Since the tactic above works on formulas, we need an extra step to convert an arbitrary sequent to an equivalent formula
        have(solveFormula(sequentToFormula(bot), Nil, Nil))
        thenHave(bot) by Restate.from
      }
  }

  val a = formulaVariable()
  val b = formulaVariable()
  val c = formulaVariable()
  val testTheorem = Lemma((a /\ (b \/ c)) <=> ((a /\ b) \/ (a /\ c))) {
    have(thesis) by SimpleTautology.solveSequent
  }
  show

}
