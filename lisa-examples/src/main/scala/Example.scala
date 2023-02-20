import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.mathematics.SetTheory.*
import lisa.utils.FOLPrinter.*
import lisa.utils.KernelHelpers.checkProof

/**
 * Discover some of the elements of LISA to get started.
 */
object Example {

  import lisa.kernel.proof.SequentCalculus.*
  val phi = formulaVariable()
  val psi = formulaVariable()
  val PierceLaw = SCProof(
    Hypothesis(phi |- phi, phi),
    Weakening(phi |- (phi, psi), 0),
    RightImplies(() |- (phi, phi ==> psi), 1, phi, psi),
    LeftImplies((phi ==> psi) ==> phi |- phi, 2, 0, (phi ==> psi), phi),
    RightImplies(() |- ((phi ==> psi) ==> phi) ==> phi, 3, (phi ==> psi) ==> phi, phi)
  )
  def main(args: Array[String]): Unit = {
    checkProof(PierceLaw)
  }

}

object Example2 extends lisa.Main {

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

  val succ = DEF(x) --> union(unorderedPair(x, singleton(x)))
  show

  val inductiveSet = DEF(x) --> in(∅, x) /\ forall(y, in(y, x) ==> in(succ(y), x))
  show

  val defineNonEmptySet = Theorem(" |- ∃!'x. !('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet)") {
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

  val nonEmpty = DEF() --> The(x, !(x === ∅))(defineNonEmptySet)
  show

  /*
  def solveFormula(f: Formula,
                   decisionsPos: List[Formula],
                   decisionsNeg: List[Formula]): ProofStep = {
    val redF = reduceWithFol2(f)
    if (redF == top()) {
      Restate(decisionsPos |- f :: decisionsNeg)
    } else if (redF == bot()) {
      val unprovableSequent = decisionsPos |- f :: decisionsNeg
      ProofStepFailure(unprovableSequent)
    } else {
      val atom = findBestAtom(redF)
      val splitF: Formula => Formula = (x => redF[atom := x])
      new TacticSubproof {
        have(atom :: decisionsPos |- splitF(top()) :: decisionsNeg) by solveFormula(splitF(top()), atom :: decisionsPos, decisionsNeg)
        val step2 = thenHave(atom :: decisionsPos |- redF :: decisionsNeg) by Substitution
          have(decisionsPos |- splitF(bot()) :: atom :: decisionsNeg) by solveFormula(splitF(bot()), decisionsPos, atom :: decisionsNeg)
        val step4 = thenHave(decisionsPos |- redF :: atom :: decisionsNeg) by Substitution
          thenHave(decisionsPos |- redF :: decisionsNeg) by Cut (atom)(step2, step4)
        thenHave(decisionsPos |- f :: decisionsNeg) by Restate
      }
    }
  }
   */
}
