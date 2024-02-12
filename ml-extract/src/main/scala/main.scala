import lisa.utils.parsing.ProofPrinter._
import lisa.utils.FOLPrinter.*

import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.K
import lisa.prooflib.ProofTacticLib.*

// def sequent2code(sq: Sequent): String = prettySequent(sq).replace("⊢", "|-").replace("'", "")
def sequent2code(sq: Sequent): String = toFront(sq).toString

def scproof2code(p: K.SCProof): String = {
  p.steps.map(scproofstep2line).mkString("\n")
}
def scproofstep2line(ps: SCProofStep): String = {
  ps match {
    case Restate(bot, t1) => "have(" + sequent2code(bot) + ") by Restate"
    case RestateTrue(bot) => "have(" + sequent2code(bot) + ") by Restate"
    case Hypothesis(bot, phi) => "have(" + sequent2code(bot) + ") by Hypothesis"
    case Cut(bot, t1, t2, phi) => "have(" + sequent2code(bot) + ") by Cut"
    case LeftAnd(bot, t1, t2, phi) => "have(" + sequent2code(bot) + ") by LeftAnd"
    case LeftOr(bot, t1, disjuncts) => "have(" + sequent2code(bot) + ") by LeftOr"
    case LeftImplies(bot, t1, t2, phi, psi) => "have(" + sequent2code(bot) + ") by LeftImplies"
    case LeftIff(bot, t1, phi, psi) => "have(" + sequent2code(bot) + ") by LeftIff"
    case LeftNot(bot, t1, phi) => "have(" + sequent2code(bot) + ") by LeftNot"
    case LeftForall(bot, t1, phi, x, t) => "have(" + sequent2code(bot) + ") by LeftForall"
    case LeftExists(bot, t1, phi, x) => "have(" + sequent2code(bot) + ") by LeftExists"
    case LeftExistsOne(bot, t1, phi, x) => "have(" + sequent2code(bot) + ") by LeftExistsOne"
    case RightAnd(bot, t, conjuncts) => "have(" + sequent2code(bot) + ") by RightAnd"
    case RightOr(bot, t1, phi, psi) => "have(" + sequent2code(bot) + ") by RightOr"
    case RightImplies(bot, t1, phi, psi) => "have(" + sequent2code(bot) + ") by RightImplies"
    case RightIff(bot, t1, t2, phi, psi) => "have(" + sequent2code(bot) + ") by RightIff"
    case RightNot(bot, t1, phi) => "have(" + sequent2code(bot) + ") by RightNot"
    case RightForall(bot, t1, phi, x) => "have(" + sequent2code(bot) + ") by RightForall"
    case RightExists(bot, t1, phi, x, t) => "have(" + sequent2code(bot) + ") by RightExists"
    case RightExistsOne(bot, t1, phi, x) => "have(" + sequent2code(bot) + ") by RightExistsOne"
    case Weakening(bot, t1) => "have(" + sequent2code(bot) + ") by Weakening"
    case LeftRefl(bot, t1, phi) => "have(" + sequent2code(bot) + ") by LeftRefl"
    case RightRefl(bot, phi) => "have(" + sequent2code(bot) + ") by RightRefl"
    case LeftSubstEq(bot, t1, equals, lambdaPhi) => "have(" + sequent2code(bot) + ") by LeftSubstEq"
    case RightSubstEq(bot, t1, equals, lambdaPhi) => "have(" + sequent2code(bot) + ") by RightSubstEq"
    case LeftSubstIff(bot, t1, equals, lambdaPhi) => "have(" + sequent2code(bot) + ") by LeftSubstIff"
    case RightSubstIff(bot, t1, equals, lambdaPhi) => "have(" + sequent2code(bot) + ") by RightSubstIff"
    case InstSchema(bot, t1, mCon, mPred, mTerm) => "have(" + sequent2code(bot) + ") by InstSchema"
    case sp @ SCSubproof(_, _) =>
      if sp.sp.length == 1 then scproofstep2line(sp.sp.steps(0))
      else "have(" + sequent2code(sp.bot) + ") subproof {\n" + scproof2code(sp.sp) + "\n}"
    case Sorry(bot) => "have(" + sequent2code(bot) + ") by Sorry"
  }
}

object MLExtract extends lisa.Main {

  /*
    You may use the following tactics:
        - Restate              | "Trivially" true Sequent. Deals with alpha equivalence and most propositional rules but not distributivity
        - Weakening            | "Trivially" weaker sequent (than the previous one).
        - Tautology.from       | Anything that can be solved by propositional reasoning alone

        - LeftForall           | To introduce a ∀ quantifier in an assumption
        - LeftExists           | To introduce a ∃ quantifier in an assumption (the variable must not be free somewhere else)
        - RightForall          | To introduce a ∀ quantifier in the conclusion (the variable must not be free somewhere else)
        - RightExists          | To introduce a ∃ quantifier in the conclusion
        - InstantiateForall    | To obtain a formula of the form P(t) from a quantified assumption ∀(x, P(x))



        thm1 and thm2 illustrate how those tactics can be used, as well as the usage of "assume", "have", "thenHave", "by", "thesis", "of" and "subproof".
   */

  val x = variable
  val y = variable
  val z = variable
  val f = function[1]
  val P = formulaVariable
  val Q = predicate[1]
  val R = predicate[1]
  val S = predicate[2]

  // A standard theorem about reordering quantifiers. Does the converse hold?
  val thm1 = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    have(S(x, y) |- S(x, y)) by Restate
    thenHave(∀(y, S(x, y)) |- S(x, y)) by LeftForall
    thenHave(∀(y, S(x, y)) |- ∃(x, S(x, y))) by RightExists
    thenHave(∃(x, ∀(y, S(x, y))) |- ∃(x, S(x, y))) by LeftExists
    thenHave(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) by RightForall
  }

  println(prettyProof(thm1.proof))
  println(prettySCProof(thm1.proof.toSCProof))
  println(scproof2code(thm1.proof.toSCProof))

  // // A standard theorem about reordering quantifiers. Does the converse hold?
  // val thm11 = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
  //   have(S(x, y) |- S(x, y)) by Restate
  //   have(∀(y, S(x, y)) |- S(x, y)) by LeftForall
  //   have(∀(y, S(x, y)) |- ∃(x, S(x, y))) by RightExists
  //   have(∃(x, ∀(y, S(x, y))) |- ∃(x, S(x, y))) by LeftExists
  //   have(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) by RightForall
  // }

  // A standard and important property of ∀: It distributes over conjunction. This is useful to justify prenex normal form.
  val thm2 = Theorem((∀(x, Q(x)) /\ ∀(x, R(x))) <=> ∀(x, Q(x) /\ R(x))) {

    // Here we prove the two directions of <=> separately and then combine them.
    val forward = have((∀(x, Q(x)), ∀(x, R(x))) |- ∀(x, Q(x) /\ R(x))) subproof {
      have((Q(x), R(x)) |- Q(x) /\ R(x)) by Restate
      thenHave((∀(x, Q(x)), R(x)) |- Q(x) /\ R(x)) by LeftForall
      thenHave((∀(x, Q(x)), ∀(x, R(x))) |- Q(x) /\ R(x)) by LeftForall
      thenHave(thesis) by RightForall
    }

    // The second direction
    val backward = have(∀(x, Q(x) /\ R(x)) |- ∀(x, Q(x)) /\ ∀(x, R(x))) subproof {
      assume(∀(x, Q(x) /\ R(x)))
      val assump = have(Q(x) /\ R(x)) by InstantiateForall
      have(Q(x)) by Weakening(assump)
      val conj1 = thenHave(∀(x, Q(x))) by RightForall
      have(R(x)) by Weakening(assump)
      val conj2 = thenHave(∀(x, R(x))) by RightForall
      have(thesis) by Tautology.from(conj1, conj2)
    }

    have(thesis) by Tautology.from(forward, backward)
  }

  // println(prettyProof(thm2.proof))
  // println(prettySCProof(thm2.proof.toSCProof))
  // println(scproof2code(thm2.proof.toSCProof))

  // This theorem requires instantiating the assumption twice, once with x and once with f(x), and then combine the two.
  // Since x is free is the sequent step1, then step 1 is true with anything substituted for x.
  // We can do such substitution with the "of" keyword.
  // Specifically, `step1 of (x := f(x))` proves the formula P(f(x)) ==> P(f(f(x)))
  val thm3 = Theorem(∀(x, Q(x) ==> Q(f(x))) |- Q(x) ==> Q(f(f(x)))) {
    assume(∀(x, Q(x) ==> Q(f(x))))
    val step1 = have(Q(x) ==> Q(f(x))) by InstantiateForall
    have(thesis) by Tautology.from(step1, step1 of (x := f(x)))
  }

  // println(prettyProof(thm3.proof))
  // println(prettySCProof(thm3.proof.toSCProof))
  // println(scproof2code(thm3.proof.toSCProof))

}
