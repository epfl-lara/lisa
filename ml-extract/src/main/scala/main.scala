import lisa.utils.parsing.ProofPrinter._
import lisa.utils.FOLPrinter.*

import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.K
import lisa.prooflib.ProofTacticLib.*
import lisa.fol.FOLHelpers.*

def sequent2code(sq: Sequent): String = prettySequent(sq).replace("⊢", "|-").replace("'", "")
// def sequent2code(sq: Sequent): String = asFront(sq).toString

def scproof2code(p: K.SCProof): String = {
  p.steps.zipWithIndex.map((ps, i) => scproofstep2line(ps, i)).mkString("\n")
}

def scproofstep2line(ps: SCProofStep, stepNum: Int): String = {
  def index2stepvar(i: Int): String =
    if i < 0 then s"s${stepNum + i}"
    else s"s$i"

  ps match
    case Restate(bot, t1) => s"val s$stepNum = have(${sequent2code(bot)}) by Restate(${index2stepvar(t1)})"
    case RestateTrue(bot) => s"val s$stepNum = have(${sequent2code(bot)}) by Restate"
    case Hypothesis(bot, phi) => s"val s$stepNum = assume(${sequent2code(bot)}) by Hypothesis"
    case Cut(bot, t1, t2, phi) => s"val s$stepNum = have(${sequent2code(bot)}) by Cut(${index2stepvar(t1)}, ${index2stepvar(t2)})"
    case LeftAnd(bot, t1, phi, psi) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftAnd(${index2stepvar(t1)})"
    case LeftOr(bot, t, disjuncts) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftOr(${t.map(index2stepvar).mkString(", ")})"
    case LeftImplies(bot, t1, t2, phi, psi) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftImplies(${index2stepvar(t1)}, ${index2stepvar(t2)})"
    case LeftIff(bot, t1, phi, psi) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftIff(${index2stepvar(t1)})"
    case LeftNot(bot, t1, phi) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftNot(${index2stepvar(t1)})"
    case LeftForall(bot, t1, phi, x, t) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftForall(${index2stepvar(t1)})"
    case LeftExists(bot, t1, phi, x) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftExists(${index2stepvar(t1)})"
    case LeftExistsOne(bot, t1, phi, x) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftExistsOne(${index2stepvar(t1)})"
    case RightAnd(bot, t, conjuncts) => s"val s$stepNum = have(${sequent2code(bot)}) by RightAnd(${t.mkString(", ")})"
    case RightOr(bot, t1, phi, psi) => s"val s$stepNum = have(${sequent2code(bot)}) by RightOr(${index2stepvar(t1)})"
    case RightImplies(bot, t1, phi, psi) => s"val s$stepNum = have(${sequent2code(bot)}) by RightImplies(${index2stepvar(t1)})"
    case RightIff(bot, t1, t2, phi, psi) => s"val s$stepNum = have(${sequent2code(bot)}) by RightIff(${index2stepvar(t1)}, ${index2stepvar(t2)})"
    case RightNot(bot, t1, phi) => s"val s$stepNum = have(${sequent2code(bot)}) by RightNot(${index2stepvar(t1)})"
    case RightForall(bot, t1, phi, x) => s"val s$stepNum = have(${sequent2code(bot)}) by RightForall(${index2stepvar(t1)})"
    case RightExists(bot, t1, phi, x, t) => s"val s$stepNum = have(${sequent2code(bot)}) by RightExists(${index2stepvar(t1)})"
    case RightExistsOne(bot, t1, phi, x) => s"val s$stepNum = have(${sequent2code(bot)}) by RightExistsOne(${index2stepvar(t1)})"
    case Weakening(bot, t1) => s"val s$stepNum = have(${sequent2code(bot)}) by Weakening(${index2stepvar(t1)})"
    case LeftRefl(bot, t1, phi) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftRefl(${index2stepvar(t1)})"
    case RightRefl(bot, phi) => s"val s$stepNum = have(${sequent2code(bot)}) by RightRefl"
    case LeftSubstEq(bot, t1, equals, lambdaPhi) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftSubstEq(${index2stepvar(t1)})"
    case RightSubstEq(bot, t1, equals, lambdaPhi) => s"val s$stepNum = have(${sequent2code(bot)}) by RightSubstEq(${index2stepvar(t1)})"
    case LeftSubstIff(bot, t1, equals, lambdaPhi) => s"val s$stepNum = have(${sequent2code(bot)}) by LeftSubstIff(${index2stepvar(t1)})"
    case RightSubstIff(bot, t1, equals, lambdaPhi) => s"val s$stepNum = have(${sequent2code(bot)}) by RightSubstIff(${index2stepvar(t1)})"
    case InstSchema(bot, t1, mCon, mPred, mTerm) => s"val s$stepNum = have(${sequent2code(bot)}) by InstSchema(${index2stepvar(t1)})"
    case sp @ SCSubproof(_, _) =>
      if sp.sp.length == 1 then scproofstep2line(sp.sp.steps(0), stepNum)
      else s"have(${sequent2code(sp.bot)}) subproof {\n" + scproof2code(sp.sp) + "\n}"
    case Sorry(bot) => s"val s$stepNum = have(${sequent2code(bot)}) by Sorry"
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

  val thm11 = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s0 = have(S(x, y) |- S(x, y)) by Restate
    val s1 = thenHave(∀(y, S(x, y)) |- S(x, y)) by LeftForall
    val s2 = have(∀(y, S(x, y)) |- ∃(x, S(x, y))) by RightExists(s1)
    val s3 = have(∃(x, ∀(y, S(x, y))) |- ∃(x, S(x, y))) by LeftExists(s2)
    val s4 = have(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) by RightForall(s3)
  }

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
