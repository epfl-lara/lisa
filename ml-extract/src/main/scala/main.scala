import lisa.utils.parsing.ProofPrinter._
import lisa.utils.FOLPrinter.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.K
import lisa.prooflib.ProofTacticLib.*
import lisa.fol.FOLHelpers.*
import lisa.fol.FOL as F
import lisa.utils.KernelHelpers.lambda
import lisa.utils.ProofsShrink.*
import lisa.automation.Tableau

// TODO: fix printing of ∧ and ∨ with > 2 arguments, currently handled as recursive binary operators
// TODO: remove unnecessary variables "val s_..." in generated proofs
// TODO: generate more realistic variable names
// TODO: handle automatic global variable declaration before theorems/proofs

def scproof2code(p: K.SCProof, premises: Seq[String] = Seq.empty, indent: Int = 0, varPrefix: String = "s"): String = {
  def scproofstep2line(ps: SCProofStep, stepNum: Int, premises: Seq[String], indent: Int, varPrefix: String): String = {
    def sequent2code(sq: Sequent): String = asFront(sq).toString.replace("⇒", "==>").replace("⇔", "<=>")
    def formula2code(form: K.Formula): String = asFront(form).toString.replace("⇒", "==>").replace("⇔", "<=>")
    def term2code(term: K.Term): String = asFront(term).toString.replace("⇒", "==>").replace("⇔", "<=>")

    def index2stepvar(i: Int): String =
      if i < -premises.size then throw new Exception(s"step $i is not defined")
      else if i < 0 then premises(-i - 1)
      else s"${varPrefix}_$i"

    val varDecl = "  " * indent + s"val ${varPrefix}_$stepNum = "
    ps match
      case Sorry(_) => "sorry"
      case sp @ SCSubproof(_, _) =>
        varDecl + s"have(${sequent2code(sp.bot)}) subproof {\n" + scproof2code(sp.sp, sp.premises.map(index2stepvar), indent + 1, s"${varPrefix}_$stepNum") + "\n" + "  " * indent + "}"
      case _ =>
        var tacticName = ps.getClass.getSimpleName
        var opening = "("
        var closing = ")"
        val (bot_, step_ref_seq) = (ps match
          case Restate(bot, t1) =>
            opening = ".from("
            (bot, Seq(t1))
          case RestateTrue(bot) =>
            tacticName = "Restate"
            (bot, null)
          case Hypothesis(bot, phi) => (bot, null)
          case Cut(bot, t1, t2, phi) => (bot, Seq(t1, t2))
          case LeftAnd(bot, t1, phi, psi) => (bot, Seq(t1))
          case LeftOr(bot, t, disjuncts) => (bot, t)
          case LeftImplies(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2))
          case LeftIff(bot, t1, phi, psi) => (bot, Seq(t1))
          case LeftNot(bot, t1, phi) => (bot, Seq(t1))
          case LeftForall(bot, t1, phi, x, t) => (bot, Seq(t1))
          case LeftExists(bot, t1, phi, x) => (bot, Seq(t1))
          case LeftExistsOne(bot, t1, phi, x) => (bot, Seq(t1))
          case RightAnd(bot, t, conjuncts) => (bot, t)
          case RightOr(bot, t1, phi, psi) => (bot, Seq(t1))
          case RightImplies(bot, t1, phi, psi) => (bot, Seq(t1))
          case RightIff(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2))
          case RightNot(bot, t1, phi) => (bot, Seq(t1))
          case RightForall(bot, t1, phi, x) => (bot, Seq(t1))
          case RightExists(bot, t1, phi, x, t) => (bot, Seq(t1))
          case RightExistsOne(bot, t1, phi, x) => (bot, Seq(t1))
          case Weakening(bot, t1) => (bot, Seq(t1))
          case LeftRefl(bot, t1, phi) => (bot, Seq(t1))
          case RightRefl(bot, phi) => (bot, null)
          case LeftSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1))
          case RightSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1))
          case LeftSubstIff(bot, t1, equals, lambdaPhi) =>
            tacticName = s"LeftSubstIff(List(${equals
                .map((a, b) => s"((${formula2code(a)}), (${formula2code(b)}))")
                .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))"
            (bot, Seq(t1))
          case RightSubstIff(bot, t1, equals, lambdaPhi) =>
            tacticName = s"RightSubstIff(List(${equals
                .map((a, b) => s"((${formula2code(a)}), (${formula2code(b)}))")
                .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))"
            (bot, Seq(t1))
          case InstSchema(bot, t1, mCon, mPred, mTerm) =>
            if mCon.isEmpty && mPred.isEmpty then
              tacticName = s"InstFunSchema(Map(${mTerm.toList
                  .map((k, v) => s"${asFrontLabel(k)} -> ${term2code(v.body)}")
                  .mkString(", ")}))"
              (bot, Seq(t1))
            else if mCon.isEmpty && mTerm.isEmpty then
              tacticName = s"InstPredSchema(Map(${mPred.toList
                  .map((k, v) => s"${asFrontLabel(k)} -> ${formula2code(v.body)}")
                  .mkString(", ")}))"
              (bot, Seq(t1))
            else throw new Exception("InstSchema not implemented")
          case _ => throw new Exception(s"Tactic ${ps.getClass.getName} not implemented")
        )

        varDecl + (
          if (step_ref_seq != null && step_ref_seq.size == 1 && stepNum > 0 && step_ref_seq.head + 1 == stepNum)
          then s"thenHave(${sequent2code(bot_)}) by $tacticName"
          else
            s"have(${sequent2code(bot_)}) by $tacticName" + (
              if step_ref_seq == null then ""
              else s"$opening${step_ref_seq.map(index2stepvar).mkString(", ")}$closing"
            )
        )
  }

  p.steps.zipWithIndex.map((ps, i) => scproofstep2line(ps, i, premises, indent, varPrefix)).mkString("\n")
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

  val x_1 = variable
  val x_2 = variable
  val y_1 = variable
  val MaRvIn_1 = formulaVariable

  // A standard theorem about reordering quantifiers. Does the converse hold?
  val thm1 = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    have(S(x, y) |- S(x, y)) by Restate
    thenHave(∀(y, S(x, y)) |- S(x, y)) by LeftForall
    thenHave(∀(y, S(x, y)) |- ∃(x, S(x, y))) by RightExists
    thenHave(∃(x, ∀(y, S(x, y))) |- ∃(x, S(x, y))) by LeftExists
    thenHave(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) by RightForall
  }

  // println(prettyProof(thm1.highProof.get))
  // println(prettySCProof(thm1.kernelProof.get))
  // println(scproof2code(thm1.kernelProof.get))
  // println(scproof2code(optimizeProofIteratively(thm1.kernelProof.get)))

  val thm1_raw = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have(S(x, y) ⊢ S(x, y)) subproof {
      val s_0_0 = have(S(x, y) ⊢ S(x, y)) by Restate
    }
    val s_1 = have(∀(y, S(x, y)) ⊢ S(x, y)) subproof {
      val s_1_0 = have(∀(y, S(x, y)) ⊢ S(x, y)) by LeftForall(s_0)
    }
    val s_2 = have(∀(y, S(x, y)) ⊢ ∃(x, S(x, y))) subproof {
      val s_2_0 = have(∀(y, S(x, y)) ⊢ ∃(x, S(x, y))) by RightExists(s_1)
    }
    val s_3 = have(∃(x, ∀(y, S(x, y))) ⊢ ∃(x, S(x, y))) subproof {
      val s_3_0 = have(∃(x, ∀(y, S(x, y))) ⊢ ∃(x, S(x, y))) by LeftExists(s_2)
    }
    val s_4 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) subproof {
      val s_4_0 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by RightForall(s_3)
    }
  }

  val thm1_optimized = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have(S(x, y) ⊢ S(x, y)) by Restate
    val s_1 = thenHave(∀(y, S(x, y)) ⊢ S(x, y)) by LeftForall
    val s_2 = thenHave(∀(y, S(x, y)) ⊢ ∃(x, S(x, y))) by RightExists
    val s_3 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∃(x, S(x, y))) by LeftExists
    val s_4 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by RightForall
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

  // println(prettyProof(thm2.highProof.get))
  // println(prettySCProof(thm2.kernelProof.get))
  // println(scproof2code(thm2.kernelProof.get))
  // println(scproof2code(optimizeProofIteratively(thm2.kernelProof.get)))

  val thm2_raw = Theorem((∀(x, Q(x)) /\ ∀(x, R(x))) <=> ∀(x, Q(x) /\ R(x))) {
    val s_0 = have((∀(x, R(x)), ∀(x, Q(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
      val s_0_0 = have((R(x), Q(x)) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_0_0_0 = have((R(x), Q(x)) ⊢ (Q(x) ∧ R(x))) by Restate
      }
      val s_0_1 = have((R(x), ∀(x, Q(x))) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_0_1_0 = have((R(x), ∀(x, Q(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall(s_0_0)
      }
      val s_0_2 = have((∀(x, R(x)), ∀(x, Q(x))) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_0_2_0 = have((∀(x, R(x)), ∀(x, Q(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall(s_0_1)
      }
      val s_0_3 = have((∀(x, R(x)), ∀(x, Q(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
        val s_0_3_0 = have((∀(x, R(x)), ∀(x, Q(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) by RightForall(s_0_2)
      }
      val s_0_4 = thenHave((∀(x, R(x)), ∀(x, Q(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) by Restate
    }
    val s_1 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
      val s_1_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
        val s_1_0_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) by Hypothesis
      }
      val s_1_1 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_1_1_0 = have((∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) subproof {
          val s_1_1_0_0 = have((∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by Restate
        }
        val s_1_1_1 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) subproof {
          val s_1_1_1_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall(s_1_1_0)
        }
      }
      val s_1_2 = have(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) subproof {
        val s_1_2_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) by Weakening(s_1_1)
      }
      val s_1_3 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) subproof {
        val s_1_3_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) by RightForall(s_1_2)
      }
      val s_1_4 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) subproof {
        val s_1_4_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) by Weakening(s_1_1)
      }
      val s_1_5 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) subproof {
        val s_1_5_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) by RightForall(s_1_4)
      }
      val s_1_6 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
        val s_1_6_0 = have(() ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x)))) by Restate.from(s_1_3)
        val s_1_6_1 = have(() ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) by Restate.from(s_1_5)
        val s_1_6_2 = have((∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
          val s_1_6_2_0 = have(() ⊢ ⊤) by Restate
          val s_1_6_2_1 = thenHave((∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate
        }
        val s_1_6_3 = have((∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s_1_6_0, s_1_6_2)
        val s_1_6_4 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s_1_6_1, s_1_6_3)
      }
      val s_1_7 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate
    }
    val s_2 = have(() ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) subproof {
      val s_2_0 = have(() ⊢ ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s_0)
      val s_2_1 = have(() ⊢ (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) by Restate.from(s_1)
      val s_2_2 = have((((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) subproof {
        val s_2_2_0 = have(() ⊢ ⊤) by Restate
        val s_2_2_1 =
          thenHave((((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Restate
      }
      val s_2_3 = have((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s_2_0, s_2_2)
      val s_2_4 = have(() ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s_2_1, s_2_3)
    }
  }

  val thm2_optimized = Theorem((∀(x, Q(x)) /\ ∀(x, R(x))) <=> ∀(x, Q(x) /\ R(x))) {
    val s_0 = have((R(x), Q(x)) ⊢ (Q(x) ∧ R(x))) by Restate
    val s_1 = thenHave((R(x), ∀(x, Q(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall
    val s_2 = thenHave((∀(x, R(x)), ∀(x, Q(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall
    val s_3 = thenHave((∀(x, R(x)), ∀(x, Q(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) by RightForall
    val s_4 = have((∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by Restate
    val s_5 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall
    val s_6 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) by Weakening
    val s_7 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) by RightForall
    val s_8 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) by Weakening(s_5)
    val s_9 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) by RightForall
    val s_10 = have(() ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x)))) by Restate.from(s_7)
    val s_11 = have(() ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) by Restate.from(s_9)
    val s_12 = have(() ⊢ ⊤) by Restate
    val s_13 = thenHave((∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate
    val s_14 = have((∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s_10, s_13)
    val s_15 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s_11, s_14)
    val s_16 = have(() ⊢ ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s_3)
    val s_17 = have(() ⊢ (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) by Restate.from(s_15)
    val s_18 =
      have((((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s_12)
    val s_19 = have((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s_16, s_18)
    val s_20 = have(() ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s_17, s_19)
  }

  // This theorem requires instantiating the assumption twice, once with x and once with f(x), and then combine the two.
  // Since x is free is the sequent step1, then step 1 is true with anything substituted for x.
  // We can do such substitution with the "of" keyword.
  // Specifically, `step1 of (x := f(x))` proves the formula P(f(x)) ==> P(f(f(x)))
  val thm3 = Theorem(∀(x, Q(x) ==> Q(f(x))) |- Q(x) ==> Q(f(f(x)))) {
    assume(∀(x, Q(x) ==> Q(f(x))))
    val step1 = have(Q(x) ==> Q(f(x))) by InstantiateForall
    have(thesis) by Tautology.from(step1, step1 of (x := f(x)))
  }

  // println(prettyProof(thm3.highProof.get))
  // println(prettySCProof(thm3.kernelProof.get))
  // println(scproof2code(thm3.kernelProof.get))
  // println(scproof2code(optimizeProofIteratively(thm3.kernelProof.get)))

  val thm3_raw = Theorem(∀(x, Q(x) ==> Q(f(x))) |- (Q(x) ==> Q(f(f(x))))) {
    val s_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ ∀(x, (Q(x) ==> Q(f(x))))) subproof {
      val s_0_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ ∀(x, (Q(x) ==> Q(f(x))))) by Hypothesis
    }
    val s_1 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) subproof {
      val s_1_0 = have((∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) subproof {
        val s_1_0_0 = have((∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by Restate
      }
      val s_1_1 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) subproof {
        val s_1_1_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by LeftForall(s_1_0)
      }
    }
    val s_2 = have(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) subproof {
      val s_2_0 = have(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) by InstFunSchema(Map(x -> f(x)))(s_1)
    }
    val s_3 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) subproof {
      val s_3_0 = have(() ⊢ (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x))))) by Restate.from(s_1)
      val s_3_1 = have(() ⊢ (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) by Restate.from(s_2)
      val s_3_2 = have((∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) ⊢ (Q(x) ==> Q(f(f(x))))) subproof {
        val s_3_2_0 = have(
          Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊤) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊤)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))
        ) by Restate
        val s_3_2_1 = thenHave(
          Q(f(x)) ⊢ ¬(
            ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
          )
        ) by RightSubstIff(
          List(((Q(f(x))), (⊤))),
          lambda(
            Seq(MaRvIn_1),
            ¬(
              ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ MaRvIn_1) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(MaRvIn_1)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(
                Q(f(f(x)))
              ))
            )
          )
        )
        val s_3_2_2 = have(
          ¬(Q(f(x))) ⊢ ¬(
            ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊥) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊥)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
          )
        ) by Restate
        val s_3_2_3 = thenHave(
          ¬(Q(f(x))) ⊢ ¬(
            ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
          )
        ) by RightSubstIff(
          List(((Q(f(x))), (⊥))),
          lambda(
            Seq(MaRvIn_1),
            ¬(
              ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ MaRvIn_1) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(MaRvIn_1)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(
                Q(f(f(x)))
              ))
            )
          )
        )
        val s_3_2_4 = thenHave(
          () ⊢ (Q(f(x)), ¬(
            ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
          ))
        ) by Restate
        val s_3_2_5 = have(
          () ⊢ ¬(
            ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
          )
        ) by Cut(s_3_2_4, s_3_2_1)
        val s_3_2_6 = thenHave(
          () ⊢ ¬(
            ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
          )
        ) by Restate
        val s_3_2_7 =
          thenHave((∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) ⊢ (Q(x) ==> Q(f(f(x))))) by Restate
      }
      val s_3_3 = have((∀(x, (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s_3_0, s_3_2)
      val s_3_4 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s_3_1, s_3_3)
    }
  }

  val thm3_optimized = Theorem(∀(x, Q(x) ==> Q(f(x))) |- (Q(x) ==> Q(f(f(x))))) {
    val s_0 = have((∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by Restate
    val s_1 = thenHave(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by LeftForall
    val s_2 = thenHave(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) by InstFunSchema(Map(x -> f(x)))
    val s_3 = have(() ⊢ (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x))))) by Restate.from(s_1)
    val s_4 = have(() ⊢ (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) by Restate.from(s_2)
    val s_5 = have(
      Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊤) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊤)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))
    ) by Restate
    val s_6 = thenHave(
      Q(f(x)) ⊢ ¬(
        ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
      )
    ) by Restate
    val s_7 = have(
      ¬(Q(f(x))) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊥) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊥)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))
    ) by Restate
    val s_8 = thenHave(
      () ⊢ (Q(f(x)), ¬(
        ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
      ))
    ) by Restate
    val s_9 = have(
      () ⊢ ¬(
        ((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))
      )
    ) by Cut(s_8, s_6)
    val s_10 = thenHave((∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) ⊢ (Q(x) ==> Q(f(f(x))))) by Restate
    val s_11 = have((∀(x, (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s_3, s_10)
    val s_12 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s_4, s_11)
  }

  val thm1bis = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    have(thesis) by Tableau
  }

  // println(prettyProof(thm1bis.highProof.get))
  // println(prettySCProof(thm1bis.kernelProof.get))
  // println(scproof2code(thm1bis.kernelProof.get))
  // println(scproof2code(optimizeProofIteratively(thm1bis.kernelProof.get)))

  val thm1bis_raw = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) subproof {
      val s_0_0 = have((S(x, y_1), ¬(S(x, y_1))) ⊢ ()) by Restate
      val s_0_1 = thenHave((S(x, y_1), ∀(x_2, ¬(S(x_2, y_1)))) ⊢ ()) by LeftForall
      val s_0_2 = thenHave((∀(x_2, ¬(S(x_2, y_1))), ∀(y, S(x, y))) ⊢ ()) by LeftForall
      val s_0_3 = thenHave((∀(x_2, ¬(S(x_2, y_1))), ∃(x, ∀(y, S(x, y)))) ⊢ ()) by LeftExists
      val s_0_4 = thenHave((∃(x, ∀(y, S(x, y))), ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ ()) by LeftExists
      val s_0_5 = thenHave((∃(x, ∀(y, S(x, y))) ∧ ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ ()) by Weakening
      val s_0_6 = thenHave((∃(x, ∀(y, S(x, y))) ∧ ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ ()) by Weakening
      val s_0_7 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by Restate
    }
  }

  val thm1bis_optimized = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have((S(x, y_1), ¬(S(x, y_1))) ⊢ ()) by Restate
    val s_1 = thenHave((S(x, y_1), ∀(x_2, ¬(S(x_2, y_1)))) ⊢ ()) by LeftForall
    val s_2 = thenHave((∀(x_2, ¬(S(x_2, y_1))), ∀(y, S(x, y))) ⊢ ()) by LeftForall
    val s_3 = thenHave((∀(x_2, ¬(S(x_2, y_1))), ∃(x, ∀(y, S(x, y)))) ⊢ ()) by LeftExists
    val s_4 = thenHave((∃(x, ∀(y, S(x, y))), ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ ()) by LeftExists
    val s_5 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by Restate
  }

}
