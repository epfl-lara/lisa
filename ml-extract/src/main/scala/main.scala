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

// TODO: fix printing of ∧ and ∨ with > 2 arguments
// TODO: determine when calling withParameters is necessary instead of using it by default
// TODO: remove unnecessary variables "val s_..." in generated proofs
// TODO: generate better random variable names
// TODO: handle automatic variable declaration  before theorems/proofs

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
        val (bot_, step_ref_seq, tactic_name, opening, closing) = (ps match
          case Restate(bot, t1) => (bot, Seq(t1), "Restate", ".from(", ")")
          case RestateTrue(bot) => (bot, null, "Restate", null, null)
          case Hypothesis(bot, phi) => (bot, null, "Hypothesis", null, null)
          // case Cut(bot, t1, t2, phi) => (bot, Seq(t1, t2), "Cut", "(", ")")
          case Cut(bot, t1, t2, phi) => (bot, Seq(t1, t2), s"Cut.withParameters(${formula2code(phi)})", "(", ")")
          // case LeftAnd(bot, t1, phi, psi) => (bot, Seq(t1), "LeftAnd", "(", ")")
          case LeftAnd(bot, t1, phi, psi) => (bot, Seq(t1), s"LeftAnd.withParameters(${formula2code(phi)}, ${formula2code(psi)})", "(", ")")
          // case LeftOr(bot, t, disjuncts) => (bot, t, "LeftOr", "(", ")")
          case LeftOr(bot, t, disjuncts) => (bot, t, s"LeftOr.withParameters(${disjuncts.map(formula2code).mkString(", ")})", "(", ")")
          // case LeftImplies(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2), "LeftImplies", "(", ")")
          case LeftImplies(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2), s"LeftImplies.withParameters(${formula2code(phi)}, ${formula2code(psi)})", "(", ")")
          // case LeftIff(bot, t1, phi, psi) => (bot, Seq(t1), "LeftIff", "(", ")")
          case LeftIff(bot, t1, phi, psi) => (bot, Seq(t1), s"LeftIff.withParameters(${formula2code(phi)}, ${formula2code(psi)})", "(", ")")
          // case LeftNot(bot, t1, phi) => (bot, Seq(t1), "LeftNot", "(", ")")
          case LeftNot(bot, t1, phi) => (bot, Seq(t1), s"LeftNot.withParameters(${formula2code(phi)})", "(", ")")
          // case LeftForall(bot, t1, phi, x, t) => (bot, Seq(t1), "LeftForall", "(", ")")
          case LeftForall(bot, t1, phi, x, t) => (bot, Seq(t1), s"LeftForall.withParameters(${formula2code(phi)}, ${asFrontLabel(x)}, ${term2code(t)})", "(", ")")
          // case LeftExists(bot, t1, phi, x) => (bot, Seq(t1), "LeftExists", "(", ")")
          case LeftExists(bot, t1, phi, x) => (bot, Seq(t1), s"LeftExists.withParameters(${formula2code(phi)}, ${asFrontLabel(x)})", "(", ")")
          // case LeftExistsOne(bot, t1, phi, x) => (bot, Seq(t1), "LeftExistsOne", "(", ")")
          case LeftExistsOne(bot, t1, phi, x) => (bot, Seq(t1), s"LeftExistsOne.withParameters(${formula2code(phi)}, ${asFrontLabel(x)})", "(", ")")
          // case RightAnd(bot, t, conjuncts) => (bot, t, "RightAnd", "(", ")")
          case RightAnd(bot, t, conjuncts) => (bot, t, s"RightAnd.withParameters(${conjuncts.map(formula2code).mkString(", ")})", "(", ")")
          // case RightOr(bot, t1, phi, psi) => (bot, Seq(t1), "RightOr", "(", ")")
          case RightOr(bot, t1, phi, psi) => (bot, Seq(t1), s"RightOr.withParameters(${formula2code(phi)}, ${formula2code(psi)})", "(", ")")
          // case RightImplies(bot, t1, phi, psi) => (bot, Seq(t1), "RightImplies", "(", ")")
          case RightImplies(bot, t1, phi, psi) => (bot, Seq(t1), s"RightImplies.withParameters(${formula2code(phi)}, ${formula2code(psi)})", "(", ")")
          // case RightIff(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2), "RightIff", "(", ")")
          case RightIff(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2), s"RightIff.withParameters(${formula2code(phi)}, ${formula2code(psi)})", "(", ")")
          // case RightNot(bot, t1, phi) => (bot, Seq(t1), "RightNot", "(", ")")
          case RightNot(bot, t1, phi) => (bot, Seq(t1), s"RightNot.withParameters(${formula2code(phi)})", "(", ")")
          // case RightForall(bot, t1, phi, x) => (bot, Seq(t1), "RightForall", "(", ")")
          case RightForall(bot, t1, phi, x) => (bot, Seq(t1), s"RightForall.withParameters(${formula2code(phi)}, ${asFrontLabel(x)})", "(", ")")
          // case RightExists(bot, t1, phi, x, t) => (bot, Seq(t1), "RightExists", "(", ")")
          case RightExists(bot, t1, phi, x, t) => (bot, Seq(t1), s"RightExists.withParameters(${formula2code(phi)}, ${asFrontLabel(x)}, ${term2code(t)})", "(", ")")
          // case RightExistsOne(bot, t1, phi, x) => (bot, Seq(t1), "RightExistsOne", "(", ")")
          case RightExistsOne(bot, t1, phi, x) => (bot, Seq(t1), s"RightExistsOne.withParameters(${formula2code(phi)}, ${asFrontLabel(x)})", "(", ")")
          case Weakening(bot, t1) => (bot, Seq(t1), "Weakening", "(", ")")
          // case LeftRefl(bot, t1, phi) => (bot, Seq(t1), "LeftRefl", "(", ")")
          case LeftRefl(bot, t1, phi) => (bot, Seq(t1), s"LeftRefl.withParameters(${formula2code(phi)})", "(", ")")
          // case RightRefl(bot, phi) => (bot, null, "RightRefl", null, null)
          case RightRefl(bot, phi) => (bot, null, s"RightRefl.withParameters(${formula2code(phi)})", null, null)
          // case LeftSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), "LeftSubstEq", "(", ")")
          case LeftSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), s"LeftSubstEq.withParameters(List(${equals
                .map((a, b) => s"((${term2code(a)}), (${term2code(b)}))")
                .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))", "(", ")")
          // case RightSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), "RightSubstEq", "(", ")")
          case RightSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), s"RightSubstEq.withParameters(List(${equals
                .map((a, b) => s"((${term2code(a)}), (${term2code(b)}))")
                .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))", "(", ")")
          case LeftSubstIff(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), s"LeftSubstIff(List(${equals
                .map((a, b) => s"((${formula2code(a)}), (${formula2code(b)}))")
                .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))", "(", ")")
          case RightSubstIff(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), s"RightSubstIff(List(${equals
                .map((a, b) => s"((${formula2code(a)}), (${formula2code(b)}))")
                .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))", "(", ")")
          case InstSchema(bot, t1, mCon, mPred, mTerm) =>
            if mCon.isEmpty && mPred.isEmpty then
              (bot, Seq(t1), s"InstFunSchema(Map(${mTerm.toList
                  .map((k, v) => s"${asFrontLabel(k)} -> ${term2code(v.body)}")
                  .mkString(", ")}))", "(", ")")
            else if mCon.isEmpty && mTerm.isEmpty then
              (bot, Seq(t1), s"InstPredSchema(Map(${mPred.toList
                  .map((k, v) => s"${asFrontLabel(k)} -> ${formula2code(v.body)}")
                  .mkString(", ")}))", "(", ")")
            else throw new Exception("InstSchema not implemented")
          case _ => throw new Exception(s"tactic ${ps.getClass.getName} not implemented")
        )

        varDecl + (
          if (step_ref_seq != null && step_ref_seq.size == 1 && stepNum > 0 && step_ref_seq.head + 1 == stepNum)
            then s"thenHave(${sequent2code(bot_)}) by $tactic_name"
          else
            s"have(${sequent2code(bot_)}) by $tactic_name" + (
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

  // println(prettyProof(thm1.proof))
  // println(prettySCProof(thm1.proof.toSCProof))
  // println(scproof2code(thm1.proof.toSCProof))
  // println(scproof2code(optimizeProofIteratively(thm1.proof.toSCProof)))

  val thm1_raw = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have(S(x, y) ⊢ S(x, y)) subproof {
      val s_0_0 = have(S(x, y) ⊢ S(x, y)) by Restate
    }
    val s_1 = have(∀(y, S(x, y)) ⊢ S(x, y)) subproof {
      val s_1_0 = have(∀(y, S(x, y)) ⊢ S(x, y)) by LeftForall.withParameters(S(x, y), y, y)(s_0)
    }
    val s_2 = have(∀(y, S(x, y)) ⊢ ∃(x, S(x, y))) subproof {
      val s_2_0 = have(∀(y, S(x, y)) ⊢ ∃(x, S(x, y))) by RightExists.withParameters(S(x, y), x, x)(s_1)
    }
    val s_3 = have(∃(x, ∀(y, S(x, y))) ⊢ ∃(x, S(x, y))) subproof {
      val s_3_0 = have(∃(x, ∀(y, S(x, y))) ⊢ ∃(x, S(x, y))) by LeftExists.withParameters(∀(y, S(x, y)), x)(s_2)
    }
    val s_4 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) subproof {
      val s_4_0 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by RightForall.withParameters(∃(x, S(x, y)), y)(s_3)
    }
  }

  val thm1_optimized = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have(S(x, y) ⊢ S(x, y)) by Restate
    val s_1 = thenHave(∀(y, S(x, y)) ⊢ S(x, y)) by LeftForall.withParameters(S(x, y), y, y)
    val s_2 = thenHave(∀(y, S(x, y)) ⊢ ∃(x, S(x, y))) by RightExists.withParameters(S(x, y), x, x)
    val s_3 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∃(x, S(x, y))) by LeftExists.withParameters(∀(y, S(x, y)), x)
    val s_4 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by RightForall.withParameters(∃(x, S(x, y)), y)
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
  // println(scproof2code(optimizeProofIteratively(thm2.proof.toSCProof)))

  val thm2_raw = Theorem((∀(x, Q(x)) /\ ∀(x, R(x))) <=> ∀(x, Q(x) /\ R(x))) {
    val s_0 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
      val s_0_0 = have(( R(x), Q(x) ) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_0_0_0 = have(( R(x), Q(x) ) ⊢ (Q(x) ∧ R(x))) by Restate
      }
      val s_0_1 = have(( R(x), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_0_1_0 = have(( R(x), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall.withParameters(Q(x), x, x)(s_0_0)
      }
      val s_0_2 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_0_2_0 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall.withParameters(R(x), x, x)(s_0_1)
      }
      val s_0_3 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
        val s_0_3_0 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) by RightForall.withParameters((Q(x) ∧ R(x)), x)(s_0_2)
      }
      val s_0_4 = thenHave(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) by Restate
    }
    val s_1 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
      val s_1_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
        val s_1_0_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) by Hypothesis
      }
      val s_1_1 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) subproof {
        val s_1_1_0 = have(( ∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x)) ) ⊢ (Q(x) ∧ R(x))) subproof {
          val s_1_1_0_0 = have(( ∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x)) ) ⊢ (Q(x) ∧ R(x))) by Restate
        }
        val s_1_1_1 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) subproof {
          val s_1_1_1_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall.withParameters((Q(x) ∧ R(x)), x, x)(s_1_1_0)
        }
      }
      val s_1_2 = have(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) subproof {
        val s_1_2_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) by Weakening(s_1_1)
      }
      val s_1_3 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) subproof {
        val s_1_3_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) by RightForall.withParameters(Q(x), x)(s_1_2)
      }
      val s_1_4 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) subproof {
        val s_1_4_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) by Weakening(s_1_1)
      }
      val s_1_5 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) subproof {
        val s_1_5_0 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) by RightForall.withParameters(R(x), x)(s_1_4)
      }
      val s_1_6 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
        val s_1_6_0 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x)))) by Restate.from(s_1_3)
        val s_1_6_1 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) by Restate.from(s_1_5)
        val s_1_6_2 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
          val s_1_6_2_0 = have((  ) ⊢ ⊤) by Restate
          val s_1_6_2_1 = thenHave(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate
        }
        val s_1_6_3 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut.withParameters((∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))))(s_1_6_0, s_1_6_2)
        val s_1_6_4 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut.withParameters((∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))))(s_1_6_1, s_1_6_3)
      }
      val s_1_7 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate
    }
    val s_2 = have((  ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) subproof {
      val s_2_0 = have((  ) ⊢ ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s_0)
      val s_2_1 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) by Restate.from(s_1)
      val s_2_2 = have(( ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) subproof {
        val s_2_2_0 = have((  ) ⊢ ⊤) by Restate
        val s_2_2_1 = thenHave(( ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Restate
      }
      val s_2_3 = have((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut.withParameters(((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))))(s_2_0, s_2_2)
      val s_2_4 = have((  ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut.withParameters((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))))(s_2_1, s_2_3)
    }
  }

  val thm2_optimized = Theorem((∀(x, Q(x)) /\ ∀(x, R(x))) <=> ∀(x, Q(x) /\ R(x))) {
    val s_0 = have(( R(x), Q(x) ) ⊢ (Q(x) ∧ R(x))) by Restate
    val s_1 = thenHave(( R(x), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall.withParameters(Q(x), x, x)
    val s_2 = thenHave(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall.withParameters(R(x), x, x)
    val s_3 = thenHave(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) by RightForall.withParameters((Q(x) ∧ R(x)), x)
    val s_4 = have(( ∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x)) ) ⊢ (Q(x) ∧ R(x))) by Restate
    val s_5 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall.withParameters((Q(x) ∧ R(x)), x, x)
    val s_6 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) by Weakening
    val s_7 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) by RightForall.withParameters(Q(x), x)
    val s_8 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) by Weakening(s_5)
    val s_9 = thenHave(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) by RightForall.withParameters(R(x), x)
    val s_10 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x)))) by Restate.from(s_7)
    val s_11 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) by Restate.from(s_9)
    val s_12 = have((  ) ⊢ ⊤) by Restate
    val s_13 = thenHave(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate
    val s_14 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut.withParameters((∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))))(s_10, s_13)
    val s_15 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut.withParameters((∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))))(s_11, s_14)
    val s_16 = have((  ) ⊢ ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s_3)
    val s_17 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) by Restate.from(s_15)
    val s_18 = have(( ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s_12)
    val s_19 = have((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut.withParameters(((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))))(s_16, s_18)
    val s_20 = have((  ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut.withParameters((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))))(s_17, s_19)
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

  // println(prettyProof(thm3.proof))
  // println(prettySCProof(thm3.proof.toSCProof))
  // println(scproof2code(thm3.proof.toSCProof))
  // println(scproof2code(optimizeProofIteratively(thm3.proof.toSCProof)))

  val thm3_raw = Theorem(∀(x, Q(x) ==> Q(f(x))) |- (Q(x) ==> Q(f(f(x))))) {
    val s_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ ∀(x, (Q(x) ==> Q(f(x))))) subproof {
      val s_0_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ ∀(x, (Q(x) ==> Q(f(x))))) by Hypothesis
    }
    val s_1 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) subproof {
      val s_1_0 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x))) ) ⊢ (Q(x) ==> Q(f(x)))) subproof {
        val s_1_0_0 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x))) ) ⊢ (Q(x) ==> Q(f(x)))) by Restate
      }
      val s_1_1 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) subproof {
        val s_1_1_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by LeftForall.withParameters((Q(x) ==> Q(f(x))), x, x)(s_1_0)
      }
    }
    val s_2 = have(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) subproof {
      val s_2_0 = have(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) by InstFunSchema(Map(x -> f(x)))(s_1)
    }
    val s_3 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) subproof {
      val s_3_0 = have((  ) ⊢ (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x))))) by Restate.from(s_1)
      val s_3_1 = have((  ) ⊢ (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) by Restate.from(s_2)
      val s_3_2 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) subproof {
        val s_3_2_0 = have(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊤) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊤)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
        val s_3_2_1 = thenHave(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by RightSubstIff(List(((Q(f(x))), (⊤))), lambda(Seq(MaRvIn_1), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ MaRvIn_1) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(MaRvIn_1)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))))
        val s_3_2_2 = have(¬(Q(f(x))) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊥) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊥)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
        val s_3_2_3 = thenHave(¬(Q(f(x))) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by RightSubstIff(List(((Q(f(x))), (⊥))), lambda(Seq(MaRvIn_1), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ MaRvIn_1) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(MaRvIn_1)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))))
        val s_3_2_4 = thenHave((  ) ⊢ ( Q(f(x)), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))) )) by Restate
        val s_3_2_5 = have((  ) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Cut.withParameters(Q(f(x)))(s_3_2_4, s_3_2_1)
        val s_3_2_6 = thenHave((  ) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
        val s_3_2_7 = thenHave(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Restate
      }
      val s_3_3 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut.withParameters((∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))))(s_3_0, s_3_2)
      val s_3_4 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut.withParameters((∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))))(s_3_1, s_3_3)
    }
  }

  val thm3_optimized = Theorem(∀(x, Q(x) ==> Q(f(x))) |- (Q(x) ==> Q(f(f(x))))) {
    val s_0 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x))) ) ⊢ (Q(x) ==> Q(f(x)))) by Restate
    val s_1 = thenHave(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by LeftForall.withParameters((Q(x) ==> Q(f(x))), x, x)
    val s_2 = thenHave(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) by InstFunSchema(Map(x -> f(x)))
    val s_3 = have((  ) ⊢ (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x))))) by Restate.from(s_1)
    val s_4 = have((  ) ⊢ (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) by Restate.from(s_2)
    val s_5 = have(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊤) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊤)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
    val s_6 = thenHave(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
    val s_7 = have(¬(Q(f(x))) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊥) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊥)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
    val s_8 = thenHave((  ) ⊢ ( Q(f(x)), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))) )) by Restate
    val s_9 = have((  ) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Cut.withParameters(Q(f(x)))(s_8, s_6)
    val s_10 = thenHave(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Restate
    val s_11 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut.withParameters((∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))))(s_3, s_10)
    val s_12 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut.withParameters((∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))))(s_4, s_11)
  }


  val thm1bis = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    have(thesis) by Tableau
  }

  // println(prettyProof(thm1bis.proof))
  // println(prettySCProof(thm1bis.proof.toSCProof))
  // println(scproof2code(thm1bis.proof.toSCProof))
  // println(scproof2code(optimizeProofIteratively(thm1bis.proof.toSCProof)))

  val thm1bis_raw = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) subproof {
      val s_0_0 = have(( S(x, y_1), ¬(S(x, y_1)) ) ⊢ (  )) by Restate
      val s_0_1 = thenHave(( ¬(S(x, y_1)), ∀(y, S(x, y)) ) ⊢ (  )) by LeftForall.withParameters(S(x, y), y, y_1)
      val s_0_2 = thenHave(( ∀(y, S(x, y)), ∀(x_2, ¬(S(x_2, y_1))) ) ⊢ (  )) by LeftForall.withParameters(¬(S(x_2, y_1)), x_2, x)
      val s_0_3 = thenHave(( ∀(x_2, ¬(S(x_2, y_1))), ∃(x, ∀(y, S(x, y))) ) ⊢ (  )) by LeftExists.withParameters(∀(y, S(x, y)), x)
      val s_0_4 = thenHave(( ∃(x, ∀(y, S(x, y))), ∃(y_1, ∀(x_2, ¬(S(x_2, y_1)))) ) ⊢ (  )) by LeftExists.withParameters(∀(x_2, ¬(S(x_2, y_1))), y_1)
      val s_0_5 = thenHave((∃(x, ∀(y, S(x, y))) ∧ ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ (  )) by Weakening
      val s_0_6 = thenHave((∃(x, ∀(y, S(x, y))) ∧ ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ (  )) by Weakening
      val s_0_7 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by Restate
    }
  }

  val thm1bis_optimized = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s_0 = have(( S(x, y_1), ¬(S(x, y_1)) ) ⊢ (  )) by Restate
    val s_1 = thenHave(( ¬(S(x, y_1)), ∀(y, S(x, y)) ) ⊢ (  )) by LeftForall.withParameters(S(x, y), y, y_1)
    val s_2 = thenHave(( ∀(y, S(x, y)), ∀(x_2, ¬(S(x_2, y_1))) ) ⊢ (  )) by LeftForall.withParameters(¬(S(x_2, y_1)), x_2, x)
    val s_3 = thenHave(( ∀(x_2, ¬(S(x_2, y_1))), ∃(x, ∀(y, S(x, y))) ) ⊢ (  )) by LeftExists.withParameters(∀(y, S(x, y)), x)
    val s_4 = thenHave(( ∃(x, ∀(y, S(x, y))), ∃(y_1, ∀(x_2, ¬(S(x_2, y_1)))) ) ⊢ (  )) by LeftExists.withParameters(∀(x_2, ¬(S(x_2, y_1))), y_1)
    val s_5 = thenHave(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by Restate
  }

}
