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

// TODO: fix printing of ∧ and ∨ with several arguments
// TODO: make sure that all proofsteps arguments are used when needed

def scproof2code(p: K.SCProof, premises: Seq[String] = Seq.empty, indent: Int = 0, varPrefix: String = "s"): String = {
  p.steps.zipWithIndex.map((ps, i) => scproofstep2line(ps, i, premises, indent, varPrefix)).mkString("\n")
}

def scproofstep2line(ps: SCProofStep, stepNum: Int, premises: Seq[String], indent: Int, varPrefix: String): String = {
  def sequent2code(sq: Sequent): String = asFront(sq).toString.replace("⇒", "==>").replace("⇔", "<=>")
  def formula2code(sq: K.Formula): String = asFront(sq).toString.replace("⇒", "==>").replace("⇔", "<=>")

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
        case Cut(bot, t1, t2, phi) => (bot, Seq(t1, t2), "Cut", "(", ")")
        case LeftAnd(bot, t1, phi, psi) => (bot, Seq(t1), "LeftAnd", "(", ")")
        case LeftOr(bot, t, disjuncts) => (bot, t, "LeftOr", "(", ")")
        case LeftImplies(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2), "LeftImplies", "(", ")")
        case LeftIff(bot, t1, phi, psi) => (bot, Seq(t1), "LeftIff", "(", ")")
        case LeftNot(bot, t1, phi) => (bot, Seq(t1), "LeftNot", "(", ")")
        case LeftForall(bot, t1, phi, x, t) => (bot, Seq(t1), "LeftForall", "(", ")")
        case LeftExists(bot, t1, phi, x) => (bot, Seq(t1), "LeftExists", "(", ")")
        case LeftExistsOne(bot, t1, phi, x) => (bot, Seq(t1), "LeftExistsOne", "(", ")")
        case RightAnd(bot, t, conjuncts) => (bot, t, "RightAnd", "(", ")")
        case RightOr(bot, t1, phi, psi) => (bot, Seq(t1), "RightOr", "(", ")")
        case RightImplies(bot, t1, phi, psi) => (bot, Seq(t1), "RightImplies", "(", ")")
        case RightIff(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2), "RightIff", "(", ")")
        case RightNot(bot, t1, phi) => (bot, Seq(t1), "RightNot", "(", ")")
        case RightForall(bot, t1, phi, x) => (bot, Seq(t1), "RightForall", "(", ")")
        case RightExists(bot, t1, phi, x, t) => (bot, Seq(t1), "RightExists", "(", ")")
        case RightExistsOne(bot, t1, phi, x) => (bot, Seq(t1), "RightExistsOne", "(", ")")
        case Weakening(bot, t1) => (bot, Seq(t1), "Weakening", "(", ")")
        case LeftRefl(bot, t1, phi) => (bot, Seq(t1), "LeftRefl", "(", ")")
        case RightRefl(bot, phi) => (bot, null, "RightRefl", null, null)
        case LeftSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), "LeftSubstEq", "(", ")")
        case RightSubstEq(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), "RightSubstEq", "(", ")")
        case LeftSubstIff(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), s"LeftSubstIff(List(${equals
              .map((a, b) => s"((${formula2code(a)}), (${formula2code(b)}))")
              .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))", "(", ")")
        case RightSubstIff(bot, t1, equals, lambdaPhi) => (bot, Seq(t1), s"RightSubstIff(List(${equals
              .map((a, b) => s"((${formula2code(a)}), (${formula2code(b)}))")
              .mkString(", ")}), lambda(Seq(${lambdaPhi.vars.map(asFrontLabel).mkString(", ")}), ${formula2code(lambdaPhi.body)}))", "(", ")")
        case InstSchema(bot, t1, mCon, mPred, mTerm) =>
          if mCon.isEmpty && mPred.isEmpty then
            (bot, Seq(t1), s"InstFunSchema(Map(${mTerm.toList
                .map((k, v) => s"${asFrontLabel(k)} -> ${asFront(v.body)}")
                .mkString(", ")}))", "(", ")")
          else if mCon.isEmpty && mTerm.isEmpty then
            (bot, Seq(t1), s"InstPredSchema(Map(${mPred.toList
                .map((k, v) => s"${asFrontLabel(k)} -> ${asFront(v.body)}")
                .mkString(", ")}))", "(", ")")
          else throw new Exception("InstSchema not implemented")
        case _ => throw new Exception(s"tactic ${ps.getClass.getName} not implemented")
      )

      var res = varDecl
      if (step_ref_seq != null && step_ref_seq.size == 1 && stepNum > 0 && step_ref_seq.head + 1 == stepNum) then res + s"thenHave(${sequent2code(bot_)}) by $tactic_name"
      else
        res += s"have(${sequent2code(bot_)}) by $tactic_name"
        if step_ref_seq == null then res
        else res + s"$opening${step_ref_seq.map(index2stepvar).mkString(", ")}$closing"
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

  // println(prettyProof(thm2.proof))
  // println(prettySCProof(thm2.proof.toSCProof))
  // println(scproof2code(thm2.proof.toSCProof))
  // println(scproof2code(optimizeProofIteratively(thm2.proof.toSCProof)))

  val thm2_raw = Theorem((∀(x, Q(x)) /\ ∀(x, R(x))) <=> ∀(x, Q(x) /\ R(x))) {
    val s0 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
      val s00 = have(( R(x), Q(x) ) ⊢ (Q(x) ∧ R(x))) subproof {
        val s000 = have(( R(x), Q(x) ) ⊢ (Q(x) ∧ R(x))) by Restate
      }
      val s01 = have(( R(x), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) subproof {
        val s010 = have(( R(x), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall(s00)
      }
      val s02 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) subproof {
        val s020 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall(s01)
      }
      val s03 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
        val s030 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) by RightForall(s02)
      }
      val s04 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) by Restate.from(s03)
    }
    val s1 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
      val s10 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) subproof {
        val s100 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, (Q(x) ∧ R(x)))) by Hypothesis
      }
      val s11 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) subproof {
        val s110 = have(( ∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x)) ) ⊢ (Q(x) ∧ R(x))) subproof {
          val s1100 = have(( ∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x)) ) ⊢ (Q(x) ∧ R(x))) by Restate
        }
        val s111 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) subproof {
          val s1110 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall(s110)
        }
      }
      val s12 = have(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) subproof {
        val s120 = have(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) by Weakening(s11)
      }
      val s13 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) subproof {
        val s130 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) by RightForall(s12)
      }
      val s14 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) subproof {
        val s140 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) by Weakening(s11)
      }
      val s15 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) subproof {
        val s150 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) by RightForall(s14)
      }
      val s16 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
        val s160 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x)))) by Restate.from(s13)
        val s161 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) by Restate.from(s15)
        val s162 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) subproof {
          val s1620 = have((  ) ⊢ ⊤) by Restate
          val s1621 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate.from(s1620)
        }
        val s163 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s160, s162)
        val s164 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s161, s163)
      }
      val s17 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate.from(s16)
    }
    val s2 = have((  ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) subproof {
      val s20 = have((  ) ⊢ ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s0)
      val s21 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) by Restate.from(s1)
      val s22 = have(( ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) subproof {
        val s220 = have((  ) ⊢ ⊤) by Restate
        val s221 = have(( ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s220)
      }
      val s23 = have((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s20, s22)
      val s24 = have((  ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s21, s23)
    }
  }

  val thm2_optimized = Theorem((∀(x, Q(x)) /\ ∀(x, R(x))) <=> ∀(x, Q(x) /\ R(x))) {
    val s0 = have(( R(x), Q(x) ) ⊢ (Q(x) ∧ R(x))) by Restate
    val s1 = have(( R(x), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall(s0)
    val s2 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ (Q(x) ∧ R(x))) by LeftForall(s1)
    val s3 = have(( ∀(x, R(x)), ∀(x, Q(x)) ) ⊢ ∀(x, (Q(x) ∧ R(x)))) by RightForall(s2)
    val s4 = have(( ∀(x, (Q(x) ∧ R(x))), (Q(x) ∧ R(x)) ) ⊢ (Q(x) ∧ R(x))) by Restate
    val s5 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (Q(x) ∧ R(x))) by LeftForall(s4)
    val s6 = have(∀(x, (Q(x) ∧ R(x))) ⊢ Q(x)) by Weakening(s5)
    val s7 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, Q(x))) by RightForall(s6)
    val s8 = have(∀(x, (Q(x) ∧ R(x))) ⊢ R(x)) by Weakening(s5)
    val s9 = have(∀(x, (Q(x) ∧ R(x))) ⊢ ∀(x, R(x))) by RightForall(s8)
    val s10 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x)))) by Restate.from(s7)
    val s11 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x)))) by Restate.from(s9)
    val s12 = have((  ) ⊢ ⊤) by Restate
    val s13 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, Q(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Restate.from(s12)
    val s14 = have(( ∀(x, (Q(x) ∧ R(x))), (∀(x, (Q(x) ∧ R(x))) ==> ∀(x, R(x))) ) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s10, s13)
    val s15 = have(∀(x, (Q(x) ∧ R(x))) ⊢ (∀(x, Q(x)) ∧ ∀(x, R(x)))) by Cut(s11, s14)
    val s16 = have((  ) ⊢ ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s3)
    val s17 = have((  ) ⊢ (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x))))) by Restate.from(s15)
    val s18 = have(( ((∀(x, R(x)) ∧ ∀(x, Q(x))) ==> ∀(x, (Q(x) ∧ R(x)))), (∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Restate.from(s12)
    val s19 = have((∀(x, (Q(x) ∧ R(x))) ==> (∀(x, Q(x)) ∧ ∀(x, R(x)))) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s16, s18)
    val s20 = have((  ) ⊢ ((∀(x, Q(x)) ∧ ∀(x, R(x))) <=> ∀(x, (Q(x) ∧ R(x))))) by Cut(s17, s19)
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
      val s0_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ ∀(x, (Q(x) ==> Q(f(x))))) by Hypothesis
    }
    val s_1 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) subproof {
      val s1_0 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x))) ) ⊢ (Q(x) ==> Q(f(x)))) subproof {
        val s10_0 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x))) ) ⊢ (Q(x) ==> Q(f(x)))) by Restate
      }
      val s1_1 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) subproof {
        val s11_0 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by LeftForall(s1_0)
      }
    }
    val s_2 = have(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) subproof {
      val s2_0 = have(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) by InstFunSchema(Map(x -> f(x)))(s_1)
    }
    val s_3 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) subproof {
      val s3_0 = have((  ) ⊢ (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x))))) by Restate.from(s_1)
      val s3_1 = have((  ) ⊢ (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) by Restate.from(s_2)
      val s3_2 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) subproof {
        val s32_0 = have(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊤) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊤)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
        val s32_1 = have(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by RightSubstIff(List(((Q(f(x))), (⊤))), lambda(Seq(MaRvIn_1), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ MaRvIn_1) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(MaRvIn_1)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))))(s32_0)
        val s32_2 = have(¬(Q(f(x))) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊥) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊥)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
        val s32_3 = have(¬(Q(f(x))) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by RightSubstIff(List(((Q(f(x))), (⊥))), lambda(Seq(MaRvIn_1), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ MaRvIn_1) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(MaRvIn_1)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))))(s32_2)
        val s32_4 = have((  ) ⊢ ( Q(f(x)), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))) )) by Restate.from(s32_3)
        val s32_5 = have((  ) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Cut(s32_4, s32_1)
        val s32_6 = have((  ) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate.from(s32_5)
        val s32_7 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Restate.from(s32_6)
      }
      val s3_3 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s3_0, s3_2)
      val s3_4 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s3_1, s3_3)
    }
  }

  val thm3_optimized = Theorem(∀(x, Q(x) ==> Q(f(x))) |- (Q(x) ==> Q(f(f(x))))) {
    val s_0 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (Q(x) ==> Q(f(x))) ) ⊢ (Q(x) ==> Q(f(x)))) by Restate
    val s_1 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(x)))) by LeftForall(s_0)
    val s_2 = have(∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ⊢ (Q(f(x)) ==> Q(f(f(x))))) by InstFunSchema(Map(x -> f(x)))(s_1)
    val s_3 = have((  ) ⊢ (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x))))) by Restate.from(s_1)
    val s_4 = have((  ) ⊢ (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x)))))) by Restate.from(s_2)
    val s_5 = have(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊤) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊤)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
    val s_6 = have(Q(f(x)) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate.from(s_5)
    val s_7 = have(¬(Q(f(x))) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ ⊥) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(⊥)))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Restate
    val s_8 = have((  ) ⊢ ( Q(f(x)), ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x)))))) )) by Restate.from(s_7)
    val s_9 = have((  ) ⊢ ¬(((((¬(((∀(x_1, ¬((Q(x_1) ∧ ¬(Q(f(x_1)))))) ∧ Q(f(x))) ∧ ¬(Q(f(f(x)))))) ∧ ¬(((∀(x, ¬((Q(x) ∧ ¬(Q(f(x)))))) ∧ Q(x)) ∧ ¬(Q(f(x)))))) ∧ ∀(x, ¬((Q(x) ∧ ¬(Q(f(x))))))) ∧ Q(x)) ∧ ¬(Q(f(f(x))))))) by Cut(s_8, s_6)
    val s_10 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x, (Q(x) ==> Q(f(x)))) ==> (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Restate.from(s_9)
    val s_11 = have(( ∀(x, (Q(x) ==> Q(f(x)))), (∀(x_1, (Q(x_1) ==> Q(f(x_1)))) ==> (Q(f(x)) ==> Q(f(f(x))))) ) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s_3, s_10)
    val s_12 = have(∀(x, (Q(x) ==> Q(f(x)))) ⊢ (Q(x) ==> Q(f(f(x))))) by Cut(s_4, s_11)
  }


  val thm1bis = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    have(thesis) by Tableau
  }

  // println(prettyProof(thm1bis.proof))
  // println(prettySCProof(thm1bis.proof.toSCProof))
  // println(scproof2code(thm1bis.proof.toSCProof))
  // println(scproof2code(optimizeProofIteratively(thm1bis.proof.toSCProof)))

  val thm1bis_raw = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s0 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) subproof {
      val s00 = have(( S(x, y_1), ¬(S(x, y_1)) ) ⊢ (  )) by Restate
      val s01 = have(( ¬(S(x, y_1)), ∀(y, S(x, y)) ) ⊢ (  )) by LeftForall(s00)
      val s02 = have(( ∀(y, S(x, y)), ∀(x_2, ¬(S(x_2, y_1))) ) ⊢ (  )) by LeftForall(s01)
      val s03 = have(( ∀(x_2, ¬(S(x_2, y_1))), ∃(x, ∀(y, S(x, y))) ) ⊢ (  )) by LeftExists(s02)
      val s04 = have(( ∃(x, ∀(y, S(x, y))), ∃(y_1, ∀(x_2, ¬(S(x_2, y_1)))) ) ⊢ (  )) by LeftExists(s03)
      val s05 = have((∃(x, ∀(y, S(x, y))) ∧ ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ (  )) by Weakening(s04)
      val s06 = have((∃(x, ∀(y, S(x, y))) ∧ ∃(y_1, ∀(x_2, ¬(S(x_2, y_1))))) ⊢ (  )) by Weakening(s05)
      val s07 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by Restate.from(s06)
    }
  }

  val thm1bis_optimized = Theorem(∃(x, ∀(y, S(x, y))) |- ∀(y, ∃(x, S(x, y)))) {
    val s0 = have(( S(x, y_1), ¬(S(x, y_1)) ) ⊢ (  )) by Restate
    val s1 = have(( ¬(S(x, y_1)), ∀(y, S(x, y)) ) ⊢ (  )) by LeftForall(s0)
    val s2 = have(( ∀(y, S(x, y)), ∀(x_2, ¬(S(x_2, y_1))) ) ⊢ (  )) by LeftForall(s1)
    val s3 = have(( ∀(x_2, ¬(S(x_2, y_1))), ∃(x, ∀(y, S(x, y))) ) ⊢ (  )) by LeftExists(s2)
    val s4 = have(( ∃(x, ∀(y, S(x, y))), ∃(y_1, ∀(x_2, ¬(S(x_2, y_1)))) ) ⊢ (  )) by LeftExists(s3)
    val s5 = have(∃(x, ∀(y, S(x, y))) ⊢ ∀(y, ∃(x, S(x, y)))) by Restate.from(s4)
  }

}
