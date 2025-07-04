package lisa.automation

import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofTacticLib.*
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.SimpleDeducedSteps.*
import lisa.utils.fol.FOL.{*, given}
import lisa.utils.unification.UnificationUtils.*
import lisa.automation.Tautology
import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply as Substitute}
import lisa.{HintDatabase, Hint}

/**
  * This tactic aims to reduce and resolve arbitrary set-membership and equality
  * questions by using registered theorems as hints. This is similar in spirit
  * to the `simp` tactic of Lean.
  *
  * @param db Hint database used for simplifications.
  */
class Simplify(using db: HintDatabase) extends ProofTactic
    with ProofSequentTactic {

  /**
    * Returns the chain of hints that can be used to simplify `t` at the top-level.
    *
    * TODO: Recurse on subterms.
    */
  private def termSimplifications(t: Expr[Ind]): List[Hint[Ind]] =
    db.findTermHint(t) match {
      case Some(hint) =>
        val (u, substitutions) = hint(t)
        hint :: termSimplifications(u)
      case None =>
        Nil
    }

  /**
    * Attemps to simplify the given term by repeatedly applying hints from the database.
    * Returns a proof of `t === s` for some simplified term `s`.
    *
    * If no hints apply, this proof tactic fails.
    */
  private def simplifyTerm(using lib: Library, proof: lib.Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = {
    val simplifications = termSimplifications(t)

    if simplifications.isEmpty then proof.InvalidProofTactic("Cannot simplify term.")
    else TacticSubproof {
      import lib.*

      have(t === t) by Congruence

      var currentTerm = t
      for (hint <- simplifications) {
        val (u, substitutions) = hint(currentTerm)
        thenHave(t === u) by Substitute(hint.source.asInstanceOf[proof.Fact].of(substitutions*))
        currentTerm = u
      }
    }
  }

  /**
    * Returns the chain of hints that can be used to simplify `f` at the top-level.
    *
    * TODO: Recurse on subterms.
    */
  private def formulaSimplifications(f: Expr[Prop]): List[Hint[Prop]] =
    db.findFormulaHint(f) match {
      case Some(hint) =>
        val (g, substitutions) = hint(f)
        hint :: formulaSimplifications(g)
      case None =>
        Nil
    }

  /**
    * Attemps to simplify the given formula by repeatedly applying hints from the database.
    * Returns a proof of `f <=> g` for some simplified formula `g`.
    *
    * If no hints apply, this proof tactic fails.
    */
  private def simplifyFormula(using lib: Library, proof: lib.Proof)(f: Expr[Prop]): proof.ProofTacticJudgement = {
    val simplifications = formulaSimplifications(f)

    TacticSubproof { sp ?=>
      import lib.*

      have(f <=> f) by Congruence
      var currentFormula = f

      if simplifications.nonEmpty then {
        for (hint <- simplifications) {
          val (g, substitutions) = hint(currentFormula)
          thenHave(f <=> g) by Substitute(hint.source.asInstanceOf[proof.Fact].of(substitutions*))
          currentFormula = g
        }
      }

      // Once there are no more simplifications, recurse on subterms
      var subtermProgress = false
      currentFormula match {
        case ¬(g) =>
          simplifyFormula(g) match {
            case valid: sp.ValidProofTactic =>
              subtermProgress = true
              val (_ <=> gSimpl) = (valid.bot.right.head: @unchecked)
              currentFormula = gSimpl

              val l = lastStep
              have(valid)
              have(f <=> gSimpl) by Tautology.from(l, lastStep)
            case invalid: sp.InvalidProofTactic => ()
          }

        case _ /\ _ | _ \/ _ | _ ==> _ | _ <=> _ =>
          val App(App(connective: Constant[Prop >>: Prop >>: Prop], l), r) = (currentFormula: @unchecked)

          val (leftEq, leftSimpl) = simplifyFormula(l) match {
            case valid: sp.ValidProofTactic =>
              subtermProgress = true
              val (_ <=> leftSimpl) = (valid.bot.right.head: @unchecked)
              (have(valid), leftSimpl)
            case invalid: sp.ValidProofTactic =>
              (have(l <=> l) by Restate, l)
          }

          val (rightEq, rightSimpl) = simplifyFormula(r) match {
            case valid: sp.ValidProofTactic =>
              subtermProgress = true
              val (_ <=> rightSimpl) = (valid.bot.right.head: @unchecked)
              (have(valid), rightSimpl)
            case invalid: sp.InvalidProofTactic =>
              (have(r <=> r) by Restate, r)
          }

          if subtermProgress then {
            currentFormula = connective(leftSimpl)(rightSimpl)
            have(f <=> currentFormula) by Tautology.from(lastStep, leftEq, rightEq)
          }
        case _ => ()
      }

      if currentFormula eq f then have(sp.InvalidProofTactic("Could not simplify formula."))
      else if subtermProgress then
        // Continue recursing if we made progress on subterms
        simplifyFormula(currentFormula) match {
          case valid: sp.ValidProofTactic => have(valid)
          case invalid: sp.InvalidProofTactic => ()
        }
    }
  }

  /**
    * Tries to prove the given sequent by simplifying it to trivial statements.
    */
  def apply(using lib: Library, proof: lib.Proof)(conclusion: Sequent): proof.ProofTacticJudgement = {
    conclusion.right.head match {
      case l === r =>
        TacticSubproof { sp ?=>
          import lib.*

          val (leftEq, leftSimpl) = simplifyTerm(l) match {
            case valid: sp.ValidProofTactic =>
              val (_ === leftSimpl) = (valid.bot.right.head: @unchecked)
              (have(valid), leftSimpl)
            case invalid: sp.ValidProofTactic =>
              (have(l === l) by Restate, l)
          }

          val (rightEq, rightSimpl) = simplifyTerm(r) match {
            case valid: sp.ValidProofTactic =>
              val (_ === rightSimpl) = (valid.bot.right.head: @unchecked)
              (have(valid), rightSimpl)
            case invalid: sp.InvalidProofTactic =>
              (have(r === r) by Restate, r)
          }

          if isSame(leftSimpl, rightSimpl) then
            have(l === r) by Congruence.from(leftEq, rightEq)
          else
            have(sp.InvalidProofTactic(s"Could not prove that $l = $r."))
        }

      case _ => proof.InvalidProofTactic("Cannot simplify expression.")
    }
  }
}
