package lisa.automation

import lisa.fol.FOL.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.unification.UnificationUtils.*
import scala.util.boundary, boundary.break


/**
  * A tactic object that applies given arguments to a theorem by guessing its good instantiation.
  * 
  * '''Example usage:'''
  *{{{
  * val thm = have(transitive(z) |- x ∈ y ==> (y ∈ z ==> x ∈ z)) by ...
  * val fact1 = have(a ∈ b) by ...
  * val fact2 = have(b ∈ c) by ...
  * have(transitive(c) |- a ∈ c) by (Apply(thm) on (fact1, fact2))
  * }}}
  * 
  * where `x`, `y`, `z` are variables and `a`, `b`, `c` are constants.
  * 
  * In some cases, this tactic also guesses the good instantiation of the facts. This feature 
  * however is not reliable at the moment.
  * 
  * @param lib the library that is being used 
  * @param proof the ongoing proof object in which the tactic is called
  * @param thm the reference theorem on which the arguments are applied. 
  * 
  * TODO: reimplement with a Horn clause solver
  */
class Apply(using val lib: Library, val proof: lib.Proof)(thm: proof.Fact) extends ProofTactic {

  /**
    * Converts a substitution map to a sequence of [[SubstPair]]
    */
  extension (subst: TermSubstitution) def toTSubstPair: Seq[SubstPair] = subst.map((k, v) => SubstPair(k, v)).toSeq

  extension (subst: FormulaSubstitution) def toFSubstPair: Seq[SubstPair] = subst.map((k, v) => SubstPair(k, v)).toSeq


  /**
    * Converts a sequent to a normal form where implications are passed to the left and where conjuctions are split in the premises.
    * 
    * @param seq the sequent to be reduced in normal form
    */
  private def normalForm(seq: Sequent): Sequent =
    def removeImplies(s: Sequent): Sequent = 
      if s.right.isEmpty then 
        s 
      else
        s.right.head match
          case AppliedConnector(Implies, Seq(phi, psi)) => removeImplies(s.left + phi |- psi)
          case _ => s

    
    
    def removeConjunctions(s: Sequent): Sequent = 
      def rec(f: Formula): Set[Formula] = 
      f match
        case AppliedConnector(And, Seq(phi, psi)) => rec(phi) ++ rec(psi)
        case _ => Set(f)
      s.left.flatMap(rec) |- s.right

    removeConjunctions(removeImplies(seq))

  /**
    * Search the premises of a sequent to find one that is matched by a given formula.
    * Performing the resulting substitution inside this premise gives the formula passed as argument. 
    *
    * @param seq the sequent whose premises are references
    * @param f the formula to match
    * @param takenTVars any term variable in the template which cannot be substituted, i.e., treated as constant
    * @param takenFVars any formula variable in the template which cannot be substituted, i.e., treated as constant
    * @return a variable assignment such that substituting the variables of seq makes f appear in one of its premises. If no such substitution exists return None.
    */
  private def searchPremises(seq: Sequent, f: Formula, takenTVars: Iterable[Variable] = Iterable.empty, takenFVars: Iterable[VariableFormula] = Iterable.empty): Option[(FormulaSubstitution, TermSubstitution)] =
    seq.left.foldLeft[Option[(FormulaSubstitution, TermSubstitution)]](None)((assignment, cclPrem) =>
      assignment match
        case None => matchFormula(f, cclPrem, takenTVars, takenFVars)
        case _ => assignment
    )

  /**
    * Search the premises of a sequent to find one that matches a given formula.
    * Performing the resulting substitution inside this formula gives the premise. 
    *
    * @param seq the sequent whose premises are being searched
    * @param f the reference formula
    * @param takenTVars any term variable in the template which cannot be substituted, i.e., treated as constant
    * @param takenFVars any formula variable in the template which cannot be substituted, i.e., treated as constant
    * @return a variable assignment such that substituting the variables of f makes f appear in one of seq's premises. If no such substitution exists return None.
    */
  private def searchPremisesRev(seq: Sequent, f: Formula, takenTVars: Iterable[Variable] = Iterable.empty, takenFVars: Iterable[VariableFormula] = Iterable.empty): Option[(FormulaSubstitution, TermSubstitution)] =
    seq.left.foldLeft[Option[(FormulaSubstitution, TermSubstitution)]](None)((assignment, cclPrem) =>
      assignment match
        case None => matchFormula(cclPrem, f, takenTVars, takenFVars)
        case _ => assignment
    )

  /**
    * Substitute the variables of a fact with given assignments.
    *
    * @param proof the ongoing proof object in which the substitution happens
    * @param fact the fact whose variables are being substituted
    * @param fSubst the assignment for formula variables
    * @param tSubst the assignment for term variables
    */
  private def substitute(using _proof: lib.Proof)(fact: _proof.Fact, fSubst: FormulaSubstitution, tSubst: TermSubstitution): _proof.Fact =
    fact.of(fSubst.toFSubstPair: _*).of(tSubst.toTSubstPair: _*)

  /**
  * Applies on method with a varargs instead of a sequence.
  */
  infix def on(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = on(premises.toSeq)(bot)


  /**
    * Executes the tactic. See class description for use cases.
    *
    * @param premises the facts that are applied to the theorem
    * @param excluding the variables that are not to be substituted
    * @param bot the sequent the user want to prove
    */
  infix def on(premises: Seq[proof.Fact], excluding: Iterable[Variable | VariableFormula] = Set())(bot: Sequent): proof.ProofTacticJudgement =

    if thm == null then
      proof.InvalidProofTactic("The theorem is null. Please check that it has been defined earlier in the proof.")
    else if premises.exists(_ == null) then
      proof.InvalidProofTactic("One of the premises is null. Please check that they all have been defined earlier in the proof.")
    else
      // STEP 0: Separate the variables and the variable formula in their respective sets
      val (excludingTVars, excludingFVars) = excluding.foldLeft[(Set[Variable], Set[VariableFormula])](Set(), Set())((acc, v) => v match
        case v: Variable => (acc._1 + v, acc._2)
        case v: VariableFormula => (acc._1, acc._2 + v)
      )

      boundary:
        TacticSubproof { sp ?=>

          // STEP 1: Convert the given theorem, facts and sequent to their normal forms
          val botNormalized: Sequent = normalForm(bot)
          val thmNormalized: sp.Fact = lib.have(normalForm(thm.statement)) by Restate.from(thm)
          val premisesNormalized = premises.map(p => lib.have(normalForm(p.statement)) by Restate.from(p))
          
          // STEP 2: Unify the conclusion of the sequent the user want to prove and the conclusion
          val thmAfterCclUnification: sp.Fact = 
            (botNormalized.right.isEmpty, thmNormalized.statement.right.isEmpty) match
              case (true, true) => thmNormalized
              case (true, false) => break(proof.InvalidProofTactic(s"The given theorem could not prove the sequent."))
              case (false, true) => break(proof.InvalidProofTactic(s"The given theorem could not prove the sequent."))
              case (false, false) => 
                val botCcl: Formula = botNormalized.right.head
                val thmCcl: Formula = thmNormalized.statement.right.head

                matchFormula(botCcl, thmCcl, excludingTVars, excludingFVars) match
                  //Unification succeeded, subtitution can be performed
                  case Some((formulaCclAssignment, termCclAssignment)) => substitute(thmNormalized, formulaCclAssignment, termCclAssignment)
                  // STEP 2 failed
                  case None => break(proof.InvalidProofTactic(s"The conclusion of the goal and the theorem could not be unified."))

          // STEP 3: Process each fact
          val thmAfterPrems: sp.Fact = {

            premisesNormalized.foldLeft(lib.have(thmAfterCclUnification))((updatedThm, premNormalized) => {

              
              val premCcl: Formula = premNormalized.statement.right.head

              // STEP 3.1: Unify the conclusion of the fact with a premise of the theorem
              // Three possibilities:
              //   - the unification succeeded and the variables in the theorem are subtituted to match the conclusion of the fact;
              //   - if the unification did not succeeded, try the unification in the other direction, i.e. try to specify the fact
              //     instead of the theorem. If this works, make the susbtitution inside the fact;
              //   - both unifications do not succeed and the fact is dropped.
              //     TODO: add a warning when the fact is dropped
              val conclusionsUnification: Option[(sp.Fact, sp.Fact)] = 
                searchPremises(updatedThm.statement, premCcl, excludingTVars, excludingFVars) match
                  case Some((fSubstAfterPrem, tSubstAfterPrem)) => Some((substitute(updatedThm, fSubstAfterPrem, tSubstAfterPrem), premNormalized))
                  case None => 
                    searchPremisesRev(updatedThm.statement, premCcl, excludingTVars, excludingFVars) match
                      case Some((fSubstAfterPrem, tSubstAfterPrem)) => Some((updatedThm, substitute(premNormalized, fSubstAfterPrem, tSubstAfterPrem)))
                      case None =>  None

              conclusionsUnification match 
                case Some(updatedThmAfterCclUnification, premAfterCclUnification) =>

                  // STEP 3.2: For each premise of the fact:
                  //   - check if it is in the sequent the user want to prove. If yes, add it to the preconditions of the theorem
                  //     using weakening;
                  //   - else if it matches one of the premises of the theorem specify the theorem by using the appropriate sustitution.
                  //     When performing this operation, the conclusion of the fact must be temporarily removed from the premises of the theorem
                  //     to avoid buggy situations in case the fact is of the form p |- p;
                  //   - else add the premise to the premises of the theorem using weakening.
                  val premCclAfterCclUnification: Formula = premAfterCclUnification.statement.right.head

                  val updatedThmAfterWeakening: sp.Fact = 
                    premAfterCclUnification.statement.left.foldLeft(updatedThmAfterCclUnification)((updatedThmDuringWeakening, premPrem) => {
                      if botNormalized.left.contains(premPrem) then 
                        lib.have(updatedThmDuringWeakening.statement +<< premPrem) by Weakening(updatedThmDuringWeakening)
                      else 
                        searchPremises(updatedThmDuringWeakening.statement -<? premCclAfterCclUnification, premPrem, excludingTVars, excludingFVars) match
                          case Some((fSubstDuringWeakening, tSubstDuringWeakening)) =>
                            substitute(updatedThmDuringWeakening, fSubstDuringWeakening, tSubstDuringWeakening)
                          case None =>
                            lib.have(updatedThmDuringWeakening.statement +<< premPrem) by Weakening(updatedThmDuringWeakening)
                    })


                  // STEP 3.3 Use cut to apply the conclusion of the fact to the theorem
                  // TODO: maybe throw a warning when the fact cannot be applied instead of making the proof crash
                  val cutStep: sp.ProofTacticJudgement = Cut(premAfterCclUnification, updatedThmAfterWeakening)(updatedThmAfterWeakening.statement -<? premCclAfterCclUnification)

                  if cutStep.isValid then
                    lib.have(cutStep)
                  else
                    break(proof.InvalidProofTactic(s"The following argument could not be applied to the theorem\n${premAfterCclUnification.statement} \n Deduced theorem: ${updatedThmAfterWeakening.statement}"))


                // STEP 3.1 failed: the fact is dropped
                case None => updatedThm
                  
            })
          }
          
          // STEP 4: If some cases, after all these operations, the theorem can remain too general to prove the sequent.
          //         To avoid such situation, perform a last unification between the premises of the sequent and those 
          //         of the theorem.
          val thmAfterLastUnification: sp.Fact = botNormalized.left.foldLeft(thmAfterPrems)((updatedThm, premBot) => {
            searchPremises(updatedThm.statement, premBot, excludingTVars, excludingFVars) match 
              case Some(fSubst, tSubst) => substitute(updatedThm, fSubst, tSubst)
              case None => updatedThm
          })

          // STEP 5: Prove the sequent using the theorem obtained with the previous steps. Weakening is necessary in case 
          //         additional preconditions that do not appear in the theorem are present in the sequent.
          val finalStep: sp.ProofTacticJudgement = Weakening(thmAfterLastUnification)(bot)
          if finalStep.isValid then
            lib.have(finalStep)
          else
            break(proof.InvalidProofTactic(s"The given theorem could not prove the sequent.\n Deduced theorem: ${thmAfterLastUnification.statement}"))


        }

}

/**
  * Helper that creates an [[Apply]] object.
  */
object Apply {
  def apply(using lib: Library, _proof: lib.Proof)(thm: _proof.Fact): Apply{val proof: _proof.type} = (new Apply(using lib, _proof)(thm)).asInstanceOf
}

/**
  * Helper to call the Apply tactic without arguments. When no facts are provided by the user, they can call
  * {{{
  *   Exact(thm)
  * }}} 
  * as a shortcut for 
  * {{{
  *   Apply(thm).on()
  * }}}
  * 
  * TODO: find an appropriate name for this tactic or replace it with Apply
  */
object Exact {
  def apply(using lib: Library, _proof: lib.Proof)(thm: _proof.Fact)(bot: Sequent): _proof.ProofTacticJudgement = Apply(thm).on()(bot)
}