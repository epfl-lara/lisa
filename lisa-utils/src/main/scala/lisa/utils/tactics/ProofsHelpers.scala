package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.Library
import lisa.utils.OutputManager
import lisa.utils.Parser.parseFormula
import lisa.utils.Parser.parseSequent
import lisa.utils.Parser.parseTerm
import lisa.utils.tactics.ProofStepLib.*
import lisa.utils.tactics.SimpleDeducedSteps.*

trait ProofsHelpers {
  library: Library & WithTheorems =>
  given Library = library
  //export BasicStepTactic.*
  //export SimpleDeducedSteps.*

  case class HaveSequent private[ProofsHelpers](bot: Sequent) {
    infix def by(just: ProofStepWithoutBot)(using om:OutputManager): just.proof.DoubleStep = {
      just.asProofStep(bot).validate
    }
  }

  case class AndThenSequent private[ProofsHelpers](bot: Sequent) {
    infix def by[N <: Int & Singleton](just: ProofStepWithoutBotNorPrem[N])(using om:OutputManager): just.proof.DoubleStep = {
      just.asProofStepWithoutBot(Seq(just.proof.mostRecentStep._2)).asProofStep(bot).validate
    }
  }

  /**
   * Claim the given Sequent as a ProofStep, which may require a justification by a proof tactic and premises.
   */
  def have(using proof: library.Proof)(res: Sequent): HaveSequent = HaveSequent(res)

  /**
   * Claim the given Sequent as a ProofStep, which may require a justification by a proof tactic and premises.
   */
  def have(using proof: library.Proof)(res: String): HaveSequent = HaveSequent(parseSequent(res))

  /**
   * Claim the given known Theorem, Definition or Axiom as a Sequent.
   */
  def have(using om:OutputManager, _proof: library.Proof)(just: theory.Justification): _proof.DoubleStep = {
    have(theory.sequentFromJustification(just)) by Restate(_proof.asOutsideFact(just))
  }

  /**
   * Import the given justification (Axiom, Theorem or Definition) into the current proof.
   */
  def withImport(using om:OutputManager, _proof: library.Proof)(just: theory.Justification): _proof.DoubleStep = have(just)


  /**
   * Claim the given Sequent as a ProofStep directly following the previously proven tactic,
   * which may require a justification by a proof tactic.
   */
  def andThen(using proof: library.Proof)(res: Sequent): AndThenSequent = AndThenSequent(res)

  /**
   * Claim the given Sequent as a ProofStep directly following the previously proven tactic,
   * which may require a justification by a proof tactic.
   */
  def andThen(using proof: library.Proof)(res: String): AndThenSequent = AndThenSequent(parseSequent(res))


  def andThen(using om:OutputManager)(pswp: ProofStepWithoutPrem[1]): pswp.proof.DoubleStep = {
    pswp.asProofStep(Seq(pswp.proof.mostRecentStep._2)).validate
  }


  /**
   * Assume the given formula in all future left hand-side of claimed sequents.
   */
  def assume(using proof: library.Proof)(f: Formula): Formula = {
    proof.addAssumption(f)
    f
  }

  given Conversion[ProofStepWithoutBotNorPrem[0], ProofStepWithoutBot] = _.asProofStepWithoutBot(Seq())


  // case class InstantiatedJustification(just:theory.Justification, instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula], instsTerm: Map[SchematicTermLabel, LambdaTermTerm], instForall:Seq[Term])

  /* //TODO: After reviewing the substitutions
    extension (just: theory.Justification) {/*
        def apply(insts: ((SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term)*): InstantiatedJustification = {
            val instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula] = insts.filter(isLTT).asInstanceOf[Seq[(SchematicVarOrPredLabel, LambdaTermFormula)]].toMap
            val instsTerm: Map[SchematicTermLabel, LambdaTermTerm] = insts.filter(isLTF).asInstanceOf[Seq[(SchematicTermLabel, LambdaTermTerm)]].toMap
            val instsForall: Seq[Term] = insts.filter(isTerm).asInstanceOf[Seq[Term]]
        InstantiatedJustification(just, instsPred, instsTerm, instsForall)
        }*/

        def apply(insts: (VariableLabel, Term)*): InstantiatedJustification = {
            InstantiatedJustification(just, Map(), insts.map((x:VariableLabel, t:Term) => (x, LambdaTermTerm(Seq(), t))).toMap, Seq())
        }
    }

    private def isTerm(x: (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term):Boolean = x.isInstanceOf[Term]
    private def isLTT(x: (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term):Boolean = x.isInstanceOf[Tuple2[_, _]] && x.asInstanceOf[Tuple2[_, _]]._2.isInstanceOf[LambdaTermTerm]
    private def isLTF(x: (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term):Boolean = x.isInstanceOf[Tuple2[_, _]] && x.asInstanceOf[Tuple2[_, _]]._2.isInstanceOf[LambdaTermFormula]

  def have(instJust: InstantiatedJustification)(using om:OutputManager): library.Proof#DoubleStep = {
    val just = instJust.just
    val (seq, ref) = proof.getSequentAndInt(just)
    if (instJust.instsPred.isEmpty && instJust.instsTerm.isEmpty && instJust.instForall.isEmpty){
      have(seq) by Restate(ref)
    } else if (instJust.instsPred.isEmpty && instJust.instForall.isEmpty){
      val res = (seq.left.map(phi => instantiateTermSchemas(phi, instJust.instsTerm)) |- seq.right.map(phi => instantiateTermSchemas(phi, instJust.instsTerm)))
      have(res) by InstFunSchema(instJust.instsTerm)(ref)
    } else if (instJust.instsTerm.isEmpty && instJust.instForall.isEmpty){
      val res = (seq.left.map(phi => instantiatePredicateSchemas(phi, instJust.instsPred)) |- seq.right.map(phi => instantiatePredicateSchemas(phi, instJust.instsPred)))
      have(res) by InstPredSchema(instJust.instsPred)(ref)
    } else if(instJust.instsPred.isEmpty && instJust.instsTerm.isEmpty){
      ???
    } else {
      ???
    }
  }

   */

}
