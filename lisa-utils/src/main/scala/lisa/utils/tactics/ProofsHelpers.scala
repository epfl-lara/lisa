package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Library
import lisa.utils.OutputManager
import lisa.utils.Parser.*
import lisa.utils.ProofPrinter
import lisa.utils.tactics.ProofTacticLib.*
import lisa.utils.tactics.SimpleDeducedSteps.*

import scala.annotation.targetName

trait ProofsHelpers {
  library: Library & WithTheorems =>
  given Library = library

  case class HaveSequent private[ProofsHelpers] (bot: Sequent) {
    inline infix def by(using proof: Library#Proof, om: OutputManager, line: sourcecode.Line, file: sourcecode.File): By { val _proof: proof.type } = By(proof, om, line, file).asInstanceOf

    class By(val _proof: Library#Proof, om: OutputManager, line: sourcecode.Line, file: sourcecode.File) {
      private val bot = HaveSequent.this.bot ++ (_proof.getAssumptions |- ())
      inline infix def apply(tactic: Sequent => _proof.ProofTacticJudgement): _proof.ProofStep = {
        tactic(bot).validate(line, file)
      }
      inline infix def apply(tactic: ParameterlessHave): _proof.ProofStep = {
        tactic(using _proof)(bot).validate(line, file)
      }
    }

    inline infix def subproof(using proof: Library#Proof, om: OutputManager, line: sourcecode.Line, file: sourcecode.File)(tactic: proof.InnerProof ?=> Unit): proof.ProofStep = {
      (new BasicStepTactic.SUBPROOF(using proof, om)(bot, line, file)(tactic)).judgement.validate(line, file).asInstanceOf[proof.ProofStep]
    }

  }

  case class AndThenSequent private[ProofsHelpers] (bot: Sequent) {

    inline infix def by(using proof: Library#Proof, om: OutputManager, line: sourcecode.Line, file: sourcecode.File): By { val _proof: proof.type } =
      By(proof, om, line, file).asInstanceOf[By { val _proof: proof.type }]

    class By(val _proof: Library#Proof, om: OutputManager, line: sourcecode.Line, file: sourcecode.File) {
      private val bot = AndThenSequent.this.bot ++ (_proof.getAssumptions |- ())
      inline infix def apply(tactic: _proof.Fact => Sequent => _proof.ProofTacticJudgement): _proof.ProofStep = {
        tactic(_proof.mostRecentStep)(bot).validate(line, file)
      }

      inline infix def apply(tactic: ParameterlessAndThen): _proof.ProofStep = {
        tactic(using _proof)(_proof.mostRecentStep)(bot).validate(line, file)
      }

    }
  }

  /**
   * Claim the given Sequent as a ProofTactic, which may require a justification by a proof tactic and premises.
   */
  def have(using proof: library.Proof)(res: Sequent): HaveSequent = HaveSequent(res)

  /**
   * Claim the given Sequent as a ProofTactic, which may require a justification by a proof tactic and premises.
   */
  def have(using proof: library.Proof)(res: String): HaveSequent = HaveSequent(parseSequent(res))

  /**
   * Claim the given known Theorem, Definition or Axiom as a Sequent.
   */
  def have(using om: OutputManager, _proof: library.Proof)(just: theory.Justification): _proof.ProofStep = {
    have(theory.sequentFromJustification(just)) by Restate(just: _proof.OutsideFact)
  }

  /**
   * Claim the given Sequent as a ProofTactic directly following the previously proven tactic,
   * which may require a justification by a proof tactic.
   */
  def andThen(using proof: library.Proof)(res: Sequent): AndThenSequent = AndThenSequent(res)
  /*
  /**
   * Claim the given Sequent as a ProofTactic directly following the previously proven tactic,
   * which may require a justification by a proof tactic.
   */
  def andThen(using proof: library.Proof)(res: String): AndThenSequent = AndThenSequent(parseSequent(res))


  def andThen(using om:OutputManager)(pswp: ProofTacticWithoutPrem[1]): pswp.proof.ProofStep = {
    pswp.asProofTactic(Seq(pswp.proof.mostRecentStep._2)).validate
  }

   */
  /**
   * Assume the given formula in all future left hand-side of claimed sequents.
   */
  def assume(using proof: library.Proof)(f: Formula): Formula = {
    proof.addAssumption(f)
    f
  }
  def assume(using proof: library.Proof)(fstring: String): Formula = {
    val f = lisa.utils.Parser.parseFormula(fstring)
    assume(f)
  }
  /*
  /**
   * Store the given import and use it to discharge the proof of one of its assumption at the very end.
   */
  def endDischarge(using proof: library.Proof)(ji: proof.OutsideFact): Unit = {
    proof.addDischarge(ji)
  }

  //TODO: Fishy
  given Conversion[ProofTacticWithoutBotNorPrem[0], ProofTacticWithoutBot] = _.asProofTacticWithoutBot(Seq())

   */
  def showCurrentProof(using om: OutputManager, _proof: library.Proof)(): Unit = {
    om.output("Current proof of" + _proof.owningTheorem.repr + ": ")
    om.output(
      ProofPrinter.prettyProof(_proof, 2)
    )
  }

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

  def have(instJust: InstantiatedJustification)(using om:OutputManager): library.Proof#ProofStep = {
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

  def currentProof(using p: Library#Proof): Library#Proof = p
}
