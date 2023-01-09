package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.FOLPrinter
import lisa.utils.Library
import lisa.utils.LisaException
import lisa.utils.OutputManager
import lisa.utils.ProofPrinter
import lisa.utils.UserLisaException
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
  def have(using proof: library.Proof)(res: String): HaveSequent = HaveSequent(lisa.utils.FOLParser.parseSequent(res))

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
    val f = lisa.utils.FOLParser.parseFormula(fstring)
    assume(f)
  }
  /*
  /**
   * Store the given import and use it to discharge the proof of one of its assumption at the very end.
   */
  def endDischarge(using proof: library.Proof)(ji: proof.OutsideFact): Unit = {
    proof.addDischarge(ji)
  }

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

  ////////////////////////////////////////
  //  DSL for definitions and theorems  //
  ////////////////////////////////////////

  /**
   * Declare and starts the proof of a new theorem.
   * @param statement The conclusion the theorem proves
   * @param computeProof How the proof should go.
   * @return The theorem, if proof is valid. Otherwise will terminate.
   */
  def makeTHM(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(statement: Sequent | String)(computeProof: Proof ?=> Unit): THM =
    new THM(statement, name.value, line.value, file.value)(computeProof) {}

  object The
  class definitionWithVars(val args: Seq[VariableLabel]) {
    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(t: Term) = definition(lambda(args, t))
    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(f: Formula) = definition(lambda(args, f))

    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(t: The.type)(out: VariableLabel, f: Formula)(
        just: theory.Theorem | theory.Axiom
    ) = definition(args, out, f, just)

  }

  def DEF(args: VariableLabel*) = new definitionWithVars(args.toSeq)

  /**
   * Allows to make definitions "by equality" of a function symbol
   */
  def definition(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(lambda: LambdaTermTerm): ConstantFunctionLabel = {
    val label = ConstantFunctionLabel(name.value, lambda.vars.length)
    val judgement = simpleDefinition(name.value, lambda)
    judgement match {
      case RunningTheoryJudgement.ValidJustification(just) =>
        library.last = Some(just)
        just.label
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
        if (!theory.belongsToTheory(lambda.body)) {
          om.lisaThrow(
            UserLisaException.UserInvalidDefinitionException(
              name.value,
              s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(lambda.body)} are unknown and you need to define them first."
            )
          )
        }
        if (!theory.isAvailable(label)) {
          om.lisaThrow(UserLisaException.UserInvalidDefinitionException(name.value, s"The symbol ${name.value} has already been defined and can't be redefined."))
        }
        if (!lambda.body.freeSchematicTermLabels.subsetOf(lambda.vars.toSet)) {
          om.lisaThrow(
            UserLisaException.UserInvalidDefinitionException(
              name.value,
              s"The definition is not allowed to contain schematic symbols or free variables." +
                s"The symbols {${(lambda.body.freeSchematicTermLabels -- lambda.vars.toSet).mkString(", ")}} are free in the expression ${FOLPrinter.prettyTerm(lambda.body)}."
            )
          )
        }
        om.lisaThrow(
          LisaException.InvalidKernelJustificationComputation(
            "The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or an error in LISA.",
            wrongJudgement,
            None
          )
        )
    }
  }

  /**
   * Allows to make definitions "by unique existance" of a function symbol
   */
  def definition(using
      om: OutputManager,
      name: sourcecode.Name,
      line: sourcecode.Line,
      file: sourcecode.File
  )(vars: Seq[VariableLabel], out: VariableLabel, f: Formula, just: theory.Theorem | theory.Axiom): ConstantFunctionLabel = {
    val label = ConstantFunctionLabel(name.value, vars.length)
    val conclusion: Sequent = just match {
      case thm: theory.Theorem => thm.proposition
      case ax: theory.Axiom => () |- ax.ax
    }
    val pr: SCProof = SCProof(IndexedSeq(Rewrite(conclusion, -1)), IndexedSeq(conclusion))
    val judgement = theory.functionDefinition(name.value, LambdaTermFormula(vars, f), out, pr, Seq(just))
    judgement match {
      case RunningTheoryJudgement.ValidJustification(just) =>
        library.last = Some(just)
        just.label
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
        if (!theory.belongsToTheory(f)) {
          om.lisaThrow(
            UserLisaException.UserInvalidDefinitionException(
              name.value,
              s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(f)} are unknown and you need to define them first."
            )
          )
        }
        if (!theory.isAvailable(label)) {
          om.lisaThrow(UserLisaException.UserInvalidDefinitionException(name.value, s"The symbol ${name.value} has already been defined and can't be redefined."))
        }
        if (!(f.freeSchematicTermLabels.subsetOf(vars.toSet) && f.schematicFormulaLabels.isEmpty)) {
          om.lisaThrow(
            UserLisaException.UserInvalidDefinitionException(
              name.value,
              s"The definition is not allowed to contain schematic symbols or free variables." +
                s"The symbols {${(f.freeSchematicTermLabels -- vars.toSet ++ f.schematicFormulaLabels).mkString(", ")}} are free in the expression ${FOLPrinter.prettyFormula(f)}."
            )
          )
        }
        if (!(conclusion.left.isEmpty && (conclusion.right.size == 1) && isSame(conclusion.right.head, BinderFormula(ExistsOne, out, f)))) {
          om.lisaThrow(
            UserLisaException.UserInvalidDefinitionException(
              name.value,
              s"The definition given justification does not correspond to the desired definition" +
                s"The justification should be of the form ${FOLPrinter.prettySequent(() |- BinderFormula(ExistsOne, out, f))}" +
                s"instead of the given ${FOLPrinter.prettySequent(conclusion)}"
            )
          )
        }
        om.lisaThrow(
          LisaException.InvalidKernelJustificationComputation(
            "The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or an error in LISA.",
            wrongJudgement,
            None
          )
        )
    }
  }

  /**
   * Allows to define a predicate symbol
   */
  def definition(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(lambda: LambdaTermFormula): ConstantPredicateLabel = {
    val label = ConstantPredicateLabel(name.value, lambda.vars.length)
    val judgement = simpleDefinition(name.value, lambda)
    judgement match {
      case RunningTheoryJudgement.ValidJustification(just) =>
        library.last = Some(just)
        just.label
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
        if (!theory.belongsToTheory(lambda.body)) {
          om.lisaThrow(
            UserLisaException.UserInvalidDefinitionException(
              name.value,
              s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(lambda.body)} are unknown and you need to define them first."
            )
          )
        }
        if (!theory.isAvailable(label)) {
          om.lisaThrow(UserLisaException.UserInvalidDefinitionException(name.value, s"The symbol ${name.value} has already been defined and can't be redefined."))
        }
        if (!(lambda.body.freeSchematicTermLabels.subsetOf(lambda.vars.toSet) && lambda.body.schematicFormulaLabels.isEmpty)) {
          om.lisaThrow(
            UserLisaException.UserInvalidDefinitionException(
              name.value,
              s"The definition is not allowed to contain schematic symbols or free variables." +
                s"The symbol(s) {${(lambda.body.freeSchematicTermLabels -- lambda.vars.toSet ++ lambda.body.schematicFormulaLabels).mkString(", ")}} are free in the expression ${FOLPrinter
                    .prettyFormula(lambda.body)}."
            )
          )
        }
        om.lisaThrow(
          LisaException.InvalidKernelJustificationComputation(
            "The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or an error in LISA.",
            wrongJudgement,
            None
          )
        )
    }
  }
}
