package lisa.prooflib

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus as SC
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.prooflib.BasicStepTactic.Rewrite
import lisa.utils.{*, given}

import scala.annotation.targetName

trait ProofsHelpers {
  library: Library & WithTheorems =>
  given Library = library

  class HaveSequent private[ProofsHelpers] (bot: Sequent) {
    inline infix def by(using proof: library.Proof, line: sourcecode.Line, file: sourcecode.File): By { val _proof: proof.type } = By(proof, line, file).asInstanceOf

    class By(val _proof: library.Proof, line: sourcecode.Line, file: sourcecode.File) {
      private val bot = HaveSequent.this.bot ++ (_proof.getAssumptions |- ())
      inline infix def apply(tactic: Sequent => _proof.ProofTacticJudgement): _proof.ProofStep & _proof.Fact = {
        tactic(bot).validate(line, file)
      }
      inline infix def apply(tactic: ProofSequentTactic): _proof.ProofStep = {
        tactic(using library, _proof)(bot).validate(line, file)
      }
    }

    inline infix def subproof(using proof: Library#Proof, om: OutputManager, line: sourcecode.Line, file: sourcecode.File)(tactic: proof.InnerProof ?=> Unit): proof.ProofStep = {
      val botWithAssumptions = HaveSequent.this.bot ++ (proof.getAssumptions |- ())
      (new BasicStepTactic.SUBPROOF(using proof)(Some(botWithAssumptions))(tactic)).judgement.validate(line, file).asInstanceOf[proof.ProofStep]
    }

  }

  class AndThenSequent private[ProofsHelpers] (bot: Sequent) {

    inline infix def by(using proof: library.Proof, line: sourcecode.Line, file: sourcecode.File): By { val _proof: proof.type } =
      By(proof, line, file).asInstanceOf[By { val _proof: proof.type }]

    class By(val _proof: library.Proof, line: sourcecode.Line, file: sourcecode.File) {
      private val bot = AndThenSequent.this.bot ++ (_proof.getAssumptions |- ())
      inline infix def apply(tactic: _proof.Fact => Sequent => _proof.ProofTacticJudgement): _proof.ProofStep = {
        tactic(_proof.mostRecentStep)(bot).validate(line, file)
      }

      inline infix def apply(tactic: ProofFactSequentTactic): _proof.ProofStep = {
        tactic(using library, _proof)(_proof.mostRecentStep)(bot).validate(line, file)
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

  def have(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(v: proof.Fact | proof.ProofTacticJudgement) = v match {
    case judg: proof.ProofTacticJudgement => judg.validate(line, file)
    case fact: proof.Fact @unchecked => HaveSequent(proof.sequentOfFact(fact)).by(using proof, line, file)(Rewrite(using library, proof)(fact))
  }

  /**
   * Claim the given Sequent as a ProofTactic directly following the previously proven tactic,
   * which may require a justification by a proof tactic.
   */
  def thenHave(using proof: library.Proof)(res: Sequent): AndThenSequent = AndThenSequent(res)

  /**
   * Claim the given Sequent as a ProofTactic, which may require a justification by a proof tactic and premises.
   */
  def thenHave(using proof: library.Proof)(res: String): AndThenSequent = AndThenSequent(lisa.utils.FOLParser.parseSequent(res))

  infix def andThen(using proof: library.Proof, line: sourcecode.Line, file: sourcecode.File): AndThen { val _proof: proof.type } = AndThen(proof, line, file).asInstanceOf

  class AndThen private[ProofsHelpers] (val _proof: library.Proof, line: sourcecode.Line, file: sourcecode.File) {
    inline infix def apply(tactic: _proof.Fact => _proof.ProofTacticJudgement): _proof.ProofStep = {
      tactic(_proof.mostRecentStep).validate(line, file)
    }
    inline infix def apply(tactic: ProofFactTactic): _proof.ProofStep = {
      tactic(using library, _proof)(_proof.mostRecentStep).validate(line, file)
    }
  }

  /*
  /**
   * Claim the given Sequent as a ProofTactic directly following the previously proven tactic,
   * which may require a justification by a proof tactic.
   */
  def thenHave(using proof: library.Proof)(res: String): AndThenSequent = AndThenSequent(parseSequent(res))


  def thenHave(using om:OutputManager)(pswp: ProofTacticWithoutPrem[1]): pswp.proof.ProofStep = {
    pswp.asProofTactic(Seq(pswp.proof.mostRecentStep._2)).validate
  }

   */
  /**
   * Assume the given formula in all future left hand-side of claimed sequents.
   */
  def assume(using proof: library.Proof)(f: Formula): proof.ProofStep = {
    proof.addAssumption(f)
    have(() |- f) by BasicStepTactic.Hypothesis
  }
  def assume(using proof: library.Proof)(fstring: String): proof.ProofStep = {
    val f = lisa.utils.FOLParser.parseFormula(fstring)
    assume(f)
  }
  def assume(using proof: library.Proof)(fs: Iterable[Formula]): proof.ProofStep = {
    fs.foreach(f => proof.addAssumption(f))
    have(() |- fs.toSet) by BasicStepTactic.Hypothesis
  }
  /*
  /**
   * Store the given import and use it to discharge the proof of one of its assumption at the very end.
   */
  def endDischarge(using proof: library.Proof)(ji: proof.OutsideFact): Unit = {
    proof.addDischarge(ji)
  }
   */

  def thesis(using proof: library.Proof): Sequent = proof.possibleGoal.get
  def goal(using proof: library.Proof): Sequent = proof.possibleGoal.get

  def lastStep(using proof: library.Proof): proof.ProofStep = proof.mostRecentStep

  def sorry(using proof: library.Proof): proof.ProofStep = have(thesis) by Sorry

  def showCurrentProof(using om: OutputManager, _proof: library.Proof)(): Unit = {
    om.output("Current proof of " + _proof.owningTheorem.prettyGoal + ": ")
    om.output(
      ProofPrinter.prettyProof(_proof, 2)
    )
  }

  // case class InstantiatedJustification(just:theory.Justification, instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula], instsTerm: Map[SchematicTermLabel, LambdaTermTerm], instForall:Seq[Term])

  private def isLTT(x: (SchematicConnectorLabel, LambdaFormulaFormula) | (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm)): Boolean =
    x.isInstanceOf[Tuple2[_, _]] && x.asInstanceOf[Tuple2[_, _]]._2.isInstanceOf[LambdaTermTerm]

  private def isLTF(x: (SchematicConnectorLabel, LambdaFormulaFormula) | (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm)): Boolean =
    x.isInstanceOf[Tuple2[_, _]] && x.asInstanceOf[Tuple2[_, _]]._2.isInstanceOf[LambdaTermFormula]

  private def isLFF(x: (SchematicConnectorLabel, LambdaFormulaFormula) | (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm)): Boolean =
    x.isInstanceOf[Tuple2[_, _]] && x.asInstanceOf[Tuple2[_, _]]._2.isInstanceOf[LambdaFormulaFormula]

  extension (using proof: library.Proof)(fact: proof.Fact) {
    def of(insts: ((SchematicConnectorLabel, LambdaFormulaFormula) | (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm))*): proof.InstantiatedFact = {
      val instsConn: Map[SchematicConnectorLabel, LambdaFormulaFormula] = insts.filter(isLFF).asInstanceOf[Seq[(SchematicConnectorLabel, LambdaFormulaFormula)]].toMap
      val instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula] = insts.filter(isLTF).asInstanceOf[Seq[(SchematicVarOrPredLabel, LambdaTermFormula)]].toMap
      val instsTerm: Map[SchematicTermLabel, LambdaTermTerm] = insts.filter(isLTT).asInstanceOf[Seq[(SchematicTermLabel, LambdaTermTerm)]].toMap
      proof.InstantiatedFact(fact, instsConn, instsPred, instsTerm)
    }
  }

  def currentProof(using p: Library#Proof): Library#Proof = p

  ////////////////////////////////////////
  //  DSL for definitions and theorems  //
  ////////////////////////////////////////

  extension (tk: TheoremKind) {

    /**
     * Declare and starts the proof of a new proposition.
     *
     * @param statement    The conclusion the theorem proves
     * @param computeProof How the proof should go.
     * @return The theorem, if proof is valid. Otherwise will terminate.
     */
    def apply(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(statement: Sequent | String)(computeProof: Proof ?=> Unit): THM = {
      val thm = new THM(statement, name.value, line.value, file.value, tk)(computeProof) {}
      if (tk == Theorem) {
        if (thm.withSorry) om.output(thm.repr, Console.YELLOW)
        else om.output(thm.repr, Console.GREEN)
      }
      thm
    }
  }

  class UserInvalidDefinitionException(val symbol: String, errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(errorMessage) { // TODO refine
    val showError: String = {
      val source = scala.io.Source.fromFile(file.value)
      val textline = source.getLines().drop(line.value - 1).next().dropWhile(c => c.isWhitespace)
      source.close()
      s"   Definition of $symbol at.(${file.value.split("/").last.split("\\\\").last}:${line.value}) is invalid:\n" +
        "   " + Console.RED + textline + Console.RESET + "\n\n" +
        "   " + errorMessage
    }
  }

  class The(val out: VariableLabel, val f: Formula)(
      val just: theory.Theorem | theory.Axiom
  )
  class definitionWithVars(val args: Seq[VariableLabel]) {
    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(t: Term) = simpleDefinition(lambda(args, t))
    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(f: Formula) = predicateDefinition(lambda(args, f))

    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(t: The) = definitionByUniqueExistance(args, t.out, t.f, t.just)

  }

  def DEF(args: VariableLabel*) = new definitionWithVars(args.toSeq)

  // Definition helpers, not part of the DSL

  /**
   * Allows to make definitions "by equality" of a function symbol
   */
  def simpleDefinition(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(lambda: LambdaTermTerm): ConstantFunctionLabel = {
    val label = ConstantFunctionLabel(name.value, lambda.vars.length)
    val judgement = simpleDefinition(name.value, lambda)
    judgement match {
      case RunningTheoryJudgement.ValidJustification(just) =>
        library.last = Some(just)
        just.label
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
        if (!theory.belongsToTheory(lambda.body)) {
          om.lisaThrow(
            UserInvalidDefinitionException(
              name.value,
              s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(lambda.body)} are unknown and you need to define them first."
            )
          )
        }
        if (!theory.isAvailable(label)) {
          om.lisaThrow(UserInvalidDefinitionException(name.value, s"The symbol ${name.value} has already been defined and can't be redefined."))
        }
        if (!lambda.body.freeSchematicTermLabels.subsetOf(lambda.vars.toSet)) {
          om.lisaThrow(
            UserInvalidDefinitionException(
              name.value,
              s"The definition is not allowed to contain schematic symbols or free variables.\n" +
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
  def definitionByUniqueExistance(using
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
    val pr: SCProof = SCProof(IndexedSeq(SC.Restate(conclusion, -1)), IndexedSeq(conclusion))
    if (!(conclusion.left.isEmpty && (conclusion.right.size == 1))) {
      om.lisaThrow(
        UserInvalidDefinitionException(
          name.value,
          s"The given justification is not valid for a definition" +
            s"The justification should be of the form ${FOLPrinter.prettySequent(() |- BinderFormula(ExistsOne, out, VariableFormulaLabel("phi")))}" +
            s"instead of the given ${FOLPrinter.prettySequent(conclusion)}"
        )
      )
    }
    val proven = conclusion.right.head match {
      case BinderFormula(ExistsOne, bound, inner) => inner
      case BinderFormula(Exists, x, BinderFormula(Forall, y, ConnectorFormula(Iff, Seq(l, r)))) if isSame(l, x === y) => r
      case BinderFormula(Exists, x, BinderFormula(Forall, y, ConnectorFormula(Iff, Seq(l, r)))) if isSame(r, x === y) => l
      case _ =>
        om.lisaThrow(
          UserInvalidDefinitionException(
            name.value,
            s"The given justification is not valid for a definition" +
              s"The justification should be of the form ${FOLPrinter.prettySequent(() |- BinderFormula(ExistsOne, out, VariableFormulaLabel("phi")))}" +
              s"instead of the given ${FOLPrinter.prettySequent(conclusion)}"
          )
        )
    }
    val judgement = theory.functionDefinition(name.value, LambdaTermFormula(vars, f), out, pr, proven, Seq(just))
    judgement match {
      case RunningTheoryJudgement.ValidJustification(just) =>
        library.last = Some(just)
        just.label
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
        if (!theory.belongsToTheory(f)) {
          om.lisaThrow(
            UserInvalidDefinitionException(
              name.value,
              s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(f)} are unknown and you need to define them first."
            )
          )
        }
        if (!theory.isAvailable(label)) {
          om.lisaThrow(UserInvalidDefinitionException(name.value, s"The symbol ${name.value} has already been defined and can't be redefined."))
        }
        if (!(f.freeSchematicTermLabels.subsetOf(vars.toSet + out) && f.schematicFormulaLabels.isEmpty)) {
          om.lisaThrow(
            UserInvalidDefinitionException(
              name.value,
              s"The definition is not allowed to contain schematic symbols or free variables." +
                s"The symbols {${(f.freeSchematicTermLabels -- vars.toSet ++ f.schematicFormulaLabels).mkString(", ")}} are free in the expression ${FOLPrinter.prettyFormula(f)}."
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
  def predicateDefinition(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(lambda: LambdaTermFormula): ConstantPredicateLabel = {
    val label = ConstantPredicateLabel(name.value, lambda.vars.length)
    val judgement = simpleDefinition(name.value, lambda)
    judgement match {
      case RunningTheoryJudgement.ValidJustification(just) =>
        library.last = Some(just)
        just.label
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
        if (!theory.belongsToTheory(lambda.body)) {
          om.lisaThrow(
            UserInvalidDefinitionException(
              name.value,
              s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(lambda.body)} are unknown and you need to define them first."
            )
          )
        }
        if (!theory.isAvailable(label)) {
          om.lisaThrow(UserInvalidDefinitionException(name.value, s"The symbol ${name.value} has already been defined and can't be redefined."))
        }
        if (!(lambda.body.freeSchematicTermLabels.subsetOf(lambda.vars.toSet) && lambda.body.schematicFormulaLabels.isEmpty)) {
          om.lisaThrow(
            UserInvalidDefinitionException(
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
