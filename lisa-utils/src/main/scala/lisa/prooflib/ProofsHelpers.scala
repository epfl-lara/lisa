package lisa.prooflib

import lisa.prooflib.BasicStepTactic.Rewrite
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.parsing.FOLPrinter
import lisa.utils.{_, given}

import scala.annotation.targetName

trait ProofsHelpers {
  library: Library & WithTheorems =>

  import lisa.fol.FOL.{given, *}

  given Library = library

  class HaveSequent private[ProofsHelpers] (bot: Sequent, safe:Boolean = false) {
    val x: lisa.fol.FOL.Sequent = bot
    inline infix def by(using proof: library.Proof, line: sourcecode.Line, file: sourcecode.File): By { val _proof: proof.type } = By(proof, line, file).asInstanceOf

    class By(val _proof: library.Proof, line: sourcecode.Line, file: sourcecode.File) {

      private val bot = HaveSequent.this.bot ++ (F.iterable_to_set(_proof.getAssumptions) |- ())
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

  def have(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(v: proof.Fact | proof.ProofTacticJudgement) = v match {
    case judg: proof.ProofTacticJudgement => judg.validate(line, file)
    case fact: proof.Fact @unchecked => HaveSequent(proof.sequentOfFact(fact)).by(using proof, line, file)(Rewrite(using library, proof)(fact))
  }

  /**
   * Claim the given Sequent as a ProofTactic directly following the previously proven tactic,
   * which may require a justification by a proof tactic.
   */
  def thenHave(using proof: library.Proof)(res: Sequent): AndThenSequent = AndThenSequent(res)

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
   * Assume the given formula in all future left hand-side of claimed sequents.
   */
  def assume(using proof: library.Proof)(f: Formula): proof.ProofStep = {
    proof.addAssumption(f)
    have(() |- f) by BasicStepTactic.Hypothesis
  }
   */
  /**
   * Assume the given formulas in all future left hand-side of claimed sequents.
   */
  def assume(using proof: library.Proof)(fs: Formula*): proof.ProofStep = {
    fs.foreach(f => proof.addAssumption(f))
    have(() |- fs.toSet) by BasicStepTactic.Hypothesis
  }

  def thesis(using proof: library.Proof): Sequent = proof.possibleGoal.get
  def goal(using proof: library.Proof): Sequent = proof.possibleGoal.get

  def lastStep(using proof: library.Proof): proof.ProofStep = proof.mostRecentStep

  def sorry(using proof: library.Proof): proof.ProofStep = have(thesis) by Sorry

  def showCurrentProof(using om: OutputManager, _proof: library.Proof)(): Unit = {
    om.output("Current proof of " + _proof.owningTheorem.prettyGoal + ": ")
    om.output(
      lisa.utils.parsing.ProofPrinter.prettyProof(_proof, 2)
    )
  }

  extension (using proof: library.Proof)(fact: proof.Fact) {
    def of(insts: F.SubstPair*): proof.InstantiatedFact = {
      proof.InstantiatedFact(fact, insts)
    }
  }

  def currentProof(using p: library.Proof): Library#Proof = p

  ////////////////////////////////////////
  //  DSL for definitions and theorems  //
  ////////////////////////////////////////

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

  class The(val out: Variable, val f: Formula)(
      val just: JUSTIFICATION
  )
  class definitionWithVars[N <: Arity](val args: Variable *** N) {

    // inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(t: Term) = simpleDefinition(lambda(args, t, args.length))
    // inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(f: Formula) = predicateDefinition(lambda(args, f, args.length))

    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(t: The): ConstantFunctionLabelOfArity[N] =
      FunctionDefinition[N](name.value, name.value, line.value, file.value)(args.toSeq, t.out, t.f, t.just).label

    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(term: Term): ConstantFunctionLabelOfArity[N] =
      SimpleFunctionDefinition[N](name.value, name.value, line.value, file.value)(lambda(args.toSeq, term).asInstanceOf).label

    inline infix def -->(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(formula: Formula): ConstantPredicateLabelOfArity[N] =
      PredicateDefinition[N](name.value, name.value, line.value, file.value)(lambda(args.toSeq, formula).asInstanceOf).label

  }

  def DEF[N <: Arity, T <: Tuple](args: T)(using Tuple.Size[T] =:= N, Tuple.Union[T] <:< Variable): definitionWithVars[N] = new definitionWithVars[N](args.asInstanceOf)
  def DEF(arg: Variable): definitionWithVars[1] = new definitionWithVars[1](EmptyTuple.*:[Variable, EmptyTuple](arg)) // todo conversion to empty tuple gets bad type

  // def DEF: definitionWithVars[0] = new definitionWithVars[0](EmptyTuple) //todo conversion to empty tuple gets bad type

  // Definition helpers, not part of the DSL

  /**
   * Allows to make definitions "by unique existance" of a function symbol
   */
  class FunctionDefinition[N <: F.Arity](using om: OutputManager)(val name: String, val fullName: String, line: Int, file: String)(
      val vars: Seq[F.Variable],
      val out: F.Variable,
      val f: F.Formula,
      j: JUSTIFICATION
  ) extends DEFINITION(line, file) {
    // val expr = LambdaExpression[Term, Formula, N](vars, f, valueOf[N])

    lazy val label: ConstantFunctionLabelOfArity[N] = (if (vars.length == 0) F.Constant(name) else F.ConstantFunctionLabel[N](name, vars.length.asInstanceOf)).asInstanceOf

    val innerJustification: theory.FunctionDefinition = {
      val conclusion: F.Sequent = j.statement
      val pr: SCProof = SCProof(IndexedSeq(SC.Restate(conclusion.underlying, -1)), IndexedSeq(conclusion.underlying))
      if (!(conclusion.left.isEmpty && (conclusion.right.size == 1))) {
        om.lisaThrow(
          UserInvalidDefinitionException(
            name,
            s"The given justification is not valid for a definition" +
              s"The justification should be of the form ${FOLPrinter.prettySequent((() |- F.BinderFormula(F.ExistsOne, out, F.VariableFormula("phi"))).underlying)}" +
              s"instead of the given ${FOLPrinter.prettySequent(conclusion.underlying)}"
          )
        )
      }
      if (!(f.freeSchematicLabels.subsetOf(vars.toSet + out))) {
        om.lisaThrow(
          UserInvalidDefinitionException(
            name,
            s"The definition is not allowed to contain schematic symbols or free variables." +
              s"The symbols {${(f.freeSchematicLabels -- vars.toSet - out).mkString(", ")}} are free in the expression ${f.toString}."
          )
        )
      }
      val proven = conclusion.right.head match {
        case F.BinderFormula(F.ExistsOne, bound, inner) => inner
        case F.BinderFormula(F.Exists, x, F.BinderFormula(F.Forall, y, F.ConnectorFormula(F.Iff, Seq(l, r)))) if F.isSame(l, x === y) => r
        case F.BinderFormula(F.Exists, x, F.BinderFormula(F.Forall, y, F.ConnectorFormula(F.Iff, Seq(l, r)))) if F.isSame(r, x === y) => l
        case _ =>
          om.lisaThrow(
            UserInvalidDefinitionException(
              name,
              s"The given justification is not valid for a definition" +
                s"The justification should be of the form ${FOLPrinter.prettySequent((() |- F.BinderFormula(F.ExistsOne, out, F.VariableFormula("phi"))).underlying)}" +
                s"instead of the given ${FOLPrinter.prettySequent(conclusion.underlying)}"
            )
          )
      }
      val underf = f.underlying
      val undervars = vars.map(_.underlyingLabel)
      val ulabel = K.ConstantFunctionLabel(name, vars.size)
      val judgement = theory.makeFunctionDefinition(pr, Seq(j.innerJustification), ulabel, out.underlyingLabel, K.LambdaTermFormula(undervars, underf), proven.underlying)
      judgement match {
        case K.ValidJustification(just) =>
          just
        case wrongJudgement: K.InvalidJustification[?] =>
          if (!theory.belongsToTheory(underf)) {
            import K.findUndefinedSymbols
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(underf)} are unknown and you need to define them first."
              )
            )
          }
          if (!theory.isAvailable(ulabel)) {
            om.lisaThrow(UserInvalidDefinitionException(name, s"The symbol ${name} has already been defined and can't be redefined."))
          }
          if (!(underf.freeSchematicTermLabels.subsetOf(undervars.toSet + out.underlyingLabel) && underf.schematicFormulaLabels.isEmpty)) {
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"The definition is not allowed to contain schematic symbols or free variables." +
                  s"Kernel returned error: The symbols {${(underf.freeSchematicTermLabels -- undervars.toSet - out.underlyingLabel ++ underf.freeSchematicTermLabels)
                      .mkString(", ")}} are free in the expression ${underf.toString}."
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

    // val label: ConstantTermLabel[N]
    val statement: F.Sequent =
      () |- F.Forall(
        out,
        Iff(
          equality(
            (label match {
              case l: F.Constant => l
              case l: F.ConstantFunctionLabel[?] => l(vars)
            }),
            out
          ),
          f
        )
      )

    library.last = Some(this)

  }

  /**
   * Allows to make definitions "by equality" of a function symbol
   */
  class SimpleFunctionDefinition[N <: F.Arity](using om: OutputManager)(name: String, fullName: String, line: Int, file: String)(
      val lambda: LambdaExpression[Term, Term, N],
      out: F.Variable,
      j: JUSTIFICATION
  ) extends FunctionDefinition[N](name, fullName, line, file)(lambda.bounds.asInstanceOf, out, out === lambda.body, j) {}

  object SimpleFunctionDefinition {
    def apply[N <: F.Arity](using om: OutputManager)(name: String, fullName: String, line: Int, file: String)(lambda: LambdaExpression[Term, Term, N]): SimpleFunctionDefinition[N] = {

      // THM(using om: OutputManager)(val statement: F.Sequent, val fullName: String, line: Int, file: String, val kind: TheoremKind)(computeProof: Proof ?=> Unit)
      val intName = "definition_" + fullName
      val out = Variable(freshId(lambda.allSchematicLabels.map(_.id), "y"))
      val defThm = new THM(F.ExistsOne(out, out === lambda.body), intName, line, file, InternalStatement)({
        have(SimpleDeducedSteps.simpleFunctionDefinition(lambda, out))
      })
      new SimpleFunctionDefinition[N](name, fullName, line, file)(lambda, out, defThm)
    }
  }

  class PredicateDefinition[N <: F.Arity](using om: OutputManager)(name: String, fullName: String, line: Int, file: String)(val lambda: LambdaExpression[Term, Formula, N])
      extends DEFINITION(line, file) {

    lazy val vars: Seq[F.Variable] = lambda.bounds.asInstanceOf
    val arity = lambda.arity

    lazy val label: ConstantPredicateLabelOfArity[N] = {
      (
        if (vars.length == 0) F.ConstantFormula(name)
        else F.ConstantPredicateLabel[N](name, vars.length.asInstanceOf[N])
      ).asInstanceOf[ConstantPredicateLabelOfArity[N]]
    }

    val innerJustification: theory.PredicateDefinition = {
      import lisa.utils.K.{predicateDefinition, findUndefinedSymbols}
      val underlambda = lambda.underlyingLTF
      val ulabel = K.ConstantFunctionLabel(name, vars.size)
      val undervars = vars.map(_.asInstanceOf[F.Variable].underlyingLabel)
      val judgement = theory.predicateDefinition(name, lambda.underlyingLTF)
      judgement match {
        case K.ValidJustification(just) =>
          just
        case wrongJudgement: K.InvalidJustification[?] =>
          if (!theory.belongsToTheory(underlambda.body)) {
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(underlambda.body)} are unknown and you need to define them first."
              )
            )
          }
          if (!theory.isAvailable(ulabel)) {
            om.lisaThrow(UserInvalidDefinitionException(name, s"The symbol ${name} has already been defined and can't be redefined."))
          }
          if (!(underlambda.body.freeSchematicTermLabels.subsetOf(undervars.toSet) && underlambda.body.schematicFormulaLabels.isEmpty)) {
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"The definition is not allowed to contain schematic symbols or free variables." +
                  s"Kernel returned error: The symbols {${(underlambda.body.freeSchematicTermLabels -- undervars.toSet ++ underlambda.body.freeSchematicTermLabels)
                      .mkString(", ")}} are free in the expression ${underlambda.body.toString}."
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

    val statement: F.Sequent = () |- Iff(
      (label match {
        case l: F.ConstantFormula => l
        case l: F.ConstantPredicateLabel[?] => l(vars)
      }),
      lambda.body
    )

    library.last = Some(this)
  }


  def fail(error:String)(using tactic: ProofTactic, proof: Library#Proof) = throw new FailedProofTactic(tactic, proof, error)



}
