package lisa.prooflib

import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.prooflib.BasicStepTactic.Rewrite
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.{_, given}

import scala.annotation.targetName

trait ProofsHelpers {
  library: Library & WithTheorems =>

  import lisa.fol.FOL.{given, *}

  class HaveSequent(val bot: Sequent) {

    inline infix def by(using proof: library.Proof, line: sourcecode.Line, file: sourcecode.File): By { val _proof: proof.type } = By(proof, line, file).asInstanceOf

    class By(val _proof: library.Proof, line: sourcecode.Line, file: sourcecode.File) {

      val bot = HaveSequent.this.bot ++ (F.iterable_to_set(_proof.getAssumptions) |- ())
      inline infix def apply(tactic: Sequent => _proof.ProofTacticJudgement): _proof.ProofStep & _proof.Fact = {
        tactic(bot).validate(line, file)
      }
      inline infix def apply(tactic: ProofSequentTactic): _proof.ProofStep = {
        tactic(using library, _proof)(bot).validate(line, file)
      }
    }

    infix def subproof(using proof: Library#Proof, line: sourcecode.Line, file: sourcecode.File)(computeProof: proof.InnerProof ?=> Unit): proof.ProofStep = {
      val botWithAssumptions = HaveSequent.this.bot ++ (proof.getAssumptions |- ())
      val iProof: proof.InnerProof = new proof.InnerProof(Some(botWithAssumptions))
      computeProof(using iProof)
      (new BasicStepTactic.SUBPROOF(using proof)(Some(botWithAssumptions))(iProof)).judgement.validate(line, file).asInstanceOf[proof.ProofStep]
    }

  }

  class AndThenSequent private[ProofsHelpers] (val bot: Sequent) {

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
      ProofPrinter.prettyProof(_proof, 2)
    )
  }

  extension (using proof: library.Proof)(fact: proof.Fact) {
    infix def of(insts: (F.SubstPair[?] | F.Term)*): proof.InstantiatedFact = {
      proof.InstantiatedFact(fact, insts)
    }
    def statement: F.Sequent = proof.sequentOfFact(fact)
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

  type ParamsOf[S] = S match {
    case Arrow[s1, s2] => s1 *: ParamsOf[s2] 
    case _ => S *: EmptyTuple
  }

  type FromParamList[S, R] = S match {
    case EmptyTuple => R
    case s *: ss => s >>: FromParamList[ss, R]
  }

  class The(val out: Variable[T], val f: Formula)(
      val just: JUSTIFICATION
  )
  class definitionWithVars[S <: Tuple](val args: Seq[Variable[?]]) {

    // inline infix def -->(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(t: Term) = simpleDefinition(lambda(args, t, args.length))
    // inline infix def -->(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(f: Formula) = predicateDefinition(lambda(args, f, args.length))

    inline infix def -->(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(t: The): Constant[?] =
      Direct[N](name.value, line.value, file.value)(args, t.out, t.f, t.just).label

    inline infix def -->[R: Sort](using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(expr: Expr[R]): Constant[FromParamList[S, R]] =
      val res: Expr[FromParamList[S, R]] = args.toList.foldRight(expr: Expr[?])((v, acc) => Abs.unsafe(v: Variable[?], acc)).asInstanceOf[Expr[FromParamList[S, R]]]
      DirectDefinition[FromParamList[S, R]](name.value, line.value, file.value)(res)(using F.unsafeSortEvidence(res.sort)).label

  }
  //Tuple.Map[S, Variable]

  def DEF(): definitionWithVars[EmptyTuple] = new definitionWithVars[EmptyTuple](Seq())
  def DEF[S1](a: Variable[S1]): definitionWithVars[(S1 *: EmptyTuple)] = 
    new definitionWithVars(Seq(a))
  def DEF[S1, S2](a: Variable[S1], b: Variable[S2]): definitionWithVars[S1*:S2*:EmptyTuple] = 
    new definitionWithVars(Seq(a, b))
  def DEF[S1, S2, S3](a: Variable[S1], b: Variable[S2], c: Variable[S3]): definitionWithVars[S1*:S2*:S3*:EmptyTuple] =
    new definitionWithVars(Seq(a, b, c))
  def DEF[S1, S2, S3, S4](a: Variable[S1], b: Variable[S2], c: Variable[S3], d: Variable[S4]): definitionWithVars[S1*:S2*:S3*:S4*:EmptyTuple] =
    new definitionWithVars(Seq(a, b, c, d))
  def DEF[S1, S2, S3, S4, S5](a: Variable[S1], b: Variable[S2], c: Variable[S3], d: Variable[S4], e: Variable[S5]): definitionWithVars[S1*:S2*:S3*:S4*:S5*:EmptyTuple] =
    new definitionWithVars(Seq(a, b, c, d, e))
  def DEF[S1, S2, S3, S4, S5, S6](a: Variable[S1], b: Variable[S2], c: Variable[S3], d: Variable[S4], e: Variable[S5], f: Variable[S6]): definitionWithVars[S1*:S2*:S3*:S4*:S5*:S6*:EmptyTuple] =
    new definitionWithVars(Seq(a, b, c, d, e, f))
  def DEF[S1, S2, S3, S4, S5, S6, S7](a: Variable[S1], b: Variable[S2], c: Variable[S3], d: Variable[S4], e: Variable[S5], f: Variable[S6], g: Variable[S7]): definitionWithVars[S1*:S2*:S3*:S4*:S5*:S6*:S7*:EmptyTuple] =
    new definitionWithVars(Seq(a, b, c, d, e, f, g))
  

  class DirectDefinition[S : Sort](using om: OutputManager)(val fullName: String, line: Int, file: String)(val expr: Expr[S]) extends DEFINITION(line, file) {

    lazy val vars: Seq[F.Variable[?]] = ???
    val arity = ???

    lazy val label: Constant[S] = F.Constant(name)


    val innerJustification: theory.Definition = {
      import lisa.utils.K.{findUndefinedSymbols}
      val uexpr = expr.underlying
      val ucst = K.Constant(name, label.sort)
      val uvars = vars.map(_.underlying)
      val judgement = theory.makeDefinition(ucst, uexpr, uvars)
      judgement match {
        case K.ValidJustification(just) =>
          just
        case wrongJudgement: K.InvalidJustification[?] =>
          if (!theory.belongsToTheory(uexpr)) {
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"All symbols in the definition must belong to the theory. The symbols ${theory.findUndefinedSymbols(uexpr)} are unknown and you need to define them first."
              )
            )
          }
          if !theory.isAvailable(ucst) then 
            om.lisaThrow(UserInvalidDefinitionException(name, s"The symbol ${name} has already been defined and can't be redefined."))
          if !uexpr.freeVariables.nonEmpty then 
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"The definition is not allowed to contain schematic symbols or free variables. " +
                  s"The variables {${(uexpr.freeVariables).mkString(", ")}} are free in the expression ${uexpr}."
              )
            )
          if !theory.isAvailable(ucst) then 
            om.lisaThrow(UserInvalidDefinitionException(name, s"The symbol ${name} has already been defined and can't be redefined."))
          om.lisaThrow(
            LisaException.InvalidKernelJustificationComputation(
              "The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or an error in LISA.",
              wrongJudgement,
              None
            )
          )
      }
    }

    val statement: F.Sequent = () |- Iff(label.applySeq(vars), lambda.body)
    library.last = Some(this)
  }




  /**
   * Allows to make definitions "by unique existance" of a function symbol
   */
  class EpsilonDefinition[S, R](using om: OutputManager)(val fullName: String, line: Int, file: String)(
      val vars: Seq[S.Variable[?]], // Tuple.Map[S, Variable],
      val out: F.Variable[R],
      val f: F.Formula,
      j: JUSTIFICATION
  ) extends DEFINITION(line, file) {
    def funWithArgs = label.applySeq(vars)
    override def repr: String =
      s" ${if (withSorry) " Sorry" else ""} Definition of function symbol ${funWithArgs} := the ${out} such that ${(out === funWithArgs) <=> f})\n"

    // val expr = LambdaExpression[Term, Formula, N](vars, f, valueOf[N])

    lazy val label: ConstantTermLabelOfArity[N] = (if (vars.length == 0) F.Constant(name) else F.ConstantFunctionLabel[N](name, vars.length.asInstanceOf)).asInstanceOf

    val innerJustification: theory.FunctionDefinition = {
      val conclusion: F.Sequent = j.statement
      val pr: SCProof = SCProof(IndexedSeq(SC.Restate(conclusion.underlying, -1)), IndexedSeq(conclusion.underlying))
      if (!(conclusion.left.isEmpty && (conclusion.right.size == 1))) {
        om.lisaThrow(
          UserInvalidDefinitionException(
            name,
            s"The given justification is not valid for a definition" +
              s"The justification should be of the form ${(() |- F.BinderFormula(F.ExistsOne, out, F.VariableFormula("phi")))}" +
              s"instead of the given ${conclusion.underlying}"
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
        case F.BinderFormula(F.Exists, x, F.BinderFormula(F.Forall, y, F.AppliedConnector(F.Iff, Seq(l, r)))) if F.isSame(l, x === y) => r
        case F.BinderFormula(F.Exists, x, F.BinderFormula(F.Forall, y, F.AppliedConnector(F.Iff, Seq(l, r)))) if F.isSame(r, x === y) => l
        case _ =>
          om.lisaThrow(
            UserInvalidDefinitionException(
              name,
              s"The given justification is not valid for a definition" +
                s"The justification should be of the form ${(() |- F.BinderFormula(F.ExistsOne, out, F.VariableFormula("phi")))}" +
                s"instead of the given ${conclusion.underlying}"
            )
          )
      }
      val underf = f.underlying
      val uvars = vars.map(_.underlyingLabel)
      val ucst = K.ConstantFunctionLabel(name, vars.size)
      val judgement = theory.makeFunctionDefinition(pr, Seq(j.innerJustification), ucst, out.underlyingLabel, K.LambdaTermFormula(uvars, underf), proven.underlying)
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
          if (!theory.isAvailable(ucst)) {
            om.lisaThrow(UserInvalidDefinitionException(name, s"The symbol ${name} has already been defined and can't be redefined."))
          }
          if (!(underf.freeSchematicTermLabels.subsetOf(uvars.toSet + out.underlyingLabel) && underf.schematicFormulaLabels.isEmpty)) {
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"The definition is not allowed to contain schematic symbols or free variables." +
                  s"Kernel returned error: The symbols {${(underf.freeSchematicTermLabels -- uvars.toSet - out.underlyingLabel ++ underf.freeSchematicTermLabels)
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
          equality(label.applySeq(vars), out),
          f
        )
      )

    library.last = Some(this)

  }

  /**
   * Allows to make definitions "by equality" of a function symbol
   */
  class SimpleFunctionDefinition[N <: F.Arity](using om: OutputManager)(fullName: String, line: Int, file: String)(
      val lambda: LambdaExpression[Term, Term, N],
      out: F.Variable,
      j: JUSTIFICATION
  ) extends FunctionDefinition[N](fullName, line, file)(lambda.bounds.asInstanceOf, out, out === lambda.body, j) {

    private val term = label.applySeq(lambda.bounds.asInstanceOf)
    private val simpleProp = lambda.body === term
    val simplePropName = "simpleDef_" + fullName
    val simpleDef = THM(simpleProp, simplePropName, line, file, InternalStatement)({
      have(thesis) by Restate.from(this of term)
    })
    shortDefs.update(label, Some(simpleDef))

  }

  object SimpleFunctionDefinition {
    def apply[N <: F.Arity](using om: OutputManager)(fullName: String, line: Int, file: String)(lambda: LambdaExpression[Term, Term, N]): SimpleFunctionDefinition[N] = {
      val intName = "definition_" + fullName
      val out = Variable(freshId(lambda.allSchematicLabels.map(_.id), "y"))
      val defThm = THM(F.ExistsOne(out, out === lambda.body), intName, line, file, InternalStatement)({
        have(SimpleDeducedSteps.simpleFunctionDefinition(lambda, out))
      })
      new SimpleFunctionDefinition[N](fullName, line, file)(lambda, out, defThm)
    }
  }



  /////////////////////////
  //  Local Definitions  //
  /////////////////////////

  import lisa.utils.parsing.FOLPrinter.prettySCProof
  import lisa.utils.KernelHelpers.apply

  /**
   * A term with a definition, local to a proof.
   *
   * @param proof
   * @param id
   */
  abstract class LocalyDefinedVariable(val proof: library.Proof, id: Identifier) extends Variable(id) {

    val definition: proof.Fact
    lazy val definingFormula = proof.sequentOfFact(definition).right.head

    // proof.addDefinition(this, defin(this), fact)
    // val definition: proof.Fact = proof.getDefinition(this)
  }

  /**
   * A witness for a statement of the form ∃(x, P(x)) is a (fresh) variable y such that P(y) holds. This is a local definition, typically used with `val y = witness(fact)`
   * where `fact` is a fact of the form `∃(x, P(x))`. The property P(y) can then be used with y.elim
   */
  def witness(using _proof: library.Proof, line: sourcecode.Line, file: sourcecode.File, name: sourcecode.Name)(fact: _proof.Fact): LocalyDefinedVariable { val proof: _proof.type } = {

    val (els, eli) = _proof.sequentAndIntOfFact(fact)
    els.right.head match
      case Exists(x, inner) =>
        val id = freshId((els.allSchematicLabels ++ _proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id), name.value)
        val c: LocalyDefinedVariable = new LocalyDefinedVariable(_proof, id) { val definition = assume(using proof)(inner.substitute(x := this)) }
        val defin = c.definingFormula
        val definU = defin.underlying
        val exDefinU = K.Exists(c.underlyingLabel, definU)

        if els.right.size != 1 || !K.isSame(els.right.head.underlying, exDefinU) then
          throw new UserInvalidDefinitionException(c.id, "Eliminator fact for " + c + " in a definition should have a single formula, equivalent to " + exDefinU + ", on the right side.")

        _proof.addElimination(
          defin,
          (i, sequent) =>
            val resSequent = (sequent.underlying -<< definU)
            List(
              SC.LeftExists(resSequent +<< exDefinU, i, definU, c.underlyingLabel),
              SC.Cut(resSequent ++<< els.underlying, eli, i + 1, exDefinU)
            )
        )

        c.asInstanceOf[LocalyDefinedVariable { val proof: _proof.type }]

      case _ => throw new Exception("Pick is used to obtain a witness of an existential statement.")

  }

  /**
   * Check correctness of the proof, using LISA's logical kernel, to the current point.
   */
  def sanityProofCheck(using p: Proof)(message: String): Unit = {
    val csc = p.toSCProof
    if checkSCProof(csc).isValid then
      println("Proof is valid. " + message)
      Thread.sleep(100)
    else
      checkProof(csc)
      throw Exception("Proof is not valid: " + message)
  }

}
