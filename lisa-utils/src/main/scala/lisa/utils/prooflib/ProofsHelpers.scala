package lisa.utils.prooflib

import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.utils.K.Identifier
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._
import lisa.utils.prooflib._
import lisa.utils.{_, given}

import scala.annotation.targetName

trait ProofsHelpers {
  library: Library & WithTheorems =>

  import lisa.utils.fol.FOL.{given, *}

  class HaveSequent(val bot: Sequent) {

    inline infix def by(using proof: library.Proof, line: sourcecode.Line, file: sourcecode.File): By { val _proof: proof.type } = By(proof, line, file).asInstanceOf

    class By(val _proof: library.Proof, line: sourcecode.Line, file: sourcecode.File) {

      val bot = HaveSequent.this.bot ++ (F.toFormulaSet(_proof.getAssumptions) |- ())
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
  def assume(using proof: library.Proof)(f: Expr[Prop]): proof.ProofStep = {
    proof.addAssumption(f)
    have(() |- f) by BasicStepTactic.Hypothesis
  }
   */
  /**
   * Assume the given formulas in all future left hand-side of claimed sequents.
   */
  def assume(using proof: library.Proof)(fs: Expr[Prop]*): proof.ProofStep = {
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
    infix def of(insts: (F.SubstPair | F.Expr[F.Ind])*): proof.InstantiatedFact = {
      proof.InstantiatedFact(fact, insts)
    }
    def statement: F.Sequent = proof.sequentOfFact(fact)
  }

  def currentProof(using p: library.Proof): Library#Proof = p

  ////////////////////////////////////////
  //  DSL for definitions and theorems  //
  ////////////////////////////////////////

  class UserInvalidDefinitionException(val symbol: String, errorMessage: String)(line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(errorMessage) { // TODO refine
    val showError: String = {
      val source = scala.io.Source.fromFile(file.value)
      val textline = source.getLines().drop(line.value - 1).next().dropWhile(c => c.isWhitespace)
      source.close()
      s"   Definition of $symbol at.(${file.value.split("/").last.split("\\\\").last}:${line.value}) is invalid:\n" +
        "   " + Console.RED + textline + Console.RESET + "\n\n" +
        "   " + errorMessage
    }
  }

  def leadingVarsAndBody(e: Expr[?]): (Seq[Variable[?]], Expr[?]) =
    def inner(e: Expr[?]): (Seq[Variable[?]], Expr[?]) = e match
      case Abs(v, body) =>
        val (vars, bodyR) = inner(body)
        (v +: vars, bodyR)
      case _ => (Seq(), e)
    val r = inner(e)
    (r._1, r._2)

  // NOTE: only the top level functions here should use sourcecode implicits!!

  def DEF[S: Sort](using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(e: Expr[S]): Constant[S] =
    val (vars, body) = leadingVarsAndBody(e)
    if vars.size == e.sort.depth then DirectDefinition[S](name.value, line, file)(e, vars).cst
    else
      val maxV: Int = vars.map(_.id.no).maxOption.getOrElse(0)
      val maxB: Int = body.freeVars.map(_.id.no).maxOption.getOrElse(0)
      var no = List(maxV, maxB).max
      val newvars = K.flatTypeParameters(body.sort).map(i => { no += 1; Variable.unsafe(K.Identifier("x", no), i) })
      val totvars = vars ++ newvars
      DirectDefinition[S](name.value, line, file)(e, totvars)(using F.unsafeSortEvidence(e.sort)).cst

  def EpsilonDEF[S: Sort](using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(e: Expr[S], j: JUSTIFICATION): Constant[S] =
    val (vars, body) = leadingVarsAndBody(e)
    if vars.size == e.sort.depth then
      body match
        case epsilon(x, inner) =>
          EpsilonDefinition[S](name, line, file)(e, vars, j).cst
        case _ => om.lisaThrow(UserInvalidDefinitionException(name.value, "The given expression is not an epsilon term.")(line, file))
    else om.lisaThrow(UserInvalidDefinitionException(name.value, "The given expression is not an epsilon term.")(line, file))

  class DirectDefinition[S: Sort](using om: OutputManager)(val fullName: String, line: sourcecode.Line, file: sourcecode.File)(val expr: Expr[S], val vars: Seq[Variable[?]])
      extends DEFINITION(line, file) {

    val arity = vars.size

    lazy val cst: Constant[S] = F.Constant(name)

    val appliedCst: Expr[?] = cst #@@ (vars)

    val innerJustification: theory.Definition = {
      import lisa.utils.K.{findUndefinedSymbols}
      val uexpr = expr.underlying
      val ucst = K.Constant(name, cst.sort)
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
              )(line, file)
            )
          }
          if !theory.isAvailable(ucst) then om.lisaThrow(UserInvalidDefinitionException(name, s"The symbol ${name} has already been defined and can't be redefined.")(line, file))
          if !uexpr.freeVariables.nonEmpty then
            om.lisaThrow(
              UserInvalidDefinitionException(
                name,
                s"The definition is not allowed to contain schematic symbols or free variables. " +
                  s"The variables {${(uexpr.freeVariables).mkString(", ")}} are free in the expression ${uexpr}."
              )(line, file)
            )
          if !theory.isAvailable(ucst) then om.lisaThrow(UserInvalidDefinitionException(name, s"The symbol ${name} has already been defined and can't be redefined.")(line, file))
          om.lisaThrow(
            LisaException.InvalidKernelJustificationComputation(
              "The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or an error in LISA.",
              wrongJudgement,
              None
            )
          )
      }
    }
    val right = expr #@@ (vars)
    val statement =
      if appliedCst.sort == K.Ind then () |- (equality #@ appliedCst #@ right).asInstanceOf[Expr[Prop]]
      else () |- (iff #@ appliedCst #@ right).asInstanceOf[Expr[Prop]]
    library.last = Some(this)

    override def repr: String =
      s" ${if (withSorry) " Sorry" else ""} Definition of ${appliedCst} := ${dropAllLambdas(expr)}"

    om.output(OutputManager.MAGENTA(repr))

  }

  def dropAllLambdas(s: Expr[?]): Expr[?] = s match {
    case Abs(v, body) => dropAllLambdas(body)
    case _ => s
  }

  /**
   * For a list of sequence of variables x, y, z, creates the term with lambdas:
   * λx.(λy.(λz. base))
   */
  def abstractVars(v: Seq[Variable[?]], body: Expr[?]): Expr[?] =
    def inner(v: Seq[Variable[?]], body: Expr[?]) = v match
      case Seq() => body
      case x +: xs => Abs.unsafe(x, abstractVars(xs, body))
    inner(v.reverse, body)

  /**
   * For a list of sequence of variables x, y, z, creates the term with lambdas:
   * λx.(λy.(λz. base))
   */
  def applyVars(v: Seq[Variable[?]], body: Expr[?]): Expr[?] = v match
    case Seq() => body
    case x +: xs => applyVars(xs, body #@ (x))

  /**
   * For a list of sequence of variables x, y, z, creates the term with lambdas:
   * ((((λx.(λy.(λz. base))) x) y) z)
   */
  def betaExpand(base: Expr[?], vars: Seq[Variable[?]]): Expr[?] =
    applyVars(vars, abstractVars(vars.reverse, base))

  /**
   * Allows to make definitions "by existance" of a symbol. May need debugging
   */
  class EpsilonDefinition[S: Sort](using om: OutputManager)(fullName: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(
      expr: Expr[S],
      vars: Seq[Variable[?]],
      val j: JUSTIFICATION
  ) extends DirectDefinition(fullName.value, line, file)(expr, vars) {

    val body: Expr[Ind] = dropAllLambdas(expr).asInstanceOf
    override val appliedCst: Expr[Ind] = (cst #@@ (vars)).asInstanceOf
    val (epsilonVar, inner) = body match
      case epsilon(x, inner) => (x, inner)
      case _ => om.lisaThrow(UserInvalidDefinitionException(name, "The given expression is not an epsilon term.")(line, file))

    private val propCst = inner.substitute(epsilonVar := appliedCst)
    private val propEpsilon = inner.substitute(epsilonVar := body)
    val definingProp = Theorem(propCst) {
      val fresh = freshId(vars, "x")
      have(this)

      def loop(expr: Expr[?], leading: List[Variable[?]]): Unit =
        expr match {
          case App(lam @ Abs(vAbs, body1: Expr[Ind]), _) =>
            val freshX = Variable.unsafe(fresh, body1.sort)
            val right: Expr[Ind] = applyVars(leading.reverse, freshX).asInstanceOf[Expr[Ind]]
            var instRight: Expr[Ind] = applyVars(leading.reverse, body1).asInstanceOf[Expr[Ind]]
            thenHave(appliedCst === instRight) by Beta
          case App(f, a: Variable[?]) => loop(expr, a :: leading)
          case _ => throw new Exception("Unreachable")
        }
      while lastStep.bot.right.head match { case App(epsilon, _) => false; case _ => true } do loop(lastStep.bot.right.head, List())
      val eqStep = lastStep // appliedCst === body
      // j is exists(x, prop(x))
      val existsStep = ??? // have(propEpsilon) by // prop(body)
      val s3 = have(appliedCst === body |- propCst) by RightSubstEq.withParameters(List((appliedCst, body)), (List(epsilonVar), inner))(lastStep)
      val s4 = have(propCst) by Cut(s3, j)
      ???
    }

    override def repr: String =
      s" ${if (withSorry) " Sorry" else ""} Definition of symbol ${appliedCst} such that ${definingProp.statement})"

    om.output(OutputManager.MAGENTA(repr))
  }

  /////////////////////////
  //  Local Definitions  //
  /////////////////////////

  import lisa.utils.K.prettySCProof
  import lisa.utils.KernelHelpers.apply

  /**
   * A term with a definition, local to a proof.
   *
   * @param proof
   * @param id
   */
  abstract class LocalyDefinedVariable[S: Sort](val proof: library.Proof, id: Identifier) extends Variable(id) {

    val definition: proof.Fact
    lazy val definingFormula = proof.sequentOfFact(definition).right.head

    // proof.addDefinition(this, defin(this), fact)
    // val definition: proof.Fact = proof.getDefinition(this)
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
