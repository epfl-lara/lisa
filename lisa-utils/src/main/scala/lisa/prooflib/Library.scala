package lisa.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SequentCalculus
import lisa.prooflib.ProofTacticLib.ProofTactic

import scala.collection.mutable.Stack as stack

/**
 * A class abstracting a [[lisa.kernel.proof.RunningTheory]] providing utility functions and a convenient syntax
 * to write and use Theorems and Definitions.
 * @param theory The inner RunningTheory
 */
abstract class Library extends lisa.prooflib.WithTheorems with lisa.prooflib.ProofsHelpers {
  val theory: RunningTheory
  given library: this.type = this
  given RunningTheory = theory
  export lisa.kernel.fol.FOL.{Formula, *}
  val SC: SequentCalculus.type = lisa.kernel.proof.SequentCalculus
  export lisa.kernel.proof.SequentCalculus.{Sequent, SCProofStep}
  export lisa.kernel.proof.SCProof
  export lisa.prooflib.TheoriesHelpers.{_, given}
  import lisa.kernel.proof.RunningTheoryJudgement as Judgement

  /**
   * a type representing different types that have a natural representation as Sequent
   */
  type Sequentable = theory.Justification | Formula | Sequent

  var last: Option[theory.Justification] = None

  /**
   * A function intended for use to construct a proof:
   * <pre> SCProof(steps(...), imports(...))</pre>
   * Must contains [[SCProofStep]]'s
   */
  inline def steps(sts: SCProofStep*): IndexedSeq[SCProofStep] = sts.toIndexedSeq

  /**
   * A function intended for use to construct a proof:
   * <pre> SCProof(steps(...), imports(...))</pre>
   * Must contains [[Justification]]'s, [[Formula]]'s or [[Sequent]], all of which are converted adequatly automatically.
   */
  inline def imports(sqs: Sequentable*): IndexedSeq[Sequent] = sqs.map(sequantableToSequent).toIndexedSeq

  // THEOREM Syntax

  /**
   * An alias to create a Theorem
   */
  def makeTheorem(name: String, statement: Sequent, proof: SCProof, justifications: Seq[theory.Justification]): Judgement[theory.Theorem] =
    theory.theorem(name, statement, proof, justifications)

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  case class TheoremNameWithStatement(name: String, statement: Sequent) {

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    def PROOF2(proof: SCProof)(using om: OutputManager): TheoremNameWithProof = TheoremNameWithProof(name, statement, proof)

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    def PROOF2(steps: IndexedSeq[SCProofStep])(using om: OutputManager): TheoremNameWithProof =
      TheoremNameWithProof(name, statement, SCProof(steps))

  }

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  case class TheoremName(name: String) {

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    infix def of(statement: Sequent): TheoremNameWithStatement = TheoremNameWithStatement(name, statement)
    infix def of(statement: String): TheoremNameWithStatement = TheoremNameWithStatement(name, lisa.utils.FOLParser.parseSequent(statement))
  }

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  def THEOREM(name: String): TheoremName = TheoremName(name)

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  case class TheoremNameWithProof(name: String, statement: Sequent, proof: SCProof)(using om: OutputManager) {
    infix def using(justifications: theory.Justification*): theory.Theorem = theory.theorem(name, statement, proof, justifications) match {
      case Judgement.ValidJustification(just) =>
        last = Some(just)
        just
      case wrongJudgement: Judgement.InvalidJustification[?] => wrongJudgement.showAndGet
    }

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    infix def using(u: Unit): theory.Theorem = using()
  }

  // DEFINITION Syntax

  /**
   * Allows to create a definition by shortcut of a function symbol:
   */
  def simpleDefinition(symbol: String, expression: LambdaTermTerm): Judgement[theory.FunctionDefinition] = {
    val LambdaTermTerm(vars, body) = expression

    val out: VariableLabel = VariableLabel(freshId((vars.map(_.id) ++ body.schematicTermLabels.map(_.id)).toSet, "y"))
    val proof: SCProof = simpleFunctionDefinition(expression, out)
    theory.functionDefinition(symbol, LambdaTermFormula(vars, out === body), out, proof, out === body, Nil)
  }

  /**
   * Allows to create a definition by shortcut of a predicate symbol:
   */
  def simpleDefinition(symbol: String, expression: LambdaTermFormula): Judgement[theory.PredicateDefinition] =
    theory.predicateDefinition(symbol, expression)

  /*


  /**
   * Syntax: <pre> DEFINE("symbol", arguments) as "definition" </pre>
   * or
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class FunSymbolDefine(symbol: String, vars: Seq[VariableLabel]) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) as "definition" </pre>
     */
    infix def as(t: Term)(using om: OutputManager): ConstantFunctionLabel = {
      val definition = simpleDefinition(symbol, LambdaTermTerm(vars, t)) match {
        case Judgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: Judgement.InvalidJustification[?] => wrongJudgement.showAndGet
      }
      definition.label
    }

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) as "definition" </pre>
     */
    infix def as(f: Formula)(using om: OutputManager): ConstantPredicateLabel = {
      val definition = simpleDefinition(symbol, LambdaTermFormula(vars, f)) match {
        case Judgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: Judgement.InvalidJustification[?] => wrongJudgement.showAndGet
      }
      definition.label
    }

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def asThe(out: VariableLabel): DefinitionNameAndOut = DefinitionNameAndOut(symbol, vars, out)
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class DefinitionNameAndOut(symbol: String, vars: Seq[VariableLabel], out: VariableLabel) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def suchThat(f: Formula): DefinitionWaitingProof = DefinitionWaitingProof(symbol, vars, out, f)
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class DefinitionWaitingProof(symbol: String, vars: Seq[VariableLabel], out: VariableLabel, f: Formula) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def PROOF(proof: SCProof): DefinitionWithProof = DefinitionWithProof(symbol, vars, out, f, proof)
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class DefinitionWithProof(symbol: String, vars: Seq[VariableLabel], out: VariableLabel, f: Formula, proof: SCProof) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def using(justifications: theory.Justification*)(using om: OutputManager): ConstantFunctionLabel = {
      val definition = complexDefinition(symbol, vars, out, f, proof, justifications) match {
        case Judgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: Judgement.InvalidJustification[?] => wrongJudgement.showAndGet
      }
      definition.label
    }

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def using(u: Unit)(using om: OutputManager): ConstantFunctionLabel = using()
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  def DEFINE(symbol: String, vars: VariableLabel*): FunSymbolDefine = FunSymbolDefine(symbol, vars)
   */
  /**
   * For a definition of the type f(x) := term, construct the required proof ?!y. y = term.
   */
  private def simpleFunctionDefinition(expression: LambdaTermTerm, out: VariableLabel): SCProof = {
    val x = out
    val LambdaTermTerm(vars, body) = expression
    val xeb = x === body
    val y = VariableLabel(freshId(body.freeVariables.map(_.id) ++ vars.map(_.id) + out.id, "y"))
    val s0 = SC.RightRefl(() |- body === body, body === body)
    val s1 = SC.Restate(() |- (xeb) <=> (xeb), 0)
    val s2 = SC.RightForall(() |- forall(x, (xeb) <=> (xeb)), 1, (xeb) <=> (xeb), x)
    val s3 = SC.RightExists(() |- exists(y, forall(x, (x === y) <=> (xeb))), 2, forall(x, (x === y) <=> (xeb)), y, body)
    val s4 = SC.Restate(() |- existsOne(x, xeb), 3)
    val v = Vector(s0, s1, s2, s3, s4)
    SCProof(v)
  }

  //////////////////////////////////////////
  //      Tools for proof development     //
  //////////////////////////////////////////

  given Conversion[TheoremNameWithProof, theory.Theorem] = _.using()

  /**
   * Allows to fetch a Justification (Axiom, Theorem or Definition) by it's name or symbol:
   * <pre>thm"fundamentalTheoremOfAlgebra", ax"comprehensionAxiom", defi"+"
   */
  implicit class StringToJust(val sc: StringContext) {

    def thm(args: Any*): theory.Theorem = getTheorem(sc.parts.mkString(""))

    def ax(args: Any*): theory.Axiom = getAxiom(sc.parts.mkString(""))

    def defi(args: Any*): theory.Definition = getDefinition(sc.parts.mkString(""))
  }

  /**
   * Fetch a Theorem by its name.
   */
  def getTheorem(name: String): theory.Theorem =
    theory.getTheorem(name) match {
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No theorem with name \"$name\" was found.")
    }

  /**
   * Fetch an Axiom by its name.
   */
  def getAxiom(name: String): theory.Axiom =
    theory.getAxiom(name) match {
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No axiom with name \"$name\" was found.")
    }

  /**
   * Fetch a Definition by its symbol.
   */
  def getDefinition(name: String): theory.Definition =
    theory.getDefinition(name) match {
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No definition for symbol \"$name\" was found.")
    }

  /**
   * Prints a short representation of the last theorem or definition introduced
   */
  def show(using om: OutputManager): theory.Justification = last match {
    case Some(value) => value.show
    case None => throw new NoSuchElementException("There is nothing to show: No theorem or definition has been proved yet.")
  }

  /**
   * Converts different class that have a natural interpretation as a Sequent
   */
  private def sequantableToSequent(s: Sequentable): Sequent = s match {
    case j: theory.Justification => theory.sequentFromJustification(j)
    case f: Formula => () |- f
    case s: Sequent => s
  }

  given convJustSequent[C <: Iterable[Sequentable], D](using bf: scala.collection.BuildFrom[C, Sequent, D]): Conversion[C, D] = cc => {
    val builder = bf.newBuilder(cc)
    cc.foreach(builder += sequantableToSequent(_))
    builder.result
  }

  given convStrInt[C <: Iterable[String], D](using bf: scala.collection.BuildFrom[C, Int, D]): Conversion[C, D] = cc => {
    val builder = bf.newBuilder(cc)
    cc.foreach(builder += _.size)
    builder.result
  }

}
