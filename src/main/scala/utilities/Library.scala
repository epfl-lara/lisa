package utilities

import lisa.kernel.proof.RunningTheory

/**
 * A class abstracting a [[lisa.kernel.proof.RunningTheory]] providing utility functions and a convenient syntax
 * to write and use Theorems and Definitions.
 * @param theory The inner RunningTheory
 */
abstract class Library(val theory: RunningTheory) {
  given RunningTheory = theory
  export lisa.kernel.fol.FOL.*
  export lisa.kernel.proof.SequentCalculus.*
  export lisa.kernel.proof.SCProof as Proof
  export theory.{Justification, Theorem, Definition, Axiom, PredicateDefinition, FunctionDefinition}
  export Helpers.{*, given}
  import lisa.kernel.proof.RunningTheoryJudgement as Judgement

  /**
   * a type representing different types that have a natural representation as Sequent
   */
  type Sequentable = Justification | Formula | Sequent

  private var last: Option[Justification] = None

  /**
   * A function intended for use to construct a proof:
   * <pre> Proof(steps(...), imports(...))</pre>
   * Must contains [[SCProofStep]]'s
   */
  inline def steps(sts: SCProofStep*): IndexedSeq[SCProofStep] = sts.toIndexedSeq

  /**
   * A function intended for use to construct a proof:
   * <pre> Proof(steps(...), imports(...))</pre>
   * Must contains [[Justification]]'s, [[Formula]]'s or [[Sequent]], all of which are converted adequatly automatically.
   */
  inline def imports(sqs: Sequentable*): IndexedSeq[Sequent] = sqs.map(sequantableToSequent).toIndexedSeq

  // THEOREM Syntax

  /**
   * An alias to create a Theorem
   */
  def makeTheorem(name: String, statement: String, proof: Proof, justifications: Seq[theory.Justification]): Judgement[theory.Theorem] =
    theory.theorem(name, statement, proof, justifications)

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  case class TheoremNameWithStatement(name: String, statement: String) {

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    def PROOF(proof: Proof)(using String => Unit): TheoremNameWithProof = TheoremNameWithProof(name, statement, proof)

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    def PROOF(steps: IndexedSeq[SCProofStep])(using String => Unit): TheoremNameWithProof = TheoremNameWithProof(name, statement, Proof(steps))
  }

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  case class TheoremName(name: String) {

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    infix def of(statement: String): TheoremNameWithStatement = TheoremNameWithStatement(name, statement)
  }

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  def THEOREM(name: String): TheoremName = TheoremName(name)

  /**
   * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
   */
  case class TheoremNameWithProof(name: String, statement: String, proof: Proof)(using String => Unit) {
    infix def using(justifications: theory.Justification*): theory.Theorem = theory.theorem(name, statement, proof, justifications) match
      case Judgement.ValidJustification(just) =>
        last = Some(just)
        just
      case wrongJudgement: Judgement.InvalidJustification[_] => wrongJudgement.showAndGet

    /**
     * Syntax: <pre> THEOREM("name") of "the sequent concluding the proof" PROOF { the proof } using (assumptions) </pre>
     */
    infix def using(u: Unit): theory.Theorem = using()
  }

  // DEFINITION Syntax

  /**
   * Allows to create a definition by shortcut of a function symbol:
   */
  def simpleDefinition(symbol: String, expression: LambdaTermTerm): Judgement[theory.FunctionDefinition] =
    val LambdaTermTerm(vars, body) = expression
    val out: VariableLabel = VariableLabel(freshId((vars.map(_.id) ++ body.schematicFunctions.map(_.id)).toSet, "y"))
    val proof: Proof = simpleFunctionDefinition(expression, out)
    theory.functionDefinition(symbol, LambdaTermFormula(vars, out === body), out, proof, Nil)

  /**
   * Allows to create a definition by existential uniqueness of a function symbol:
   */
  def complexDefinition(symbol: String, vars: Seq[SchematicFunctionLabel], v: SchematicFunctionLabel, f: Formula, proof: Proof, just: Seq[Justification]): Judgement[theory.FunctionDefinition] =
    val out: VariableLabel = VariableLabel(freshId((vars.map(_.id) ++ f.schematicFunctions.map(_.id)).toSet, "y"))
    theory.functionDefinition(symbol, LambdaTermFormula(vars, instantiateFunctionSchemas(f, Map(v -> LambdaTermTerm(Nil, out)))), out, proof, just)

  /**
   * Allows to create a definition by shortcut of a function symbol:
   */
  def simpleDefinition(symbol: String, expression: LambdaTermFormula): Judgement[theory.PredicateDefinition] =
    theory.predicateDefinition(symbol, expression)

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) as "definition" </pre>
   * or
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class FunSymbolDefine(symbol: String, vars: Seq[SchematicFunctionLabel]) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) as "definition" </pre>
     */
    infix def as(t: Term)(using String => Unit): ConstantFunctionLabel =
      val definition = simpleDefinition(symbol, LambdaTermTerm(vars, t)) match
        case Judgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: Judgement.InvalidJustification[_] => wrongJudgement.showAndGet
      definition.label

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) as "definition" </pre>
     */
    infix def as(f: Formula)(using String => Unit): ConstantPredicateLabel =
      val definition = simpleDefinition(symbol, LambdaTermFormula(vars, f)) match
        case Judgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: Judgement.InvalidJustification[_] => wrongJudgement.showAndGet
      definition.label

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def asThe(out: SchematicFunctionLabel): DefinitionNameAndOut = DefinitionNameAndOut(symbol, vars, out)
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class DefinitionNameAndOut(symbol: String, vars: Seq[SchematicFunctionLabel], out: SchematicFunctionLabel) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def suchThat(f: Formula): DefinitionWaitingProof = DefinitionWaitingProof(symbol, vars, out, f)
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class DefinitionWaitingProof(symbol: String, vars: Seq[SchematicFunctionLabel], out: SchematicFunctionLabel, f: Formula) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def PROOF(proof: Proof): DefinitionWithProof = DefinitionWithProof(symbol, vars, out, f, proof)
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  case class DefinitionWithProof(symbol: String, vars: Seq[SchematicFunctionLabel], out: SchematicFunctionLabel, f: Formula, proof: Proof) {

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def using(justifications: theory.Justification*)(using String => Unit): ConstantFunctionLabel =
      val definition = complexDefinition(symbol, vars, out, f, proof, justifications) match
        case Judgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: Judgement.InvalidJustification[_] => wrongJudgement.showAndGet
      definition.label

    /**
     * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
     */
    infix def using(u: Unit)(using String => Unit): ConstantFunctionLabel = using()
  }

  /**
   * Syntax: <pre> DEFINE("symbol", arguments) asThe x suchThat P(x) PROOF { the proof } using (assumptions) </pre>
   */
  def DEFINE(symbol: String, vars: SchematicFunctionLabel*): FunSymbolDefine = FunSymbolDefine(symbol, vars)

  /**
   * For a definition of the type f(x) := term, construct the required proof ∃!y. y = term.
   */
  private def simpleFunctionDefinition(expression: LambdaTermTerm, out: VariableLabel): Proof = {
    val x = out
    val LambdaTermTerm(vars, body) = expression
    val xeb = x === body
    val y = VariableLabel(freshId(body.freeVariables.map(_.id) ++ vars.map(_.id) + out.id, "y"))
    val s0 = RightRefl(() |- body === body, body === body)
    val s1 = Rewrite(() |- (xeb) <=> (xeb), 0)
    val s2 = RightForall(() |- forall(x, (xeb) <=> (xeb)), 1, (xeb) <=> (xeb), x)
    val s3 = RightExists(() |- exists(y, forall(x, (x === y) <=> (xeb))), 2, forall(x, (x === y) <=> (xeb)), y, body)
    val s4 = Rewrite(() |- existsOne(x, xeb), 3)
    val v = Vector(s0, s1, s2, s3, s4)
    Proof(v)
  }

  // Implicit conversions

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
    theory.getTheorem(name) match
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No theorem with name \"$name\" was found.")

  /**
   * Fetch an Axiom by its name.
   */
  def getAxiom(name: String): theory.Axiom =
    theory.getAxiom(name) match
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No axiom with name \"$name\" was found.")

  /**
   * Fetch a Definition by its symbol.
   */
  def getDefinition(name: String): theory.Definition =
    theory.getDefinition(name) match
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No definition for symbol \"$name\" was found.")

  /**
   * Prints a short representation of the last theorem or definition introduced
   */
  def show(using String => Unit): Justification = last match
    case Some(value) => value.show
    case None => throw new NoSuchElementException("There is nothing to show: No theorem or definition has been proved yet.")
  // given Conversion[String, theory.Justification] = name => theory.getJustification(name).get

  /**
   * Converts different class that have a natural interpretation as a Sequent
   */
  private def sequantableToSequent(s: Sequentable): Sequent = s match
    case j: Justification => theory.sequentFromJustification(j)
    case f: Formula => () |- f
    case s: Sequent => s

  given Conversion[Sequentable, Sequent] = sequantableToSequent
  given Conversion[Axiom, Formula] = theory.sequentFromJustification(_).right.head
  given Conversion[Formula, Axiom] = (f: Formula) => theory.getAxiom(f).get
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
