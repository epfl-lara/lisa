package utilities

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import Helpers.{*, given}
import lisa.settheory.AxiomaticSetTheory.pair
import proven.tactics.ProofTactics.simpleFunctionDefinition

abstract class Library(val theory: RunningTheory) {
  val realOutput: String => Unit

  type Proof = SCProof
  val Proof = SCProof
  type Justification = theory.Justification
  type Theorem = theory.Theorem
  val Theorem = theory.Theorem
  type Definition = theory.Definition
  type Axiom = theory.Axiom
  val Axiom = theory.Axiom
  type PredicateDefinition = theory.PredicateDefinition
  val PredicateDefinition = theory.PredicateDefinition
  type FunctionDefinition = theory.FunctionDefinition
  val FunctionDefinition = theory.FunctionDefinition
  type Judgement[J <: Justification] = RunningTheoryJudgement[J]


  type Sequentable = Justification | Formula | Sequent

  private var last :Option[Justification] = None

  private var outString :List[String] = List()
  private val lineBreak = "\n"
  given output: (String => Unit) = s => outString = lineBreak :: s :: outString



  inline def steps(sts:SCProofStep*):IndexedSeq[SCProofStep] = sts.toIndexedSeq
  inline def imports(sqs:Sequentable*):IndexedSeq[Sequent] = sqs.map(sequantableToSequent).toIndexedSeq
  // extension (s:String) def apply():Unit = ()


  // THEOREM Syntax
  def makeTheorem(name: String, statement: String, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] =
    theory.theorem(name, statement, proof, justifications)

  case class TheoremNameWithStatement(name: String, statement: String) {
    def PROOF(proof: SCProof): TheoremNameWithProof = TheoremNameWithProof(name, statement, proof)
  }

  case class TheoremName(name: String) {

    infix def of(statement: String): TheoremNameWithStatement = TheoremNameWithStatement(name, statement)
  }

  def THEOREM(name: String): TheoremName = TheoremName(name)

  case class TheoremNameWithProof(name: String, statement: String, proof: SCProof) {
    infix def using(justifications: theory.Justification*): theory.Theorem = theory.theorem(name, statement, proof, justifications) match
      case RunningTheoryJudgement.ValidJustification(just) =>
        last = Some(just)
        just
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[_] => wrongJudgement.showAndGet(output)

    infix def using(u: Unit): theory.Theorem = using()
  }


  //DEFINITION Syntax
  def simpleDefinition(symbol:String, expression: LambdaTermTerm): RunningTheoryJudgement[theory.FunctionDefinition] =
    val LambdaTermTerm(vars, body) = expression
    val out:VariableLabel = VariableLabel(freshId((vars.map(_.id)++body.schematicFunctions.map(_.id)).toSet, "y"))
    val proof:Proof = simpleFunctionDefinition(expression, out)
    theory.functionDefinition(symbol, LambdaTermFormula(vars, out === body), out, proof, Nil)

  def complexDefinition(symbol:String, vars:Seq[SchematicFunctionLabel], v:SchematicFunctionLabel, f:Formula, proof:Proof, just:Seq[Justification]): RunningTheoryJudgement[theory.FunctionDefinition] =
    val out:VariableLabel = VariableLabel(freshId((vars.map(_.id)++f.schematicFunctions.map(_.id)).toSet, "y"))
    theory.functionDefinition(symbol, LambdaTermFormula(vars, instantiateFunctionSchemas(f, Map(v -> LambdaTermTerm(Nil, out)))), out, proof, just)

  def simpleDefinition(symbol:String, expression: LambdaTermFormula): RunningTheoryJudgement[theory.PredicateDefinition] =
    theory.predicateDefinition(symbol, expression)

  case class FunSymbolDefine(symbol:String, vars:Seq[SchematicFunctionLabel]){
    infix def as(t:Term): ConstantFunctionLabel =
      val definition = simpleDefinition(symbol, LambdaTermTerm(vars, t)) match
        case RunningTheoryJudgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: RunningTheoryJudgement.InvalidJustification[_] => wrongJudgement.showAndGet(realOutput)
      definition.label
    infix def as(f:Formula): ConstantPredicateLabel =
      val definition = simpleDefinition(symbol, LambdaTermFormula(vars, f)) match
        case RunningTheoryJudgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: RunningTheoryJudgement.InvalidJustification[_] => wrongJudgement.showAndGet(realOutput)
      definition.label

    infix def asThe(out:SchematicFunctionLabel):DefinitionNameAndOut = DefinitionNameAndOut(symbol, vars, out)
  }

  case class DefinitionNameAndOut(symbol:String, vars:Seq[SchematicFunctionLabel], out:SchematicFunctionLabel){
    infix def suchThat (f:Formula):DefinitionWaitingProof = DefinitionWaitingProof(symbol, vars, out, f)
  }

  case class DefinitionWaitingProof(symbol:String, vars:Seq[SchematicFunctionLabel], out:SchematicFunctionLabel, f:Formula ){
    infix def PROOF(proof:SCProof):DefinitionWithProof = DefinitionWithProof(symbol, vars, out, f, proof)
  }

  case class DefinitionWithProof(symbol:String, vars:Seq[SchematicFunctionLabel], out:SchematicFunctionLabel, f:Formula, proof:Proof){
    infix def using(justifications: theory.Justification*): ConstantFunctionLabel =
      val definition = complexDefinition(symbol, vars, out, f, proof, justifications) match
        case RunningTheoryJudgement.ValidJustification(just) =>
          last = Some(just)
          just
        case wrongJudgement: RunningTheoryJudgement.InvalidJustification[_] => wrongJudgement.showAndGet(realOutput)
      definition.label

    infix def using(u: Unit): ConstantFunctionLabel = using()
  }

  //DEFINE("+", sx, sy) asThe v suchThat ... PROOF {...} using ()

  def DEFINE(symbol:String, vars:SchematicFunctionLabel*): FunSymbolDefine = FunSymbolDefine(symbol, vars)

  def simpleFunctionDefinition(expression:LambdaTermTerm, out:VariableLabel): SCProof = {
    val x = out
    val LambdaTermTerm(vars, body) = expression
    val xeb = x===body
    val y = VariableLabel(freshId(body.freeVariables.map(_.id)++vars.map(_.id)+out.id, "y"))
    val s0 = RightRefl(() |- body === body, body === body)
    val s1 = Rewrite(() |- (xeb) <=> (xeb), 0)
    val s2 = RightForall(() |- forall(x, (xeb) <=> (xeb)), 1, (xeb) <=> (xeb), x)
    val s3 = RightExists(() |- exists(y, forall(x, (x === y) <=> (xeb))), 2, forall(x, (x === y) <=> (xeb)), y, body)
    val s4 = Rewrite(() |- existsOne(x, xeb), 3)
    val v = Vector(s0, s1, s2, s3, s4)
    SCProof(v)
  }

  given Conversion[TheoremNameWithProof, theory.Theorem] = _.using()

  implicit class StringToJust(val sc: StringContext) {

    def thm(args: Any*): theory.Theorem = getTheorem(sc.parts.mkString(""))

    def ax(args: Any*): theory.Axiom = getAxiom(sc.parts.mkString(""))

    def defi(args: Any*): theory.Definition = getDefinition(sc.parts.mkString(""))
  }

  def getTheorem(name: String): theory.Theorem =
    theory.getTheorem(name) match
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No theorem with name \"$name\" was found.")

  def getAxiom(name: String): theory.Axiom =
    theory.getAxiom(name) match
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No axiom with name \"$name\" was found.")

  def getDefinition(name: String): theory.Definition =
    theory.getDefinition(name) match
      case Some(value) => value
      case None => throw java.util.NoSuchElementException(s"No definition for symbol \"$name\" was found.")

  def show: Justification = last match
    case Some(value) => value.show
    case None => throw new NoSuchElementException("There is nothing to show: No theorem or definition has been proved yet.")
  //given Conversion[String, theory.Justification] = name => theory.getJustification(name).get

  private def sequantableToSequent(s:Sequentable): Sequent= s match
    case j:Justification => theory.sequentFromJustification(j)
    case f:Formula => () |- f
    case s:Sequent => s

  given Conversion[Sequentable, Sequent] = sequantableToSequent
  given Conversion[theory.Axiom, Formula] = theory.sequentFromJustification(_).right.head
  given Conversion[Formula, Axiom] = (f:Formula) => theory.getAxiom(f).get
  given convJustSequent[C <: Iterable[Sequentable], D](using bf: scala.collection.BuildFrom[C, Sequent, D]) : Conversion[C, D] = cc => {
    val builder = bf.newBuilder(cc)
    cc.foreach(builder += sequantableToSequent(_))
    builder.result
  }

  given convStrInt[C <: Iterable[String], D](using bf: scala.collection.BuildFrom[C, Int, D]) : Conversion[C, D] = cc => {
    val builder = bf.newBuilder(cc)
    cc.foreach(builder += _.size)
    builder.result
  }

  def main(args: Array[String]): Unit = { realOutput(outString.reverse.mkString("")) }

}
