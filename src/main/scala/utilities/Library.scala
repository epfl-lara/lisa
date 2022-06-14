package utilities

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.SCProof

import Helpers.{given, *}

abstract class Library(val theory: RunningTheory) {
  val output: String => Unit
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

  type Proof = SCProof
  val Proof = SCProof
  Proof.apply()

  // extension (s:String) def apply():Unit = ()

  def makeTheorem(name: String, statement: String, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] =
    theory.theorem(name, statement, proof, justifications)

  case class TheoremNameWithStatement(name: String, statement: String) {
    def PROOF(proof: SCProof): TheoremNameWithProof = TheoremNameWithProof(name, statement, proof)
  }

  case class TheoremName(name: String) {
    def of(statement: String): TheoremNameWithStatement = TheoremNameWithStatement(name, statement)
  }

  def THEOREM(name: String): TheoremName = TheoremName(name)

  case class TheoremNameWithProof(name: String, statement: String, proof: SCProof) {
    def using(justifications: theory.Justification*): theory.Theorem = theory.theorem(name, statement, proof, justifications) match
      case RunningTheoryJudgement.ValidJustification(just) => just
      case wrongJudgement: RunningTheoryJudgement.InvalidJustification[_] => wrongJudgement.showAndGet(output)

    def using(u: Unit): theory.Theorem = using()
  }

  given Conversion[TheoremNameWithProof, theory.Theorem] = _.using()

  implicit class JsonHelper(val sc: StringContext) {

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

  given Conversion[String, theory.Justification] = name => theory.getJustification(name).get

  def main(args: Array[String]): Unit = { println("bonjour") }
  /*
    val a:String = "a"
    val b:String = "b"
    val c:String = "c"
    val d:String = "d"
    val e:String = "e"
    val f:String = "f"
    val g:String = "g"
    val h:String = "h"
    val i:String = "i"
    val j:String = "j"
    val k:String = "k"
    val l:String = "l"
    val m:String = "m"
    val n:String = "n"
    val o:String = "o"
    val p:String = "p"
    val q:String = "q"
    val r:String = "r"
    val s:String = "s"
    val t:String = "t"
    val u:String = "u"
    val v:String = "v"
    val w:String = "w"
    val x:String = "x"
    val y:String = "y"
    val z:String = "z"

    case class SchematicFLabel(s:String){
        def apply(ts:Term*): FunctionTerm = FunctionTerm(SchematicFunctionLabel(s, ts.length), ts)
        def apply(n:Int): SchematicFunctionLabel = SchematicFunctionLabel(s, n)
    }

    case class SchematicPLabel(s:String){
        def apply(fs:Term*): PredicateFormula = PredicateFormula(SchematicPredicateLabel(s, fs.length), fs)
        def apply(n:Int): SchematicPredicateLabel = SchematicPredicateLabel(s, n)
    }

    def ?(s:String) = SchematicFLabel(s)
    def &(s:String) = SchematicPLabel(s)

    given Conversion[String, VariableLabel] = VariableLabel(_)
    given Conversion[String, VariableTerm] = s => VariableTerm(VariableLabel(s))

   */
}
