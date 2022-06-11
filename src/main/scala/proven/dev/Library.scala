package proven.dev

import lisa.kernel.fol.FOL
import lisa.kernel.proof.*
import utilities.TheoriesHelpers.{*, given}
import utilities.KernelHelpers.{*, given}
import lisa.kernel.fol.FOL.*

trait Library {
    implicit val theory:RunningTheory

    def theorem(name: String, statement:String, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] = theory.theorem(name, statement, proof, justifications)

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

    //given Conversion[FunctionTerm, FunctionLabel] = _.label

    def ?(s:String) = SchematicFLabel(s)
    def &(s:String) = SchematicPLabel(s)

    given Conversion[String, VariableLabel] = VariableLabel(_)
    given Conversion[String, VariableTerm] = s => VariableTerm(VariableLabel(s))

    ?("x")
}
