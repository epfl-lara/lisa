package lisa.hol
import lisa.hol.VarsAndFunctions
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

trait HOLTestMain extends AnyFunSuite with lisa.HOL {
  this: AnyFunSuite =>
  override val om: OutputManager = new OutputManager {
    def finishOutput(exception: Exception): Nothing = {
      log(exception)
      main(Array[String]())
      throw exception
    }
    val stringWriter: java.io.StringWriter = new java.io.StringWriter()
  }

  override def HOLTheorem(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: Sequent)(computeProof: Proof ?=> Unit): THM =

    val f = file.value.split("/").last.split("\\\\").last
    test(s"Test theorem ${name.value.split("\\.").last} at ${f}:${line.value}") {
      super.HOLTheorem(using om, name, line, file)(statement)(computeProof)
    }
    super.HOLTheorem(using om, name, line, file)(statement)(sorry)

  def TypingTheorem(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: Expr[Prop]): THM =

    val f = file.value.split("/").last.split("\\\\").last
    test(s"Test type-checking theorem of ${name.value.split("\\.").last} at ${f}:${line.value}") {
      VarsAndFunctions.TypingTheorem(using om, name)(statement)
    }
    Theorem(using om, name)(statement) { sorry }
}
