package lisa.proven.mathematics

import lisa.utils.Helpers.{given, *}
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory

object Peano {
  type Axiom = Formula
  final val (x, y) =
    (VariableLabel("x"), VariableLabel("y"))

  final val zero: Term = ConstantFunctionLabel("0", 0)()
  final val s = ConstantFunctionLabel("S", 1)
  final val plus = ConstantFunctionLabel("+", 2)
  final val times = ConstantFunctionLabel("*", 2)
  final val sPhi: SchematicPredicateLabel = SchematicPredicateLabel("?p", 1)

  final val ax1ZeroSuccessor: Axiom = forall(x, !(s(x) === zero))
  final val ax2Injectivity: Axiom = forall(x, forall(y, (s(x) === s(y)) ==> (x === y)))
  final val ax3neutral: Axiom = forall(x, plus(x, zero) === x)
  final val ax4plus: Axiom = forall(x, forall(y, plus(x, s(y)) === s(plus(x, y))))
  final val ax5: Axiom = forall(x, times(x, zero) === zero)
  final val ax6: Axiom = forall(x, forall(y, times(x, s(y)) === plus(times(x, y), x)))
  final val ax7induction: Axiom = (sPhi(zero) /\ forall(x, sPhi(x) ==> sPhi(s(x)))) ==> forall(x, sPhi(x))

  final val runningPeanoTheory: RunningTheory = new RunningTheory()
  final val functions: Set[ConstantFunctionLabel] = Set(ConstantFunctionLabel("0", 0), s, plus, times)
  functions.foreach(runningPeanoTheory.addSymbol(_))

  private val peanoAxioms: Set[(String, Axiom)] = Set(
    ("A1", ax1ZeroSuccessor),
    ("A2", ax2Injectivity),
    ("A3", ax3neutral),
    ("A4", ax4plus),
    ("A5", ax5),
    ("A6", ax6),
    ("Induction", ax7induction)
  )
  peanoAxioms.foreach(a => runningPeanoTheory.addAxiom(a._1, a._2))
}
