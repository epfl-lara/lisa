package lisa.examples.peano_example

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.KernelHelpers.{_, given}

object PeanoArithmetics extends lisa.prooflib.Library {
  export lisa.fol.FOL.{*, given}
  final val (x, y, z) =
    (variable, variable, variable)

  final val zero = Constant("0")
  final val s = ConstantFunctionLabel("S", 1)
  final val plus = ConstantFunctionLabel("+", 2)
  final val times = ConstantFunctionLabel("*", 2)
  final val sPhi = predicate[1]
  val theory: RunningTheory = new RunningTheory()
  final val ax1ZeroSuccessor: Formula = forall(x, !(s(x) === zero))
  final val ax2Injectivity: Formula = forall(x, forall(y, (s(x) === s(y)) ==> (x === y)))
  final val ax3neutral: Formula = forall(x, plus(x, zero) === x)
  final val ax4plusSuccessor: Formula = forall(x, forall(y, plus(x, s(y)) === s(plus(x, y))))
  final val ax5timesZero: Formula = forall(x, times(x, zero) === zero)
  final val ax6timesDistrib: Formula = forall(x, forall(y, times(x, s(y)) === plus(times(x, y), x)))
  final val ax7induction: Formula = (sPhi(zero) /\ forall(x, sPhi(x) ==> sPhi(s(x)))) ==> forall(x, sPhi(x))

  final val functions: Set[ConstantTermLabel] = Set(ConstantFunctionLabel("0", 0), s, plus, times)
  functions.foreach(l => theory.addSymbol(l.underlyingLabel))

  private val peanoAxioms: Set[(String, Formula)] = Set(
    ("ax1ZeroSuccessor", ax1ZeroSuccessor),
    ("ax2Injectivity", ax2Injectivity),
    ("ax3neutral", ax3neutral),
    ("ax4plusSuccessor", ax4plusSuccessor),
    ("ax5timesZero", ax5timesZero),
    ("ax6timesDistrib", ax6timesDistrib),
    ("ax7induction", ax7induction)
  )
  peanoAxioms.foreach(a => theory.addAxiom(a._1, a._2.underlying))
}
