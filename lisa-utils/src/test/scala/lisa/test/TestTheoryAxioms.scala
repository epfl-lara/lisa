package lisa.test

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.KernelHelpers.{_, given}

trait TestTheoryAxioms {
  final val p1 = ConstantPredicateLabel("p1", 1)
  final val p2 = ConstantPredicateLabel("p2", 1)
  final val f1 = ConstantFunctionLabel("f1", 1)
  final val fixedElement = ConstantFunctionLabel("fixedElement", 0)
  final val anotherFixed = ConstantFunctionLabel("anotherElement", 0)

  val runningTestTheory = new RunningTheory()
  runningTestTheory.addSymbol(p1)
  runningTestTheory.addSymbol(p2)
  runningTestTheory.addSymbol(f1)
  runningTestTheory.addSymbol(fixedElement)
  runningTestTheory.addSymbol(anotherFixed)

  private final val x = VariableLabel("x")
  final val p1_implies_p2_f: Formula = forall(x, p1(x) ==> p2(x))
  final val ax2_f = p1(fixedElement())
  final val same_fixed_f = fixedElement() === anotherFixed()
  final val fixed_point_f = forall(x, (f1(x) === fixedElement()) <=> (x === fixedElement()))

  val p1_implies_p2 = runningTestTheory.addAxiom("p1_implies_p2", p1_implies_p2_f).get
  val A2 = runningTestTheory.addAxiom("A2", ax2_f).get
  val same_fixed = runningTestTheory.addAxiom("same_fixed", same_fixed_f).get
  val fixed_point = runningTestTheory.addAxiom("fixed_point", fixed_point_f).get
}
