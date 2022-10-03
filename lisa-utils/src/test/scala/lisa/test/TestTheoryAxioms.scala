package lisa.test

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.Helpers.{*, given}

trait TestTheoryAxioms {
  final val p1 = ConstantPredicateLabel("p1", 1)
  final val p2 = ConstantPredicateLabel("p2", 1)
  final val f1 = ConstantFunctionLabel("f1", 1)
  final val fixedElement = ConstantFunctionLabel("fixed_element", 0)
  final val anotherFixed = ConstantFunctionLabel("another_element", 0)

  val runningTestTheory = new RunningTheory()
  runningTestTheory.addSymbol(p1)
  runningTestTheory.addSymbol(p2)
  runningTestTheory.addSymbol(f1)
  runningTestTheory.addSymbol(fixedElement)
  runningTestTheory.addSymbol(anotherFixed)

  private final val x = VariableLabel("x")
  final val p1_implies_p2: Formula = forall(x, p1(x) ==> p2(x))
  final val ax2 = p1(fixedElement())
  final val same_fixed = fixedElement() === anotherFixed()
  final val fixed_point = forall(x, (f1(x) === fixedElement()) <=> (x === fixedElement()))

  assert(runningTestTheory.addAxiom("p1_implies_p2", p1_implies_p2), "p1_implies_p2")
  assert(runningTestTheory.addAxiom("A2", ax2), "ax2")
  assert(runningTestTheory.addAxiom("same_fixed", same_fixed), "same fixed")
  assert(runningTestTheory.addAxiom("fixed_point", fixed_point), "fixed point")
}
