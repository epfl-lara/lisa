package lisa.test

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.Helpers.{_, given}

trait TestTheoryAxioms {
  final val p1 = ConstantPredicateLabel("p1", 1)
  final val p2 = ConstantPredicateLabel("p2", 1)
  final val f1 = ConstantFunctionLabel("f1", 1)
  final val fixed_element = ConstantFunctionLabel("fixed_element", 0)
  final val another_fixed = ConstantFunctionLabel("another_element", 0)

  val runningTestTheory = new RunningTheory()
  runningTestTheory.addSymbol(p1)
  runningTestTheory.addSymbol(p2)
  runningTestTheory.addSymbol(f1)
  runningTestTheory.addSymbol(fixed_element)
  runningTestTheory.addSymbol(another_fixed)

  private final val x = VariableLabel("x")
  final val p1_implies_p2: Formula = forall(x, p1(x) ==> p2(x))
  final val p1_for_fixed = p1(fixed_element())
  final val same_fixed = fixed_element() === another_fixed()
  final val fixed_point = forall(x, (f1(x) === fixed_element()) <=> (x === fixed_element()))

  assert(runningTestTheory.addAxiom("p1_implies_p2", p1_implies_p2), "p1_implies_p2")
  assert(runningTestTheory.addAxiom("p1_for_fixed", p1_for_fixed), "p1_for_fixed")
  assert(runningTestTheory.addAxiom("same_fixed", same_fixed), "same fixed")
  assert(runningTestTheory.addAxiom("fixed_point", fixed_point), "fixed point")
}
