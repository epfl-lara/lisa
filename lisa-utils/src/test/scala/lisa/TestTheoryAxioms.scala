package lisa.test

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.KernelHelpers.{_, given}

trait TestTheoryAxioms {
  final val p1 = Constant("p1", Arrow(Term, Formula))
  final val p2 = Constant("p2", Arrow(Term, Formula))
  final val f1 = Constant("f1", Arrow(Term, Term))
  final val fixedElement = Constant("fixedElement", Term)
  final val anotherFixed = Constant("anotherElement", Term)

  val runningTestTheory = new RunningTheory()
  runningTestTheory.addSymbol(p1)
  runningTestTheory.addSymbol(p2)
  runningTestTheory.addSymbol(f1)
  runningTestTheory.addSymbol(fixedElement)
  runningTestTheory.addSymbol(anotherFixed)

  private final val x = Variable("x", Term)
  final val p1_implies_p2_f = forall(x, p1(x) ==> p2(x))
  final val ax2_f = p1(fixedElement)
  final val same_fixed_f = fixedElement === anotherFixed
  final val fixed_point_f = forall(x, (f1(x) === fixedElement) <=> (x === fixedElement))

  val p1_implies_p2 = runningTestTheory.addAxiom("p1_implies_p2", p1_implies_p2_f).get
  val A2 = runningTestTheory.addAxiom("A2", ax2_f).get
  val same_fixed = runningTestTheory.addAxiom("same_fixed", same_fixed_f).get
  val fixed_point = runningTestTheory.addAxiom("fixed_point", fixed_point_f).get
}
