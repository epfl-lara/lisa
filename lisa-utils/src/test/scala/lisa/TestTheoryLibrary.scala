package lisa.test

import lisa.utils.prooflib.Library

object TestTheoryLibrary extends Library {
  val theory: TestTheory.runningTestTheory.type = TestTheory.runningTestTheory

  export lisa.utils.fol.FOL.{*, given}

  final val p1 = constant[Ind >>: Prop]
  final val p2 = constant[Ind >>: Prop]
  final val f1 = constant[Ind >>: Ind]
  final val fixedElement = constant[Ind]
  final val anotherElement = constant[Ind]
  addSymbol(p1)
  addSymbol(p2)
  addSymbol(f1)
  addSymbol(fixedElement)
  addSymbol(anotherElement)

  private final val x = variable[Ind]
  final val p1_implies_p2_f: Expr[Prop] = forall(x, p1(x) ==> p2(x))
  final val ax2 = p1(fixedElement)
  final val same_fixed_f = fixedElement === anotherElement
  final val fixed_point_f = forall(x, (f1(x) === fixedElement) <=> (x === fixedElement))

  val p1_implies_p2 = AXIOM(TestTheory.p1_implies_p2, p1_implies_p2_f, "p1_implies_p2")
  val A2 = AXIOM(TestTheory.A2, ax2, "A2")
  println(s"TestTheory.same_fixed: ${TestTheory.same_fixed}")
  println(s"same_fixed_f                 : ${same_fixed_f}")
  println(s"same_fixed_f.underlying      : ${same_fixed_f.underlying}")
  println(s"TestTheory.same_fixed.ax     : ${TestTheory.same_fixed.ax}")
  val same_fixed = AXIOM(TestTheory.same_fixed, same_fixed_f, "same_fixed")
  val fixed_point = AXIOM(TestTheory.fixed_point, fixed_point_f, "fixed_point")

  assert(fixed_point == fixed_point)
}
