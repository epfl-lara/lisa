package lisa.test

import lisa.prooflib.Library
import TestTheory as TT

object TestTheoryLibrary extends Library {
  val theory: TT.runningTestTheory.type = TT.runningTestTheory

  export F.{*, given}

  final val p1 = ConstantPredicateLabel("p1", 1)
  final val p2 = ConstantPredicateLabel("p2", 1)
  final val f1 = ConstantFunctionLabel("f1", 1)
  final val fixedElement = Constant("fixedElement")
  final val anotherFixed = Constant("anotherElement")

  addSymbol(p1)
  addSymbol(p2)
  addSymbol(f1)
  addSymbol(fixedElement)
  addSymbol(anotherFixed)

  private final val x = Variable("x")
  final val p1_implies_p2_f: Formula = forall(x, p1(x) ==> p2(x))
  final val ax2 = p1(fixedElement)
  final val same_fixed_f = fixedElement === anotherFixed
  final val fixed_point_f = forall(x, (f1(x) === fixedElement) <=> (x === fixedElement))

  val p1_implies_p2 = AXIOM(TT.p1_implies_p2, p1_implies_p2_f, "p1_implies_p2")
  val A2 = AXIOM(TT.A2, ax2, "A2")
  val same_fixed = AXIOM(TT.same_fixed, same_fixed_f, "same_fixed")
  val fixed_point = AXIOM(TT.fixed_point, fixed_point_f, "fixed_point")

  assert(fixed_point == fixed_point)
}
