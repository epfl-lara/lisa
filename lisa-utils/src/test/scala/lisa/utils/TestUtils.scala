package lisa.utils

import lisa.kernel.fol.FOL._
import lisa.utils.KernelHelpers._
import lisa.utils.KernelHelpers.given_Conversion_Identifier_String
import lisa.utils.KernelHelpers.given_Conversion_String_Identifier
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}

trait TestUtils {
  val (a, b, c) = (Constant("a", Formula), Constant("b", Formula), Constant("c", Formula))
  val p = Constant("p", Arrow(Term, Formula))
  val (x, y, z) = (Variable("x", Term), Variable("y", Term), Variable("z", Term))
  val (x1, y1, z1) = (Variable("x1", Term), Variable("y1", Term), Variable("z1", Term))
  val (xPrime, yPrime, zPrime) = (Variable("x'", Term), Variable("y'", Term), Variable("z'", Term))
  val (cx, cy, cz) = (Constant("x", Term), Constant("y", Term), Constant("z", Term))
  val (f0, f1, f2, f3) = (Constant("f", Term), Constant("f", Arrow(Term, Term)), Constant("f", Arrow(Term, Arrow(Term, Term))), Constant("f", Arrow(Term, Arrow(Term, Arrow(Term, Term)))))
  val (sf1, sf2, sf3) = (Variable("f", Arrow(Term, Term)), Variable("f", Arrow(Term, Arrow(Term, Term))), Variable("f", Arrow(Term, Arrow(Term, Arrow(Term, Term)))))
  val (sPhi1, sPhi2) = (Variable("phi", Arrow(Term, Formula)), Variable("phi", Arrow(Term, Arrow(Term, Formula))))
  val (sc1, sc2) = (Variable("c", Formula >>: Formula), Variable("c", Formula >>: Formula))
  val (in, plus) = (Constant("elem", Formula >>: Formula >>: Term), Constant("+", Arrow(Term, Arrow(Term, Term))))

}
