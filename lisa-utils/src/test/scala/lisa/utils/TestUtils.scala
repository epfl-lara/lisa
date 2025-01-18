package lisa.utils

import lisa.kernel.fol.FOL._
import lisa.utils.KernelHelpers._
import lisa.utils.KernelHelpers.given_Conversion_Identifier_String
import lisa.utils.KernelHelpers.given_Conversion_String_Identifier
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}

trait TestUtils {
  val (a, b, c) = (Constant("a", Prop), Constant("b", Prop), Constant("c", Prop))
  val p = Constant("p", Arrow(Ind, Prop))
  val (x, y, z) = (Variable("x", Ind), Variable("y", Ind), Variable("z", Ind))
  val (x1, y1, z1) = (Variable("x1", Ind), Variable("y1", Ind), Variable("z1", Ind))
  val (xPrime, yPrime, zPrime) = (Variable("x'", Ind), Variable("y'", Ind), Variable("z'", Ind))
  val (cx, cy, cz) = (Constant("x", Ind), Constant("y", Ind), Constant("z", Ind))
  val (f0, f1, f2, f3) = (Constant("f", Ind), Constant("f", Arrow(Ind, Ind)), Constant("f", Arrow(Ind, Arrow(Ind, Ind))), Constant("f", Arrow(Ind, Arrow(Ind, Arrow(Ind, Ind)))))
  val (sf1, sf2, sf3) = (Variable("f", Arrow(Ind, Ind)), Variable("f", Arrow(Ind, Arrow(Ind, Ind))), Variable("f", Arrow(Ind, Arrow(Ind, Arrow(Ind, Ind)))))
  val (sPhi1, sPhi2) = (Variable("phi", Arrow(Ind, Prop)), Variable("phi", Arrow(Ind, Arrow(Ind, Prop))))
  val (sc1, sc2) = (Variable("c", Prop >>: Prop), Variable("c", Prop >>: Prop))
  val (in, plus) = (Constant("elem", Prop >>: Prop >>: Ind), Constant("+", Arrow(Ind, Arrow(Ind, Ind))))

}
