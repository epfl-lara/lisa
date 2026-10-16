package lisa.hol

import lisa.hol.Import.Transformers.*
import org.scalatest.funsuite.AnyFunSuite

class VariableConversionSuite extends AnyFunSuite:
  test("keep equal names at distinct HOL types separate during repeated conversion"):
    val a = core.TypeVariable("conversion-A")
    val b = core.TypeVariable("conversion-B")
    val xa = core.Variable("conversion-x", a)
    val xb = core.Variable("conversion-x", b)
    val first = xa.toLisaVar
    for _ <- 0 until 10 do
      val other = xb.toLisaVar
      val again = xa.toLisaVar
      assert(again.id == first.id && again.typ == a.toLisaType)
      assert(other.id != first.id && other.typ == b.toLisaType)

  test("retain identifiers and annotations after many unrelated conversions"):
    val original = core.Variable("conversion-stable", core.FunType(core.BoolType, core.BoolType))
    val first = original.toLisaVar
    for i <- 0 until 5000 do core.Variable(s"conversion-fill-$i", core.BoolType).toLisaVar
    val again = original.copy().toLisaVar
    assert(again.id == first.id)
    assert(again.typ == first.typ && again.underlying == first.underlying)
