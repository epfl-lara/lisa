package lisa.utils.fol

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class ExpressionPrintingSuite extends AnyFunSuite:
  private val x = variable[Ind](K.Identifier("print-x"))
  private def function = variable[Ind >>: Ind](K.Identifier("print-f"))

  test("render default applications and separated applications"):
    val f = function
    assert(f.mkString(Seq(x)) == f.defaultMkString(Seq(x)))
    assert(f.mkStringSeparated(Seq(x)) == f.defaultMkStringSeparated(Seq(x)))
    assert(f(x).toString == f.defaultMkString(Seq(x)))

  test("replace custom printers independently and restore defaults"):
    val f = function
    f.mkString = args => s"custom[${args.size}]"
    f.mkStringSeparated = args => s"separate[${args.size}]"
    assert(f(x).toString == "custom[1]")
    assert(f.mkStringSeparated(Seq(x)) == "separate[1]")
    f.mkString = f.defaultMkString
    assert(f(x).toString == f.defaultMkString(Seq(x)))
    assert(f.mkStringSeparated(Seq(x)) == "separate[1]")

  test("keep printers local to their expression instance"):
    val f = function
    val g = function
    f.mkString = _ => "local"
    assert(f(x).toString == "local")
    assert(g(x).toString == g.defaultMkString(Seq(x)))

  test("print qualified constants and binders without changing their identifiers"):
    val f = Constant[Ind >>: Ind](K.Identifier("qualified.owner.f", 3))
    val binding = binder[Ind, Ind, Ind](K.Identifier("qualified.owner.bind"))
    assert(f.fullName == "qualified.owner.f" + K.Identifier.counterSeparator + "3")
    assert(f.shortName == "f" + K.Identifier.counterSeparator + "3")
    assert(f(x).toString == s"${f.shortName}($x)")
    assert(binding(x, x).toString == s"bind($x, $x)")
    assert(binding.mkStringSeparated(Seq(λ(x, x))) == s"(bind($x, $x))")
    assert(binding.underlying.id.name == "qualified.owner.bind")
