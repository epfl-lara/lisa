package lisa.hol.core

import org.scalatest.funsuite.AnyFunSuite

class TypeHashSuite extends AnyFunSuite:
  test("retain structural hashing for nested and copied type applications"):
    val types = (0 until 40).scanLeft(BoolType: Type)((t, i) => FunType(TypeVariable(s"A$i"), t))
    for t <- types.collect { case app: TypeApplication => app } do
      assert(t.hashCode == scala.util.hashing.MurmurHash3.productHash(t))
      assert(t.copy() == t && t.copy().hashCode == t.hashCode)
      val changed = t.copy(name = "other", args = List(t))
      assert(changed.hashCode == scala.util.hashing.MurmurHash3.productHash(changed))
      assert(Map(t -> 42).get(t.copy()).contains(42))

  test("use parsed and constructed equal types interchangeably as map keys"):
    val parsed = Parser.parseAll("c[fun][[v[A]][c[bool][]]]", Parser.typ(using _)).get.value
    val constructed = FunType(TypeVariable("A"), BoolType)
    assert(parsed == constructed)
    assert(parsed.hashCode == constructed.hashCode)
    assert(Map(parsed -> "parsed").get(constructed).contains("parsed"))

  test("keep distinct types separate even when their structural hashes collide"):
    val a = TypeApplication("Aa", Nil)
    val b = TypeApplication("BB", Nil)
    assert(a.hashCode == b.hashCode)
    assert(a != b)
    val values = Map(a -> 1, b -> 2)
    assert(values(a) == 1 && values(b) == 2)
