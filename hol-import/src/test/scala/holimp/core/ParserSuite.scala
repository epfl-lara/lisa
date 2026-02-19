package holimp
package core

class ParserSuite extends munit.FunSuite:
  import Parser.*

  test("Parse a simple variable term") {
    val input = "v(x)(c[bool][])"
    val expected = Variable("x", BoolType)
    assertEquals(parse(term, input).get, expected)
  }

  test("Parse a simple constant term") {
    val input = "c(T)(c[bool][])"
    val expected = Constant("T", BoolType)
    assertEquals(parse(term, input).get, expected)
  }

  test("Parse a combination term") {
    val input = "C(c(T)(c[bool][]))(v(x)(c[bool][]))"
    val expected = Combination(Constant("T", BoolType), Variable("x", BoolType))
    assertEquals(parse(term, input).get, expected)
  }

  test("Parse an abstraction term") {
    val input = "A(v(x)(c[bool][]))(v(x)(c[bool][]))"
    val expected = Abstraction(Variable("x", BoolType), Variable("x", BoolType))
    assertEquals(parse(term, input).get, expected)
  }

  test("Parse a function type") {
    val input = "c[fun][[c[bool][]][c[bool][]]]"
    val expected = FunType(BoolType, BoolType)
    assertEquals(parse(typ, input).get, expected)
  }

  // test terms extracted from HOL Light proof export
  val testTerms = Seq(
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))(C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))",
    "C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))(A(v(p)(c[bool][]))(v(p)(c[bool][])))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))(c(T)(c[bool][]))",
    "C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[bool][]]]]]))(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]])))(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))",
    "C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][]))))(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))(A(v(p)(c[bool][]))(v(p)(c[bool][])))))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))(c(T)(c[bool][]))))(C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))(A(v(p)(c[bool][]))(v(p)(c[bool][])))))(c(T)(c[bool][])))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))(A(v(p)(c[bool][]))(v(p)(c[bool][])))))(c(T)(c[bool][]))",
    "c(T)(c[bool][])",
    "v(t)(c[bool][])",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(t)(c[bool][])))(c(T)(c[bool][]))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(t)(c[bool][])))(c(T)(c[bool][]))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(t)(c[bool][])))(v(t)(c[bool][]))",
    "C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[bool][]]]]]))(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]])))(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))",
    "C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(t)(c[bool][]))))(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(t)(c[bool][])))(v(t)(c[bool][]))))(C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))(v(t)(c[bool][])))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))(v(t)(c[bool][]))",
    "v(t)(c[bool][])",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(t)(c[bool][])))(C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(t)(c[bool][])))(c(T)(c[bool][])))",
    "C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[bool][]]]]]))(c(/\\)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]])))(A(v(p)(c[bool][]))(A(v(q)(c[bool][]))(C(C(c(=)(c[fun][[c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[bool][]]]][c[fun][[c[fun][[c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]][c[bool][]]]][c[bool][]]]]]))(A(v(f)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(C(v(f)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(p)(c[bool][])))(v(q)(c[bool][])))))(A(v(f)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(C(v(f)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))(c(T)(c[bool][])))))))",
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(p)(c[bool][])))(v(p)(c[bool][]))",
  )

  test("Parse terms extracted from HOL Light proof export") {
    testTerms.foreach { input =>
      assert(parse(term, input).successful, s"Failed to parse term: $input")
    }
  }
