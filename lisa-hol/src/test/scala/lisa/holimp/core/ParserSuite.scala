package lisa
package hol
package core

import org.scalatest.funsuite.AnyFunSuite

class ParserSuite extends AnyFunSuite:
  import Parser.*

  inline def assertEquals[T](actual: T, expected: T) = assert(actual == expected, s"Expected: $expected, but found: $actual")

  test("Parse a simple variable term") {
    val input = "v(x)(c[bool][])"
    val expected = Variable("x", BoolType)
    assertEquals(parseAll(input, term(using _)).get.value, expected)
  }

  test("Parse a simple constant term") {
    val input = "c(T)(c[bool][])"
    val expected = Constant("T", BoolType)
    assertEquals(parseAll(input, term(using _)).get.value, expected)
  }

  test("Parse a combination term") {
    val input = "C(c(T)(c[bool][]))(v(x)(c[bool][]))"
    val expected = Combination(Constant("T", BoolType), Variable("x", BoolType))
    assertEquals(parseAll(input, term(using _)).get.value, expected)
  }

  test("Parse an abstraction term") {
    val input = "A(v(x)(c[bool][]))(v(x)(c[bool][]))"
    val expected = Abstraction(Variable("x", BoolType), Variable("x", BoolType))
    assertEquals(parseAll(input, term(using _)).get.value, expected)
  }

  test("Parse a function type") {
    val input = "c[fun][[c[bool][]][c[bool][]]]"
    val expected = FunType(BoolType, BoolType)
    assertEquals(parseAll(input, typ(using _)).get.value, expected)
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
    "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(v(p)(c[bool][])))(v(p)(c[bool][]))"
  )

  test("Parse terms extracted from HOL Light proof export") {
    testTerms.foreach { input =>
      assertEquals(parseAll(input, term(using _)).get.value, ReferenceParser.parseAll(ReferenceParser.term, input).get)
    }
  }

  test("preserve identifiers, type annotations, and whitespace across constructors"):
    val names = Seq("x", "λ😀", " space name \t", "∀\"\\")
    val types = Seq("v[A]", "c[bool][]", "c[fun][[v[A]][c[bool][]]]", " c[pair][[v[A]][v[B]]] ")
    for name <- names; tpe <- types do
      val variable = s"v($name)($tpe)"
      val constant = s"c($name)($tpe)"
      val inputs = Seq(variable, constant, s" C( $variable )($constant) ", s"A($variable)(C($constant)($variable))")
      for input <- inputs do
        val expected = ReferenceParser.parseAll(ReferenceParser.term, input).get
        assertEquals(parseAll(input, term(using _)).get.value, expected)
      assertEquals(parseAll(tpe, typ(using _)).get.value, ReferenceParser.parseAll(ReferenceParser.typ, tpe).get)

  test("reject malformed input and trailing tokens"):
    val inputs = Seq("", "v()(v[A])", "v(x)(v[])", "v(x)(v[A])junk", "v(x)(v[A]", "A(c(x)(v[A]))(v(x)(v[A]))", "C(v(x)(v[A]))", "v(x) (v[A])")
    for input <- inputs do
      assert(!ReferenceParser.parseAll(ReferenceParser.term, input).successful)
      assert(parseAll(input, term(using _)).isInstanceOf[fastparse.Parsed.Failure], input)

  test("parse variable and type-variable entry points completely"):
    assertEquals(parseAll("v(x)(v[A])", variable(using _)).get.value, Variable("x", TypeVariable("A")))
    assertEquals(parseAll("v[A]", typeVariable(using _)).get.value, TypeVariable("A"))
    assert(parseAll("c(x)(v[A])", variable(using _)).isInstanceOf[fastparse.Parsed.Failure])
    assert(parseAll("v[A]suffix", typeVariable(using _)).isInstanceOf[fastparse.Parsed.Failure])

/** Keep the former grammar as an independent oracle for parser compatibility tests. */
private object ReferenceParser extends scala.util.parsing.combinator.RegexParsers:
  def typ: Parser[Type] = typeVariable ||| typeApplication
  def term: Parser[Term] = variable ||| constant ||| combination ||| abstraction
  private def identifier: Parser[String] = rep1(acceptIf(c => !"()[]".contains(c))(_ => "identifier")) ^^ (_.mkString)
  def variable: Parser[Variable] = "v(" ~ identifier ~ ")(" ~ typ ~ ")" ^^ { case _ ~ id ~ _ ~ tp ~ _ => Variable(id, tp) }
  def constant: Parser[Constant] = "c(" ~ identifier ~ ")(" ~ typ ~ ")" ^^ { case _ ~ id ~ _ ~ tp ~ _ => Constant(id, tp) }
  def combination: Parser[Combination] = "C(" ~ term ~ ")(" ~ term ~ ")" ^^ { case _ ~ a ~ _ ~ b ~ _ => Combination(a, b) }
  def abstraction: Parser[Abstraction] = "A(" ~ variable ~ ")(" ~ term ~ ")" ^^ { case _ ~ v ~ _ ~ body ~ _ => Abstraction(v, body) }
  def typeVariable: Parser[TypeVariable] = "v[" ~ identifier ~ "]" ^^ { case _ ~ id ~ _ => TypeVariable(id) }
  def typeApplication: Parser[TypeApplication] = "c[" ~ identifier ~ "][" ~ rep(typeArg) ~ "]" ^^ { case _ ~ id ~ _ ~ args ~ _ => TypeApplication(id, args) }
  private def typeArg: Parser[Type] = "[" ~ typ ~ "]" ^^ { case _ ~ tp ~ _ => tp }
