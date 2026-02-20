package lisa.hol

import lisa.hol.core.*
import core.Parser.*
import extractor.*

val str =
  // "C(C(c(=)(c[fun][[c[fun][[c[fun][[v[A]][c[bool][]]]][c[bool][]]]][c[fun][[c[fun][[c[fun][[v[A]][c[bool][]]]][c[bool][]]]][c[bool][]]]]]))(c(?)(c[fun][[c[fun][[v[A]][c[bool][]]]][c[bool][]]])))(A(v(P)(c[fun][[v[A]][c[bool][]]]))(C(c(!)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]))(A(v(q)(c[bool][]))(C(C(c(==>)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(c(!)(c[fun][[c[fun][[v[A]][c[bool][]]]][c[bool][]]]))(A(v(x)(v[A]))(C(C(c(==>)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(C(v(P)(c[fun][[v[A]][c[bool][]]]))(v(x)(v[A]))))(v(q)(c[bool][]))))))(v(q)(c[bool][]))))))"
  "C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))(c(T)(c[bool][])))(C(C(c(=)(c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[fun][[c[fun][[c[bool][]][c[bool][]]]][c[bool][]]]]]))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))(A(v(p)(c[bool][]))(v(p)(c[bool][]))))"

@main def main =
  println(parse(term, str).getDone.pretty)
  