package lisa
package hol
package core

import scala.util.parsing.combinator.*

/**
  * A parser for the core HOL Light terms in ProofTrace export syntax.
  */
object Parser extends RegexParsers:

    def typ: Parser[Type] = typeVariable ||| typeApplication
    def term: Parser[Term] = variable ||| constant ||| combination ||| abstraction

    private type Identifier = String

    private def isParen(c: Char): Boolean = 
      c match
          case '(' | ')' | '[' | ']' => true
          case _ => false

    private def char: Parser[Char] = acceptIf(!isParen(_))(el => s"Unexpected: $el")
    private def identifier: Parser[Identifier] = rep1(char) ^^ { _.mkString }

    ///// Term parsers
    // term := variable | constant | combination | abstraction
    // variable := v(identifier)(type)
    // constant := c(identifier)(type)
    // combination := C(term)(term)
    // abstraction := A(variable)(term)
    def variable: Parser[Variable] = "v(" ~ identifier ~ ")(" ~ typ ~ ")" ^^ { case _ ~ id ~ _ ~ tp ~ _ => Variable(id, tp) }
    def constant: Parser[Constant] = "c(" ~ identifier ~ ")(" ~ typ ~ ")" ^^ { case _ ~ id ~ _ ~ tp ~ _ => Constant(id, tp) }
    def combination: Parser[Combination] = "C(" ~ term ~ ")(" ~ term ~ ")" ^^ { case _ ~ t1 ~ _ ~ t2 ~ _ => Combination(t1, t2) }
    def abstraction: Parser[Abstraction] = "A(" ~ variable ~ ")(" ~ term ~ ")" ^^ { case _ ~ v ~ _ ~ tm ~ _ => Abstraction(v, tm) }

    ///// Type parsers
    // type := typeVariable | typeApplication
    // typeVariable := v[identifier]
    // typeApplication := c[identifier][typeArg*]
    // typeArg := [type]
    def typeVariable: Parser[TypeVariable] = "v[" ~ identifier ~ "]" ^^ { case _ ~ id ~ _ => TypeVariable(id)}
    def typeApplication: Parser[TypeApplication] = "c[" ~ identifier ~ "][" ~ rep(typeArg) ~ "]" ^^ { case _ ~ id ~ _ ~ args ~ _ => TypeApplication(id, args) }
    private def typeArg: Parser[Type] = "[" ~ typ ~ "]" ^^ { case _ ~ tp ~ _ => tp}

end Parser
