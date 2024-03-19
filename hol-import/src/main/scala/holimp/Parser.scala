package holimp

import Core.*
import scala.util.parsing.combinator.*

object Parser extends RegexParsers:
    type Identifier = String

    def isParen(c: Char): Boolean = c == '[' || c == ']' || c == '(' || c == ')'

    def char: Parser[Char] = acceptIf(!isParen(_))(el => s"Unexpected: $el")
    def identifier: Parser[Identifier] = rep1(char) ^^ {_.mkString}
    def typ: Parser[Type] = typeVariable ||| typeApplication
    def term: Parser[Term] = variable ||| constant ||| combination ||| abstraction

    def variable: Parser[Variable] = "v(" ~ identifier ~ ")(" ~ typ ~ ")" ^^ { case _ ~ id ~ _ ~ tp ~ _ => Variable(id, tp) }
    def constant: Parser[Constant] = "c(" ~ identifier ~ ")(" ~ typ ~ ")" ^^ { case _ ~ id ~ _ ~ tp ~ _ => Constant(id, tp) }
    def combination: Parser[Combination] = "C(" ~ term ~ ")(" ~ term ~ ")" ^^ { case _ ~ t1 ~ _ ~ t2 ~ _ => Combination(t1, t2) }
    def abstraction: Parser[Abstraction] = "A(" ~ variable ~ ")(" ~ term ~ ")" ^^ { case _ ~ v ~ _ ~ tm ~ _ => Abstraction(v, tm) }

    def typeVariable: Parser[TypeVariable] = "t[" ~ identifier ~ "]" ^^ { case _ ~ id ~ _ => TypeVariable(id)}
    def typeApplication: Parser[TypeApplication] = "T[" ~ identifier ~ "][" ~ rep(typeArg) ~ "]" ^^ { case _ ~ id ~ _ ~ args ~ _ => TypeApplication(id, args) }
    def typeArg: Parser[Type] = "[" ~ typ ~ "]" ^^ { case _ ~ tp ~ _ => tp}

end Parser