package lisa.front.parser

/**
 * Symbols to be used by the parser and printer.
 * There exists two variants, [[FrontSymbols.FrontAsciiSymbols]] and [[FrontSymbols.FrontUnicodeSymbols]].
 */
private[front] sealed abstract class FrontSymbols {
  val Forall: String
  val Exists: String
  val ExistsOne: String
  val Iff: String
  val Implies: String
  val Or: String
  val And: String
  val Exclamation: String
  val Turnstile: String
  val Ellipsis: String
  val Subset: String
  val Membership: String
  val EmptySet: String
  val Equal: String = "="
  val Tilde: String = "~"
  val Backslash: String = "\\"
  val CurlyBracketOpen: String = "{"
  val CurlyBracketClose: String = "}"
  val SquareBracketOpen: String = "["
  val SquareBracketClose: String = "]"
  val ParenthesisOpen: String = "("
  val ParenthesisClose: String = ")"
  val Dot: String = "."
  val Comma: String = ","
  val Semicolon: String = ";"
  val QuestionMark: String = "?"
  val PowerSet: String = "P"
  val UnionSet: String = "U"
}

private[front] object FrontSymbols {
  object FrontAsciiSymbols extends FrontSymbols {
    override val Forall: String = "forall"
    override val Exists: String = "exists"
    override val ExistsOne: String = "existsone"
    override val Iff: String = "<=>"
    override val Implies: String = "=>"
    override val Or: String = raw"\/"
    override val And: String = """/\"""
    override val Exclamation: String = "!"
    override val Turnstile: String = "|-"
    override val Ellipsis: String = "..."
    override val Membership: String = "in"
    override val Subset: String = "sub"
    override val EmptySet: String = "{}"
  }

  object FrontUnicodeSymbols extends FrontSymbols {
    override val Forall: String = "∀"
    override val Exists: String = "∃"
    override val ExistsOne: String = "∃!"
    override val Iff: String = "↔"
    override val Implies: String = "→"
    override val Or: String = "∨"
    override val And: String = "∧"
    override val Exclamation: String = "¬"
    override val Turnstile: String = "⊢"
    override val Ellipsis: String = "…"
    override val Membership: String = "∈"
    override val Subset: String = "⊆"
    override val EmptySet: String = "∅"
  }

  object FrontLatexSymbols extends FrontSymbols {
    override val Forall: String = raw"\forall"
    override val Exists: String = raw"\exists"
    override val ExistsOne: String = raw"\exists!"
    override val Iff: String = raw"\Leftrightarrow"
    override val Implies: String = raw"\Rightarrow"
    override val Or: String = raw"\lor"
    override val And: String = raw"\land"
    override val Exclamation: String = raw"\neg"
    override val Turnstile: String = raw"\vdash"
    override val Ellipsis: String = raw"\ldots"
    override val Membership: String = raw"\in"
    override val Subset: String = raw"\subseteq"
    override val EmptySet: String = raw"\varnothing"
    override val Tilde: String = raw"\sim"
    override val Backslash: String = raw"\setminus"
    override val CurlyBracketOpen: String = raw"\{"
    override val CurlyBracketClose: String = raw"\}"
    override val PowerSet: String = raw"\mathcal{P}"
    override val UnionSet: String = raw"\mathcal{U}"
  }
}
