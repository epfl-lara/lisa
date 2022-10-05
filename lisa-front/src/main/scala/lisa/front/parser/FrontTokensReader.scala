package lisa.front.parser

import scala.util.parsing.input.NoPosition
import scala.util.parsing.input.Position
import scala.util.parsing.input.Reader

private[parser] class FrontTokensReader(tokens: Seq[FrontToken]) extends Reader[FrontToken] {
  override def first: FrontToken = tokens.head
  override def atEnd: Boolean = tokens.isEmpty
  override def pos: Position = tokens.headOption.map(_.pos).getOrElse(NoPosition)
  override def rest: Reader[FrontToken] = new FrontTokensReader(tokens.tail)
}
