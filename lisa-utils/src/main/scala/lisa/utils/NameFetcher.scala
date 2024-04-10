package lisa.utils

import scala.quoted.*
import lisa.utils.parsing.UnreachableException


import scala.language.implicitConversions
import scala.quoted._


abstract class SourceValue{
  def value: String
}
abstract class SourceCompanion[V <: SourceValue](build: String => V){
  def apply()(implicit s: V): String = s.value
  implicit def wrap(s: String): V = build(s)
}

case class Name(value: String) extends SourceValue

inline implicit def generate: Name = ${ Macros.nameImpl }

object Macros {

  def nameImpl(using Quotes): Expr[Name] = {
    import quotes.reflect._
    '{Name(${Expr(Symbol.spliceOwner.owner.name)})}
  }



}
