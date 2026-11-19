package lisa.hol

import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class TypedQuantifierSuite extends AnyFunSuite:
  private val A, x = variable[Ind]
  private val body = variable[Prop]

  test("construct typed universal quantifiers with either helper"):
    val formula: Expr[Prop] = tforall(x, A, body)
    assert(formula.isInstanceOf[TypedForall])
    assert(formula == ∀(x, (x ∈ A) ==> body))
    assert(tforall(x :: A, body) == formula)

  test("construct typed existential quantifiers with either helper"):
    val formula: Expr[Prop] = texists(x, A, body)
    assert(formula.isInstanceOf[TypedExists])
    assert(formula == ∃(x, (x ∈ A) /\ body))
    assert(texists(x :: A, body) == formula)
