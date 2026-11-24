package lisa.hol

import lisa.hol.VarsAndFunctions.{_, given}
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class TypedQuantifierSuite extends AnyFunSuite:
  private val A, x = variable[Ind]
  private val body = variable[Prop]

  test("convert typed quantifier tuples without treating formulas as HOL terms"):
    summon[TypedForall <:< Expr[Prop]]
    summon[TypedExists <:< Expr[Prop]]
    val universal = tforall(x, A, body)
    val existential = texists(x, A, body)
    assert(((universal, universal, universal) |- existential) == Sequent(Set(universal), Set(existential)))
    assert(((universal, existential, x) |- body) == Sequent(Set(universal, existential, eqOne(x)), Set(body)))
    assert((Seq(x) |- Seq(universal, existential)) == Sequent(Set(eqOne(x)), Set(universal, existential)))

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
