package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.FOLPrinter.*
import org.scalatest.compatible.Assertion
import org.scalatest.funsuite.AnyFunSuite


class SubstitutionTest extends AnyFunSuite {
  private val x = variable
  private val x2 = SchematicFunctionLabel("x", 1)
  private val y = variable
  private val z = variable

  private val f = function(1)
  private val g = function(1)

  private val h = function(2)

  private val X = formulaVariable
  private val Y = formulaVariable
  private val Z = formulaVariable


  private val P = predicate(1)
  private val Q = predicate(1)

  private val R = predicate(2)

  private val c1 = connector(1)

  private val c2 = connector(2)

  test("Substitution in Terms") {
    case class $(t:Term, m: (SchematicTermLabel, LambdaTermTerm)*)
    extension (c:$) {
      inline def ->(t2:Term): Assertion = {
        assert(instantiateTermSchemas(c.t, c.m.toMap) == t2, "\n - " + prettyTerm(instantiateTermSchemas(c.t, c.m.toMap)) +" didn't match " + prettyTerm(t2))
      }
    }
    //  def instantiateTermSchemas(t: Term, m: Map[SchematicTermLabel, LambdaTermTerm]): Term

    val cases:List[Assertion] = List(
      $(x, x -> x()) -> x,
      $(x, y -> y()) -> x,
      $(x, x -> y()) -> y,
      $(x, y -> z(), x -> y()) -> y,
      $(x, x2 -> lambda(y, f(y))) -> x,
      $(f(x), x -> y()) -> f(y),
      $(f(f(h(x, y))), x -> y()) -> f(f(h(y, y))),
      $(f(f(h(x, y))), x -> z()) -> f(f(h(z, y))),
      $(f(f(h(x, y))), x -> z(), z -> x()) -> f(f(h(z, y))),
      $(f(f(h(x, y))), x -> y(), y -> x()) -> f(f(h(y, x))),
    )
  }

}
