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
      inline infix def _VS_(t2:Term): Assertion = {
        assert(instantiateTermSchemas(c.t, c.m.toMap) == t2, "\n - " + prettyTerm(instantiateTermSchemas(c.t, c.m.toMap)) +" didn't match " + prettyTerm(t2))
      }
    }
    //  def instantiateTermSchemas(t: Term, m: Map[SchematicTermLabel, LambdaTermTerm]): Term

    val cases:List[Assertion] = List(
      $(x, x -> x()) _VS_ x,
      $(x, y -> y()) _VS_ x,
      $(x, x -> y()) _VS_ y,
      $(x, y -> z(), x -> y()) _VS_ y,
      $(x, x2 -> lambda(y, f(y))) _VS_ x,
      $(f(x), x -> y()) _VS_ f(y),
      $(f(f(h(x, y))), x -> y()) _VS_ f(f(h(y, y))),
      $(f(f(h(x, y))), x -> z()) _VS_ f(f(h(z, y))),
      $(f(f(h(x, y))), x -> z(), z -> x()) _VS_ f(f(h(z, y))),
      $(f(f(h(x, y))), x -> y(), y -> x()) _VS_ f(f(h(y, x))),
      $(f(f(h(x, y))), z -> y(), g -> lambda(Seq(x), f(h(y, x)))) _VS_ f(f(h(x, y))),
      $(f(f(h(x, y))), f -> lambda(x, x)) _VS_ h(x, y),
      $(f(f(h(x, y))), f -> lambda(x, y)) _VS_ y,
      $(f(f(h(x, y))), f -> lambda(x, f(f(x)))) _VS_ f(f(f(f(h(x,y))))),
      $(f(f(h(x, y))), f -> lambda(x, f(f(x)))) _VS_ f(f(f(f(h(x,y))))),
      $(f(f(h(x, y))), f -> lambda(x, f(f(x))), h -> lambda(Seq(x, z), h(f(x), h(g(z), x)))) _VS_ f(f(f(f(h(f(x),h(g(y), x)))))),
    )
  }

  test("Substitution of Terms in Formulas") {
    case class $(f: Formula, m: (SchematicTermLabel, LambdaTermTerm)*)
    extension (c: $) {
      inline infix def _VS_(t2: Formula): Assertion = {
        assert(instantiateTermSchemas(c.f, c.m.toMap) == t2, "\n - " + prettyFormula(instantiateTermSchemas(c.f, c.m.toMap)) + " didn't match " + prettyFormula(t2))
      }
    }
    //  def instantiateTermSchemas(t: Term, m: Map[SchematicTermLabel, LambdaTermTerm]): Term

    val cases: List[Assertion] = List(
      $(Q(x), x -> x()) _VS_ Q(x),
      $(Q(x), y -> y()) _VS_ Q(x),
      $(c1(c1(Q(x))), x -> y()) _VS_ c1(c1(Q(y))),
      $(Q(f(f(h(x, y)))), x -> y()) _VS_ Q(f(f(h(y, y)))),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z()) _VS_ Q(f(f(h(z, y)))) /\ R(z, f(y)),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z(), h -> lambda(Seq(x, z), g(h(z, y)))) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, f(y)),
      $(R(x, h(f(z), y)), x -> z(), h -> lambda(Seq(x, z), g(h(z, y))), z -> y()) _VS_ R(z, g(h(y, y))),
      $(Q(f(f(h(x, y)))) /\ R(x, h(y, f(z))), x -> z(), h -> lambda(Seq(x, z), g(h(z, y))), z -> y()) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, g(h(f(y), y))),
    )
  }

}
