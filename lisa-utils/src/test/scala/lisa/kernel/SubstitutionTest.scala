package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.FOLPrinter.*
import lisa.utils.KernelHelpers.{_, given}
import org.scalatest.compatible.Assertion
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionTest extends AnyFunSuite {
  private val x = variable
  private val x1 = VariableLabel(Identifier("x", 1))
  private val x2 = variable
  private val x3 = variable
  private val y = variable
  private val y2 = variable
  private val y3 = variable
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
  private val d1 = connector(1)

  private val e2 = connector(2)

  test("Substitution in Terms") {
    case class $(t: Term, m: (SchematicTermLabel, LambdaTermTerm)*)
    extension (c: $) {
      inline infix def _VS_(t2: Term): Assertion = {
        assert(instantiateTermSchemasInTerm(c.t, c.m.toMap) == t2, "\n - " + prettyTerm(instantiateTermSchemasInTerm(c.t, c.m.toMap)) + " didn't match " + prettyTerm(t2))
      }
    }

    val cases: List[Assertion] = List(
      $(x, x -> x()) _VS_ x,
      $(x, y -> y()) _VS_ x,
      $(x, x -> y()) _VS_ y,
      $(x, y -> z(), x -> y()) _VS_ y,
      $(x, g -> lambda(y, f(y))) _VS_ x,
      $(f(x), x -> y()) _VS_ f(y),
      $(f(f(h(x, y))), x -> y()) _VS_ f(f(h(y, y))),
      $(f(f(h(x, y))), x -> z()) _VS_ f(f(h(z, y))),
      $(f(f(h(x, y))), x -> z(), z -> x()) _VS_ f(f(h(z, y))),
      $(f(f(h(x, y))), x -> y(), y -> x()) _VS_ f(f(h(y, x))),
      $(f(f(h(x, y))), z -> y(), g -> lambda(Seq(x), f(h(y, x)))) _VS_ f(f(h(x, y))),
      $(f(f(h(x, y))), f -> lambda(x, x)) _VS_ h(x, y),
      $(f(f(h(x, y))), f -> lambda(x, y)) _VS_ y,
      $(f(f(h(x, y))), f -> lambda(x, f(f(x)))) _VS_ f(f(f(f(h(x, y))))),
      $(f(f(h(x, y))), f -> lambda(x, f(f(x))), h -> lambda(Seq(x, z), h(f(x), h(g(z), x)))) _VS_ f(f(f(f(h(f(x), h(g(y), x))))))
    )
  }

  test("Substitution of Terms in Formulas") {
    case class $(f: Formula, m: (SchematicTermLabel, LambdaTermTerm)*)
    extension (c: $) {
      inline infix def _VS_(t2: Formula): Assertion = {
        assert(isSame(instantiateTermSchemas(c.f, c.m.toMap), t2), "\n - " + prettyFormula(instantiateTermSchemas(c.f, c.m.toMap)) + " didn't match " + prettyFormula(t2))
      }
    }

    val cases: List[Assertion] = List(
      $(Q(x), x -> x()) _VS_ Q(x),
      $(Q(x), y -> y()) _VS_ Q(x),
      $(c1(c1(Q(x))), x -> y()) _VS_ c1(c1(Q(y))),
      $(Q(f(f(h(x, y)))), x -> y()) _VS_ Q(f(f(h(y, y)))),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z()) _VS_ Q(f(f(h(z, y)))) /\ R(z, f(y)),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z(), h -> lambda(Seq(x, z), g(h(z, y)))) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, f(y)),
      $(R(x, h(f(z), y)), x -> z(), h -> lambda(Seq(x, z), g(h(z, y))), z -> y()) _VS_ R(z, g(h(y, y))),
      $(Q(f(f(h(x, y)))) /\ R(x, h(y, f(z))), x -> z(), h -> lambda(Seq(x, z), g(h(z, y))), z -> y()) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, g(h(f(y), y))),
      $(forall(x, R(x, y)), x -> z()) _VS_ forall(x, R(x, y)),
      $(forall(x, R(x, y)), y -> z()) _VS_ forall(x, R(x, z)),
      $(forall(x, P(x)), x1 -> f(x())) _VS_ forall(x, P(x)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> z(), x -> y()) _VS_ forall(x, R(x, z)) /\ P(h(y, z)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> x()) _VS_ forall(y, R(y, x)) /\ P(h(x, x)),
      $(existsOne(x, R(x, y)) /\ P(h(x, y)), y -> x()) _VS_ existsOne(y, R(y, x)) /\ P(h(x, x))
    )
  }

  test("Substitution of Predicates in Formulas") {
    case class $(f: Formula, m: (SchematicVarOrPredLabel, LambdaTermFormula)*)
    extension (c: $) {
      inline infix def _VS_(t2: Formula): Assertion = {
        assert(
          isSame(instantiatePredicateSchemas(c.f, c.m.toMap), t2),
          "\n - " + prettyFormula(instantiatePredicateSchemas(c.f, c.m.toMap)) + " didn't match " + prettyFormula(t2)
        )
      }
    }

    val cases: List[Assertion] = List(
      $(X, X -> X()) _VS_ X,
      $(X, Y -> Y()) _VS_ X,
      $(X, X -> Y()) _VS_ Y,
      $(X, Y -> Z(), X -> Y()) _VS_ Y,
      $(c1(X), X -> Y()) _VS_ c1(Y),
      $(c1(c1(e2(X, Y))), X -> Y()) _VS_ c1(c1(e2(Y, Y))),
      $(c1(c1(e2(X, Y))), X -> Z()) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Z(), Z -> X()) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Y(), Y -> X()) _VS_ c1(c1(e2(Y, X))),
      $(c1(c1(e2(X, Y))), Z -> Y()) _VS_ c1(c1(e2(X, Y))),
      $(R(x, f(y)), R -> lambda(Seq(z, y), P(z) /\ Q(y))) _VS_ P(x) /\ Q(f(y)),
      $(R(x, f(y)) /\ R(z, z), R -> lambda(Seq(z, y), P(z) /\ Q(y))) _VS_ (P(x) /\ Q(f(y))) /\ (P(z) /\ Q(z)),
      $(forall(y, R(x, f(y))), R -> lambda(Seq(x, z), (x === z) /\ P(f(y)))) _VS_ forall(y2, (x === f(y2)) /\ P(f(y)))
    )
  }

  test("Substitution of Formulas in Formulas") {
    case class $(f: Formula, m: (SchematicConnectorLabel, LambdaFormulaFormula)*)
    extension (c: $) {
      inline infix def _VS_(t2: Formula): Assertion = {
        assert(instantiateConnectorSchemas(c.f, c.m.toMap) == t2, "\n - " + prettyFormula(instantiateConnectorSchemas(c.f, c.m.toMap)) + " didn't match " + prettyFormula(t2))
      }
    }

    val cases: List[Assertion] = List(
      $(c1(P(x)), c1 -> lambda(X, !X)) _VS_ !P(x),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, X)) _VS_ e2(X, P(y)),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, Y)) _VS_ Y,
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, c1(c1(X)))) _VS_ c1(c1(c1(c1(e2(X, P(y))))))
    )
  }

  test("Simultaneous Substitutions in Formulas") {
    case class $(f: Formula, m: ((SchematicConnectorLabel, LambdaFormulaFormula) | (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm))*)
    extension (c: $) {
      inline infix def _VS_(t2: Formula): Assertion = {
        val mCon: Map[SchematicConnectorLabel, LambdaFormulaFormula] = c.m
          .collect({
            case e if e._1.isInstanceOf[SchematicConnectorLabel] => e
          })
          .toMap
          .asInstanceOf
        val mPred: Map[SchematicVarOrPredLabel, LambdaTermFormula] = c.m
          .collect({
            case e if e._1.isInstanceOf[SchematicVarOrPredLabel] => e
          })
          .toMap
          .asInstanceOf
        val mTerm: Map[SchematicTermLabel, LambdaTermTerm] = c.m
          .collect({
            case e if e._1.isInstanceOf[SchematicTermLabel] => e
          })
          .toMap
          .asInstanceOf
        assert(
          isSame(instantiateSchemas(c.f, mCon, mPred, mTerm), t2),
          "\n - " + prettyFormula(instantiateSchemas(c.f, mCon, mPred, mTerm)) + " didn't match " + prettyFormula(t2)
        )
      }
    }

    val cases: List[Assertion] = List(
      $(Q(x), x -> x()) _VS_ Q(x),
      $(Q(x), y -> y()) _VS_ Q(x),
      $(c1(c1(Q(x))), x -> y()) _VS_ c1(c1(Q(y))),
      $(Q(f(f(h(x, y)))), x -> y()) _VS_ Q(f(f(h(y, y)))),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z()) _VS_ Q(f(f(h(z, y)))) /\ R(z, f(y)),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z(), h -> lambda(Seq(x, z), g(h(z, y)))) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, f(y)),
      $(R(x, h(f(z), y)), x -> z(), h -> lambda(Seq(x, z), g(h(z, y))), z -> y()) _VS_ R(z, g(h(y, y))),
      $(Q(f(f(h(x, y)))) /\ R(x, h(y, f(z))), x -> z(), h -> lambda(Seq(x, z), g(h(z, y))), z -> y()) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, g(h(f(y), y))),
      $(forall(x, R(x, y)), x -> z()) _VS_ forall(x, R(x, y)),
      $(forall(x, R(x, y)), y -> z()) _VS_ forall(x, R(x, z)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> z(), x -> y()) _VS_ forall(x, R(x, z)) /\ P(h(y, z)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> x()) _VS_ forall(y, R(y, x)) /\ P(h(x, x)),
      $(existsOne(x, R(x, y)) /\ P(h(x, y)), y -> x()) _VS_ existsOne(y, R(y, x)) /\ P(h(x, x)),
      $(X, X -> X()) _VS_ X,
      $(X, Y -> Y()) _VS_ X,
      $(X, X -> Y()) _VS_ Y,
      $(X, Y -> Z(), X -> Y()) _VS_ Y,
      $(c1(X), X -> Y()) _VS_ c1(Y),
      $(c1(c1(e2(X, Y))), X -> Y()) _VS_ c1(c1(e2(Y, Y))),
      $(c1(c1(e2(X, Y))), X -> Z()) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Z(), Z -> X()) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Y(), Y -> X()) _VS_ c1(c1(e2(Y, X))),
      $(c1(c1(e2(X, Y))), Z -> Y()) _VS_ c1(c1(e2(X, Y))),
      $(R(x, f(y)), R -> lambda(Seq(z, y), P(z) /\ Q(y))) _VS_ P(x) /\ Q(f(y)),
      $(R(x, f(y)) /\ R(z, z), R -> lambda(Seq(z, y), P(z) /\ Q(y))) _VS_ (P(x) /\ Q(f(y))) /\ (P(z) /\ Q(z)),
      $(forall(y, R(x, f(y))), R -> lambda(Seq(x, z), (x === z) /\ P(f(y)))) _VS_ forall(y2, (x === f(y2)) /\ P(f(y))),
      $(c1(P(x)), c1 -> lambda(X, !X)) _VS_ !P(x),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, X)) _VS_ e2(X, P(y)),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, Y)) _VS_ Y,
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, c1(c1(X)))) _VS_ c1(c1(c1(c1(e2(X, P(y)))))),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, c1(c1(X))), e2 -> lambda(Seq(X, Y), X <=> Y), X -> (z === y)) _VS_ c1(c1(c1(c1((z === y) <=> P(y))))),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, c1(c1(X))), e2 -> lambda(Seq(X, Y), X <=> Y), X -> (z === y), P -> lambda(x, !(x === f(h(x, y))) \/ X)) _VS_ c1(
        c1(c1(c1((z === y) <=> !(y === f(h(y, y))) \/ X)))
      ),
      $(forall(x, exists(y, c1(e2(X, P(y))) /\ R(y, f(y)))), c1 -> lambda(X, c1(c1(X))), e2 -> lambda(Seq(X, Y), X <=> Y), X -> (z === y), P -> lambda(x, !(x === f(h(x, y))) \/ X)) _VS_ forall(
        x,
        exists(y2, c1(c1((z === y) <=> !(y2 === f(h(y2, y))) \/ X)) /\ R(y2, f(y2)))
      ),
      $(exists(x, P(x) /\ X), c1 -> lambda(X, exists(y, Q(y) /\ X)), e2 -> lambda(Seq(X, Y), X <=> exists(x, P(x) /\ Y)), X -> (z === y), P -> lambda(x2, exists(y, R(x2, y) /\ P(x)))) _VS_ exists(
        x2,
        exists(y2, R(x2, y2) /\ P(x)) /\ (z === y)
      ),
      $(
        c1(e2(X, P(x))) /\ R(y, f(y)),
        c1 -> lambda(X, exists(y, Q(y) /\ X)),
        e2 -> lambda(Seq(X, Y), X <=> exists(x, P(x) /\ Y)),
        X -> (z === y),
        P -> lambda(x2, exists(y, R(x2, y) /\ P(x)))
      ) _VS_ (exists(y2, Q(y2) /\ ((z === y) <=> exists(x2, P(x2) /\ exists(y, R(x, y) /\ P(x))))) /\ R(y, f(y))),
      $(forall(x, P(x)), x1 -> f(x())) _VS_ forall(x, P(x)),
      $(
        forall(x, e2(c1(e2(X, P(x))) /\ R(y, f(y)), exists(x, P(x) /\ X))),
        c1 -> lambda(X, exists(y, Q(y) /\ X)),
        e2 -> lambda(Seq(X, Y), X <=> exists(x, P(x) /\ Y)),
        X -> (z === y),
        P -> lambda(x2, exists(y, R(x2, y) /\ P(x)))
      ) _VS_ forall(
        x3,
        exists(y2, Q(y2) /\ ((z === y) <=> exists(x2, P(x2) /\ exists(y2, R(x3, y2) /\ P(x))))) /\ R(y, f(y)) <=> exists(x2, P(x2) /\ exists(x2, exists(y2, R(x2, y2) /\ P(x)) /\ (z === y)))
      )
    )

  }

}
