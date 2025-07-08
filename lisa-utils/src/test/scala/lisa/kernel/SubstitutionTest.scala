package lisa.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory._
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus._
import lisa.utils.KernelHelpers.{_, given}
import org.scalatest.compatible.Assertion
import org.scalatest.funsuite.AnyFunSuite

/**
 * Extensive tests for the file lisa.kernel.Substitution
 */
class SubstitutionTest extends AnyFunSuite {
  private val x = variable
  private val x1 = variable
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
  case class $(t: Expression, m: (Variable, Expression)*) {
    inline infix def _VS_(t2: Expression): Assertion = {
      assert(isSame(substituteVariables(t, m.toMap).betaNormalForm, t2), "\n - " + substituteVariables(t, m.toMap).repr + " didn't match " + t2.repr)
    }
  }
  test("First Order Substitutions") {

    val cases: List[Assertion] = List(
      $(x, x -> x) _VS_ x,
      $(x, y -> y) _VS_ x,
      $(x, x -> y) _VS_ y,
      $(x, y -> z, x -> y) _VS_ y,
      $(x, g -> lambda(y, f(y))) _VS_ x,
      $(f(x), x -> y) _VS_ f(y),
      $(f(f(h(x, y))), x -> y) _VS_ f(f(h(y, y))),
      $(f(f(h(x, y))), x -> z) _VS_ f(f(h(z, y))),
      $(f(f(h(x, y))), x -> z, z -> x) _VS_ f(f(h(z, y))),
      $(f(f(h(x, y))), x -> y, y -> x) _VS_ f(f(h(y, x))),
      $(Q(x), x -> x) _VS_ Q(x),
      $(Q(x), y -> y) _VS_ Q(x),
      $(c1(c1(Q(x))), x -> y) _VS_ c1(c1(Q(y))),
      $(Q(f(f(h(x, y)))), x -> y) _VS_ Q(f(f(h(y, y)))),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z) _VS_ Q(f(f(h(z, y)))) /\ R(z, f(y)),
      $(forall(x, R(x, y)), x -> z) _VS_ forall(x, R(x, y)),
      $(forall(x, R(x, y)), y -> z) _VS_ forall(x, R(x, z)),
      $(forall(x, P(x)), x1 -> f(x)) _VS_ forall(x, P(x)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> z, x -> y) _VS_ forall(x, R(x, z)) /\ P(h(y, z)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> x) _VS_ forall(y, R(y, x)) /\ P(h(x, x)),
      $(X, X -> X) _VS_ X,
      $(X, Y -> Y) _VS_ X,
      $(X, X -> Y) _VS_ Y,
      $(X, Y -> Z, X -> Y) _VS_ Y,
      $(c1(X), X -> Y) _VS_ c1(Y),
      $(c1(c1(e2(X, Y))), X -> Y) _VS_ c1(c1(e2(Y, Y))),
      $(c1(c1(e2(X, Y))), X -> Z) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Z, Z -> X) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Y, Y -> X) _VS_ c1(c1(e2(Y, X))),
      $(Q(x), x -> x) _VS_ Q(x),
      $(Q(x), y -> y) _VS_ Q(x),
      $(c1(c1(Q(x))), x -> y) _VS_ c1(c1(Q(y))),
      $(Q(f(f(h(x, y)))), x -> y) _VS_ Q(f(f(h(y, y)))),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z) _VS_ Q(f(f(h(z, y)))) /\ R(z, f(y)),
      $(forall(x, R(x, y)), x -> z) _VS_ forall(x, R(x, y)),
      $(forall(x, R(x, y)), y -> z) _VS_ forall(x, R(x, z)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> z, x -> y) _VS_ forall(x, R(x, z)) /\ P(h(y, z)),
      $(forall(x, R(x, y)) /\ P(h(x, y)), y -> x) _VS_ forall(y, R(y, x)) /\ P(h(x, x)),
      $(X, X -> X) _VS_ X,
      $(X, Y -> Y) _VS_ X,
      $(X, X -> Y) _VS_ Y,
      $(X, Y -> Z, X -> Y) _VS_ Y,
      $(c1(X), X -> Y) _VS_ c1(Y),
      $(c1(c1(e2(X, Y))), X -> Y) _VS_ c1(c1(e2(Y, Y))),
      $(c1(c1(e2(X, Y))), X -> Z) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Z, Z -> X) _VS_ c1(c1(e2(Z, Y))),
      $(c1(c1(e2(X, Y))), X -> Y, Y -> X) _VS_ c1(c1(e2(Y, X))),
      $(c1(c1(e2(X, Y))), Z -> Y) _VS_ c1(c1(e2(X, Y))),
      $(c1(c1(e2(X, Y))), Z -> Y) _VS_ c1(c1(e2(X, Y)))
    )
  }

  test("Higher Order Substitutions, with beta normalization") {

    val cases: List[Assertion] = List(
      $(f(f(h(x, y))), z -> y, g -> lambda(x, f(h(y, x)))) _VS_ f(f(h(x, y))),
      $(f(f(h(x, y))), f -> lambda(x, x)) _VS_ h(x, y),
      $(f(f(h(x, y))), f -> lambda(x, y)) _VS_ y,
      $(f(f(h(x, y))), f -> lambda(x, f(f(x)))) _VS_ f(f(f(f(h(x, y))))),
      $(f(f(h(x, y))), f -> lambda(x, f(f(x))), h -> lambda(Seq(x, z), h(f(x), h(g(z), x)))) _VS_ f(f(f(f(h(f(x), h(g(y), x)))))),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z, h -> lambda(Seq(x, z), g(h(z, y)))) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, f(y)),
      $(R(x, h(f(z), y)), x -> z, h -> lambda(Seq(x, z), g(h(z, y))), z -> y) _VS_ R(z, g(h(y, y))),
      $(Q(f(f(h(x, y)))) /\ R(x, h(y, f(z))), x -> z, h -> lambda(Seq(x, z), g(h(z, y))), z -> y) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, g(h(f(y), y))),
      $(R(x, f(y)), R -> lambda(Seq(z, y), P(z) /\ Q(y))) _VS_ P(x) /\ Q(f(y)),
      $(R(x, f(y)) /\ R(z, z), R -> lambda(Seq(z, y), P(z) /\ Q(y))) _VS_ (P(x) /\ Q(f(y))) /\ (P(z) /\ Q(z)),
      $(forall(y, R(x, f(y))), R -> lambda(Seq(x, z), (x === z) /\ P(f(y)))) _VS_ forall(y2, (x === f(y2)) /\ P(f(y))),
      $(c1(P(x)), c1 -> lambda(X, !X)) _VS_ !P(x),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, X)) _VS_ e2(X, P(y)),
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, Y)) _VS_ Y,
      $(c1(c1(e2(X, P(y)))), c1 -> lambda(X, c1(c1(X)))) _VS_ c1(c1(c1(c1(e2(X, P(y)))))),
      $(Q(f(f(h(x, y)))) /\ R(x, f(y)), x -> z, h -> lambda(Seq(x, z), g(h(z, y)))) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, f(y)),
      $(R(x, h(f(z), y)), x -> z, h -> lambda(Seq(x, z), g(h(z, y))), z -> y) _VS_ R(z, g(h(y, y))),
      $(Q(f(f(h(x, y)))) /\ R(x, h(y, f(z))), x -> z, h -> lambda(Seq(x, z), g(h(z, y))), z -> y) _VS_ Q(f(f(g(h(y, y))))) /\ R(z, g(h(f(y), y))),
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
      $(forall(x, P(x)), x1 -> f(x)) _VS_ forall(x, P(x)),
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
