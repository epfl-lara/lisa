package lisa.kernel.proof

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class RuleMembershipSuite extends AnyFunSuite:
  import Helpers.*
  private val x = Variable(Identifier("membership-x"), Ind)
  private val y = Variable(Identifier("membership-y"), Ind)
  private val a = Constant(Identifier("membership-a"), Ind)
  private val p = Constant(Identifier("membership-p"), Prop)
  private val q = Constant(Identifier("membership-q"), Prop)
  private val predicate = Constant(Identifier("membership-predicate"), Ind -> Prop)
  private val formulas = Vector(p, q, and(p)(q), and(q)(p), predicate(a), Lambda(x, predicate(x))(a), forall(Lambda(x, predicate(x))), forall(Lambda(y, predicate(y))))
  private val contexts = Vector(Set.empty[Expression], formulas.toSet) ++ formulas.map(Set(_)) ++ formulas.combinations(2).map(_.toSet)

  test("subset membership agrees with normalized containment on exact, beta, and quantified formulas"):
    for source <- contexts; target <- contexts do
      val normalized = target.map(simpleReducedForm)
      val expected = source.forall(f => normalized.contains(simpleReducedForm(f)))
      assert(source.subsetOfEq(target) == expected)

  test("pivot-exempt membership preserves normalized and OL fallbacks without accepting extras"):
    for source <- contexts; target <- contexts; pivot <- formulas do
      val normalized = target.map(simpleReducedForm)
      val expected = source.forall(f => normalized.contains(simpleReducedForm(f)) || isSame(f, pivot))
      assert(source.containedExcept(target, pivot) == expected)
