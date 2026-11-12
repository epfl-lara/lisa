package lisa.kernel.proof

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus._
import org.scalatest.funsuite.AnyFunSuite

class ContainmentParitySuite extends AnyFunSuite:
  private val x = Variable(Identifier("membership-x"), Ind)
  private val y = Variable(Identifier("membership-y"), Ind)
  private val a = Constant(Identifier("membership-a"), Ind)
  private val p = Constant(Identifier("membership-p"), Prop)
  private val q = Constant(Identifier("membership-q"), Prop)
  private val predicate = Constant(Identifier("membership-predicate"), Ind -> Prop)
  private val formulas = Vector(p, q, and(p)(q), and(q)(p), predicate(a), Lambda(x, predicate(x))(a), forall(Lambda(x, predicate(x))), forall(Lambda(y, predicate(y))))
  private val contexts = Vector(Set.empty[Expression], formulas.toSet) ++ formulas.map(Set(_)) ++ formulas.combinations(2).map(_.toSet)
  private val empty = Sequent(Set.empty, Set.empty)

  private def accepts(step: SCProofStep, premises: Seq[Sequent]): Boolean =
    SCProofChecker.checkSingleSCStep(premises.size, step, premises.apply, 0).isValid

  test("subset shortcuts agree with normalized containment through Cut"):
    for source <- contexts; target <- contexts do
      val normalized = target.map(simpleReducedForm)
      val expected = source.forall(f => normalized.contains(simpleReducedForm(f)))
      val conclusion = Sequent(target, Set.empty)
      assert(accepts(Cut(conclusion, 0, 1, p), Seq(Sequent(source, Set.empty), empty)) == expected)

  test("pivot shortcuts retain normalized and OL fallbacks without accepting extra formulas"):
    for source <- contexts; target <- contexts; pivot <- formulas do
      val normalized = target.map(simpleReducedForm)
      val expected = source.forall(f => normalized.contains(simpleReducedForm(f)) || isSame(f, pivot))
      val conclusion = Sequent(Set.empty, target)
      assert(accepts(Cut(conclusion, 0, 1, pivot), Seq(Sequent(Set.empty, source), empty)) == expected)
