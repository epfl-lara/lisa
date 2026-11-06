package lisa.kernel.proof

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.*
import org.scalatest.funsuite.AnyFunSuite

class SequentFastPathSuite extends AnyFunSuite:
  private val p = Variable(Identifier("sequent-fast-p"), Prop)
  private val q = Variable(Identifier("sequent-fast-q"), Prop)
  private val contexts = Vector(Set.empty[Expression], Set(p), Set(q), Set(p, q), Set(and(p)(q)), Set(or(p)(q)))
  private val statements = for left <- contexts; right <- contexts yield Sequent(left, right)

  test("exact sequent equality and Weakening agree with their original OL predicates"):
    for from <- statements; to <- statements do
      assert(isSameSequent(from, to) == isSame(sequentToFormula(from), sequentToFormula(to)))
      val accepted = SCProofChecker.checkSingleSCStep(1, Weakening(to, 0), _ => from, 0).isValid
      assert(accepted == isImplyingSequent(from, to), s"$from -> $to")

  test("retain OL-only weakening, reject premise removal, and propagate sorry"):
    val source = Sequent(Set(p), Set.empty)
    val target = Sequent(Set(and(p)(q)), Set.empty)
    assert(!source.left.subsetOf(target.left))
    assert(SCProofChecker.checkSingleSCStep(1, Weakening(target, 0), _ => source, 0).isValid)
    assert(!SCProofChecker.checkSingleSCStep(1, Weakening(Sequent(Set.empty, Set.empty), 0), _ => source, 0).isValid)
    val widened = Sequent(Set(p, q), Set(q))
    val proof = SCProof(Sorry(source), Weakening(widened, 0))
    assert(SCProofChecker.checkSCProof(proof) match
      case SCProofCheckerJudgement.SCValidProof(_, sorry) => sorry
      case _ => false)
