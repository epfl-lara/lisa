package lisa.automation.clausification

import lisa.automation.clausification.Clausification.Problem
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.utils.K.{_, given}

/** Reproducer for the original combo failure:
  *   ∀x₁∃y₁ ∀x₂∃y₂. ((p₁ ∧ p₂) ∨ R(x₂, y₂))
  * where the Tseitin connector `(p₁ ∧ p₂)` syntactically appears inside
  * the ε-Skolem-bound subterm produced by Skolemization. */
object ComboRepro {

  private val R  = Variable(Identifier("R", 0), Ind >>: (Ind >>: Prop))
  private def xv(i: Int): Variable = Variable(Identifier("x", i), Ind)
  private def yv(i: Int): Variable = Variable(Identifier("y", i), Ind)
  private def pv(i: Int): Variable = Variable(Identifier("p", i), Prop)

  private def refuteWithSorry(problem: Problem): SCProof = {
    val clauses = problem.hypotheses.map(_.right.head)
    SCProof(IndexedSeq(Sorry(Sequent(clauses.toSet, Set.empty))), problem.imports)
  }

  def comboFamily(n: Int): Problem = {
    require(n >= 1)
    val xn = xv(n); val yn = yv(n)
    val inner = R(xn)(yn)
    val shell = or(and(pv(1))(pv(2)))(inner)
    def wrap(i: Int): Expression =
      val body = if (i == n) shell else wrap(i + 1)
      forall(Lambda(xv(i), exists(Lambda(yv(i), body))))
    Problem(Seq(() |- wrap(1)), None)
  }

  def main(args: Array[String]): Unit = {
    val n = args.headOption.map(_.toInt).getOrElse(2)
    val problem = comboFamily(n)
    println(s"=== Combo problem n=$n ===")
    problem.hypotheses.foreach(s => println(s.repr))
    val proof = Clausification.certifyClausal(problem, refuteWithSorry)
    val judge = checkSCProof(proof)
    println(s"\n=== Judgement ===")
    println(judge.repr)
  }
}
