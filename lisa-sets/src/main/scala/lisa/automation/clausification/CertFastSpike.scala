package lisa.automation.clausification

import lisa.automation.clausification.Clausification.Problem
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.utils.K.{_, given}

/** Kernel-check harness for [[CertifiedFastClausifier]]: clausify with a `Sorry` refuter (so every *non-Sorry*
 *  clausification step is validated by the kernel) and print the judgement. */
object CertFastSpike:

  private def pv(i: Int): Variable = Variable(Identifier(s"p$i", 0), Prop)
  private val Q = Variable(Identifier("Q", 0), Ind >>: Prop)
  private def xv(i: Int): Variable = Variable(Identifier(s"x$i", 0), Ind)

  // Contract: the prover proper must conclude the EMPTY sequent `⊢` (see Clausification.certifyClausal).
  private def refuteWithSorry(problem: Problem): SCProof =
    SCProof(IndexedSeq(Sorry(Sequent(Set.empty, Set.empty))), problem.imports)

  private def check(name: String, phi: Expression): Unit =
    val problem = Problem(Seq(() |- phi), None)
    val proof = CertifiedFastClausifier.certifyClausal(problem, refuteWithSorry)
    val judge = checkSCProof(proof)
    println(s"=== $name ===")
    println(s"  formula: ${phi.repr}")
    println(s"  kernel valid: ${judge.isValid}")
    judge match
      case p: lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof =>
        println(s"  path: ${p.path}")
        println(s"  message: ${p.message}")
      case _ => ()

  def main(args: Array[String]): Unit =
    // (1) top-level nested Iff chain — naming with no enclosing binders.
    check("iff-chain-5", (1 to 5).map(pv).reduceRight((a, b) => a <=> b))
    // (2) the same chain under a universal — exercises the under-binder HO substitution.
    check("iff-chain-under-forall", forall(Lambda(xv(1), or((1 to 5).map(pv).reduceRight((a, b) => a <=> b))(Q(xv(1))))))
    // (3) an Iff whose child itself contains a quantifier — discharge instantiates d to a quantified formula.
    check("iff-with-quantified-child",
      ((forall(Lambda(xv(1), Q(xv(1)))) <=> pv(2)) <=> (pv(3) <=> pv(4))) <=> pv(5))
