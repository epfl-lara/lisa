import lisa.automation.clausification.*
import lisa.automation.clausification.ClausificationStressTest
import lisa.kernel.proof.*
import lisa.kernel.proof.SequentCalculus.*

object SkTest {
  def main(args: Array[String]): Unit = {
    for (n <- Seq(2, 4, 6, 8)) {
      val p = ClausificationStressTest.skolemFamily(n)
      val proof = Clausification.certifyClausal(p, ClausificationStressTest.refuteClausalProblem)
      def count(pp: SCProof): (Int, Int) = {
        var leaves = 0; var subs = 0
        pp.steps.foreach {
          case SCSubproof(sp, _) => subs += 1; val (l, s) = count(sp); leaves += l; subs += s
          case _ => leaves += 1
        }
        (leaves, subs)
      }
      val (l, s) = count(proof)
      println(s"n=$n  leaves=$l  subproofs=$s  topLevelSteps=${proof.steps.size}")
    }
  }
}
