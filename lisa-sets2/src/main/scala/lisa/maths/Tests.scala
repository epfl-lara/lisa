package lisa.maths
import lisa.automation.atp.Goeland
import lisa.utils.KernelHelpers.checkProof
import lisa.utils.tptp.*
import java.io.*
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SCProofCheckerJudgement.SCValidProof

object Tests extends lisa.Main {
  draft()

  val x = variable[Term]
  val y = variable[Term]
  val z = variable[Term]
  val P = variable[Term >>: Formula]

  val ppp = ProofParser.reconstructProof(new File("goeland/testEgg.p"))(using ProofParser.mapAtom, ProofParser.mapTerm, ProofParser.mapVariable)
  
  checkProof(ppp)
  
  

  /*
  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Goeland // ("goeland/Example.buveurs2_sol")
  }
    */
}