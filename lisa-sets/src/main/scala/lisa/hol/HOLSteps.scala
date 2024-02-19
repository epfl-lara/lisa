package lisa.hol
import VarsAndFunctions.*
import lisa.fol.FOL as F
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.* 
import lisa.prooflib.ProofTacticLib.*
import lisa.automation.*

/**
  * Here we define and implement all the basic steps from HOL Light
  */
object HOLSteps extends lisa.HOL {
  import lisa.SetTheoryLibrary.*
  
  //REFL
  //TRANS
  //MK_COMB
  //ABS
  //BETA
  //ASSUME
  //EQ_MP
  //DEDUCT_ANTISYM_RULE
  //INST
  //INST_TYPE
  

  import lisa.hol.HOLTest.=:=

  val A = variable
  val x = typedvar(A)
  val eqRefl = Axiom(F.forall(A, tforall(x, x.=:=(A)(x) === One)))


  object REFL extends ProofTactic {

    def apply(using proof: Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof{
      have(t.=:=(computeType(t))(t)) by Tautology.from(eqRefl)
    }
  }
}
