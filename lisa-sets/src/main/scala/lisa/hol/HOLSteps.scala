package lisa.hol
import VarsAndFunctions.*
import lisa.fol.FOL as F
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.* 
import lisa.prooflib.ProofTacticLib.*
import lisa.automation.*

import lisa.maths.settheory.SetTheory.{singleton, app}

/**
  * Here we define and implement all the basic steps from HOL Light
  */
object HOLSteps extends lisa.HOL {
  import lisa.SetTheoryLibrary.*

  draft()
  
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
  val w = typedvar(A)
  val x = typedvar(A)
  val y = typedvar(A)
  val z = typedvar(A) 
  val eqRefl = Theorem((x =:= x)) {sorry}

  val eqTrans = Theorem( ((x =:= y),  (y =:= z))  |- (x =:= z) )  {sorry}


  /**
   *  ------------------
   *     |- t = t
   */
  object REFL extends ProofTactic {
    def apply(using proof: Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof{
      val typ = computeType(t)
      have(holeq(typ)*t*t) by Restate.from(eqRefl of (A := typ, x := t))
    }
  }

  /**
   *  |- s = t    |- t = u
   *  ---------------------
   *        |- s = u
   */
  object TRANS extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      val s1 = t1.statement
      val s2 = t2.statement
      (s1, s2) match {
        case (HOLSequent(left1, =:=(aa)*s*ta), HOLSequent(left2, =:=(ab)*tb*u) ) if ta == tb && aa == ab => //equality is too strict
          have((left1 ++ left2) |- (s =:= u)) by Tautology.from(eqTrans of (x := s, y := ta, z := u), t1, t2)


        case _ => 

          return proof.InvalidProofTactic(s"The facts should be of the form s =:= t and t =:= u")
      }

    }
  }

  

  val test1 = Theorem((w =:= x, x =:= y, y =:= z) |- (w =:=z)) {
    val a1 = assume(w =:= x)
    val a2 = assume(x =:= y)
    val a3 = assume(y =:= z)
    val s1 = have(TRANS(a1, a2))
    have(TRANS(s1, a3))
  }


/*
  /**
   *  |- f = g    |- x = y
   *  ---------------------
   *        |- f x = g y
   */
  object MK_COMB extends ProofTactic {
    def apply(using proof: Proof)(f: Term, x: Term): proof.ProofTacticJudgement = TacticSubproof{
      val typ = computeType(f)
      val typ2 = computeType(x)
      val f1 = proof.facts.head.statement
      val x1 = proof.facts.tail.head.statement
      if f1.right.size != 1 || f1.right.head != (f =:= x) then
        return proof.InvalidProofTactic(s"The first fact should $f =:= $x")
      else have(holeq(typ2)*f*x) by Restate.from(MK_COMB of (A := typ, B := typ2, f := f, x := x))
    }
  }
*/

}
