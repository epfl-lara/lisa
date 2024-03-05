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

  //draft()
  
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

  val eqCorrect = Theorem(((x::A), (y::A)) |- ((x =:= y)===One) <=> (x===y)) {sorry}
  val eqRefl = Theorem((x =:= x)) {sorry}

  val eqTrans = Theorem( ((x =:= y),  (y =:= z))  |- (x =:= z) )  {sorry}


  /**
   *  ------------------
   *     |- t = t
   */
  object REFL extends ProofTactic {
    def apply(using proof: Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof{
      val s1 = have(ProofType(t)) //t::A
      val typ = s1.statement.right.head.asInstanceOf[TypeAssignment[Term]].typ
      have(holeq(typ)*t*t) by Tautology.from(eqRefl of (x := t, A := typ), s1)
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



  /**
   *  |- f = g    |- x = y
   *  ---------------------
   *        |- f x = g y
   */
  object MK_COMB extends ProofTactic {
    def apply(using proof: Proof)(f1: proof.Fact, f2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof {
      val fg = f1.statement
      val xy = f2.statement
      (fg, xy) match {
        case (HOLSequent(left1, =:=(typ1)*f*g), HOLSequent(left2, =:=(typ2)*x*y) )  => //equality is too strict
        typ1 match {
          case |=>(`typ2`, b) => 
            val s1 = have(REFL(f*x))
            val s2 = have((f :: typ1, g::typ1) |- (f===g)) by Tautology.from(f1, eqCorrect of (HOLSteps.x := f, HOLSteps.y := g, A := typ1))
            val s3 = have((x :: typ2, y::typ2) |- (x===y)) by Tautology.from(f2, eqCorrect of (HOLSteps.x := x, HOLSteps.y := y, A := typ2))
            val s4 = have(f*x =:= f*y) by Substitution.ApplyRules(s3)(s1)
            val s5 = have(f*x =:= g*y) by Substitution.ApplyRules(s2)(s4)

          case _ => 
            return proof.InvalidProofTactic(s"Types don't agree: fun types are $typ1 and arg types are $typ2")
        }
        case _ => 
          return proof.InvalidProofTactic(s"The facts should be of the form f =:= g and x =:= y")
      }
    }
  }

  val f = typedvar(A |=> 𝔹)
  val g = typedvar(A |=> 𝔹)
  val test2 = Theorem((f =:= g, x =:= y) |- (f*x =:= g*y)) {
    val a1 = assume(f =:= g)
    val a2 = assume(x =:= y)
    have(MK_COMB(a1, a2))
  }

  object ABS extends ProofTactic {

  }

  object BETA extends ProofTactic {
    def apply(using proof: Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof{
      t match
        case (l:Abstraction)*(r: TypedVar) if l.bound == r => 
          have(l.BETA)
        case _ => 
          return proof.InvalidProofTactic(s"The term should be of the form (λx. t) x")  
      
    }

  }

  val test5 = Theorem( λ(x, x)*x =:= x) {
    have(BETA(λ(x, x)*x))
  }

  val test6 = Theorem( λ(x, x)*x =:= (x)) {
    have(BETA(λ(x, x)*x))
  }
  
  val test7 = Theorem( λ(x, y)*x =:= (y)) {
    have(BETA(λ(x, y)*x))
  }
  
  val test8 = Theorem( λ(x, x =:= x)*x =:= (x =:= x)) {
    have(BETA(λ(x, x =:= x)*x))
  }
  
  val test9 = Theorem( λ(x, x =:= y)*x =:= (x =:= y)) {
    have(BETA(λ(x, x =:= y)*x))
  }
  
  val test10 = Theorem( λ(x, λ(y, x))*x =:= λ(y, x)) {
    have(BETA(λ(x, λ(y, x))*x))
  }
  
  val test11 = Theorem( λ(x, λ(y, y))*x =:= λ(y, y)) {
    have(BETA(λ(x, λ(y, y))*x))
  }

  val test12 = Theorem( λ(x, λ(y, x =:= y))*x =:= λ(y, x =:= y)) {
    have(BETA(λ(x, λ(y, x =:= y))*x))
  }


  val test13 = Theorem( λ(x, λ(y, λ(z, x)))*x =:= λ(y, λ(z, x))) {
    have(BETA(λ(x, λ(y, λ(z, x)))*x))
  }

  val test14 = Theorem( λ(x, λ(y, λ(z, y) =:= λ(w, x)))*x =:= λ(y, λ(z, y) =:= λ(w, x))) {
    have(BETA(λ(x, λ(y, λ(z, y) =:= λ(w, x)))*x))
  }

  object ASSUME extends ProofTactic {

  }

  object EQ_MP extends ProofTactic {

  }

  object DEDUCT_ANTISYM_RULE extends ProofTactic {

  }

  object INST extends ProofTactic {

  }

  object INST_TYPE extends ProofTactic {

  }

}
