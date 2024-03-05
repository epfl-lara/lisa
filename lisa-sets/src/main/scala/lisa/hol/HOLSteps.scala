package lisa.hol
import VarsAndFunctions.*
import lisa.fol.FOL as F
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.* 
import lisa.prooflib.ProofTacticLib.*
import lisa.automation.*

import lisa.maths.settheory.SetTheory.{singleton, app}
import ap.Prover.Proof
import lisa.maths.settheory.types.TypeLib.B

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
  //ETA
  //ASSUME
  //EQ_MP
  //DEDUCT_ANTISYM_RULE
  //INST
  //INST_TYPE

  



  import lisa.hol.HOLTest.=:=

  val A = variable
  val B = variable
  val w = typedvar(A)
  val x = typedvar(A)
  val y = typedvar(A)
  val z = typedvar(A) 
  val f = typedvar(A |=> B)
  val g = typedvar(A |=> B)

  val eqCorrect = Theorem(((x::A), (y::A)) |- ((x =:= y)===One) <=> (x===y)) {sorry}
  val eqRefl = Theorem((x =:= x)) {sorry}

  val eqTrans = Theorem( ((x =:= y),  (y =:= z))  |- (x =:= z) )  {sorry}

  val funcUnique = Theorem((f :: (A |=> B), g :: (A |=> B), tforall(x, f*x === g*x)) |- (f === g)) {sorry}
  val funcUnique2 =  Lemma((f :: (A |=> B), g :: (A |=> B), tforall(x, f*x === g*x)) |- ((f =:= g) === One)) {
    have(thesis) by Substitution.ApplyRules(eqCorrect of (HOLSteps.x := f, HOLSteps.y := g, A := (A |=> B)))(funcUnique)
  }

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


  val test2 = Theorem((f =:= g, x =:= y) |- (f*x =:= g*y)) {
    val a1 = assume(f =:= g)
    val a2 = assume(x =:= y)
    have(MK_COMB(a1, a2))
  }

  /**
    *     |- t = u
    * ---------------------
    *  |- λx. t = λx. u
    * 
    */
  object ABS extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVar)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val s1 = prem.statement
      s1 match {
        case HOLSequent(left, =:=(typ1)*t*u) => 
          left.foreach(assume)
          val lt = λ(x, t)
          val lu = λ(x, u)
          val ctx = computeContext(Set(lt, lu))
          ctx._1.foreach(a => assume(a))
          ctx._2.foreach(a => assume(a))
          val typjudgt = {
            val j = ProofType(t)
            j match
              case j: ip.ValidProofTactic => have(j)
              case j: ip.InvalidProofTactic => return proof.InvalidProofTactic(s"Can't compute type judgement for $t: " + j.message)
          }
          val typjudgltx = {
            val j = ProofType(lt*x)
            j match
              case j: ip.ValidProofTactic => have(j)
              case j: ip.InvalidProofTactic => return proof.InvalidProofTactic(s"Can't compute type judgement for $lt: " + j.message)
          }
          val typjudgu = {
            val j = ProofType(u)
            j match
              case j: ip.ValidProofTactic => have(j)
              case j: ip.InvalidProofTactic => return proof.InvalidProofTactic(s"Can't compute type judgement for $u: " + j.message)
          }
          val typjudglux = {
            val j = ProofType(lu*x)
            j match
              case j: ip.ValidProofTactic => have(j)
              case j: ip.InvalidProofTactic => return proof.InvalidProofTactic(s"Can't compute type judgement for $lu: " + j.message)
          }
          val ltx_lux = have((x::x.typ) |- (lt*x === lu*x)) subproof { iip ?=>
            Seq(typjudgt, typjudgltx, typjudgu, typjudglux).foreach( a =>
              assume(a.statement.right.head)
              iip.addDischarge(a)
            )

            val s0 = have((x::x.typ) |- (t===u)) by Tautology.from(prem, eqCorrect of (HOLSteps.x := t, HOLSteps.y := u, A := typ1))
            val ltprop = assume(lt.defin.bodyProp)
            val luprop = assume(lu.defin.bodyProp)
            val bt1 = have(BETA(lt*x))
            val bt = have((x::x.typ) |- ((lt*x =:= t) === One)) by Restate.from(bt1)
            val bth = have((x::x.typ) |- (lt*x === t)) by Substitution.ApplyRules(eqCorrect of (HOLSteps.x := lt*x, HOLSteps.y := t, A := typ1))(bt)
            val btc = lastStep.statement // x::x.typ |- lt(a)...(z)(x) = t

            val bu1 = have(BETA(lu*x))
            val bu = have((x::x.typ) |- ((lu*x =:= u) === One)) by Restate.from(bu1)
            val buh = have((x::x.typ) |- (lu*x === u)) by Substitution.ApplyRules(eqCorrect of (HOLSteps.x := lu*x, HOLSteps.y := u, A := typ1))(bu)
            val buc = lastStep.statement // x::x.typ |- lt(a)...(z)(x) = u

            val s1 = have((x::x.typ) |- ((lt*x)===u)) by Substitution.ApplyRules(s0)(bth)
            val s2 = have((x::x.typ) |- ((lt*x)===(lu*x))) by Substitution.ApplyRules(buh)(s1)

          }
          val s2c = lastStep.statement.right.head // lt*x = lu*x
          val is2 = have((x::x.typ) ==> s2c) by Restate.from(lastStep)
          val qs2 = have(tforall(x, (lt*x)===(lu*x))) by RightForall(is2)
          ip.addDischarge(have(ProofType(lt)))
          ip.addDischarge(have(ProofType(lu)))
          have((lt:: (x.typ |=> typ1), lu:: (x.typ |=> typ1)) |- ((lt =:= lu) === One)) by Tautology.from(funcUnique2 of (f := lt, g := lu, HOLSteps.x := x, A := x.typ, B := typ1), qs2)


        case _ => 
          return proof.InvalidProofTactic(s"The fact should be of the form t =:= u")
      }
    }
  }
  /*
  val test_abs_1 = Theorem((y =:= z) |- (λ(x, y) =:= λ(x, z))) {
    assume(y =:= z)
    have(ABS(x)(lastStep))
  }

  val thm_abs_2 = Theorem(λ(x, λ(y, y)) =:= λ(x, λ(z, z))) {
    have(λ(y, y) =:= λ(z, z)) by Sorry
    have(ABS(x)(lastStep))
  }

  val thm_abs_3 = Theorem(λ(x, λ(y, x)) =:= λ(x, λ(z, x))) {
    have(λ(y, x) =:= λ(z, x)) by Sorry
    have(ABS(x)(lastStep))
  }

  val test_abs_4 = Theorem(λ(x, λ(y, f*x =:= g*(λ(z, y)*x))) =:= λ(x, λ(z, z =:= x))) {
    have(λ(y, f*x =:= g*(λ(z, y)*x)) =:= λ(z, z =:= x)) by Sorry
    have(ABS(x)(lastStep))
  }
*/
  object BETA extends ProofTactic {
    def apply(using proof: Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof{
      t match
        case (l:Abstraction)*(r: TypedVar) if l.bound == r => 
          val b = l.BETA
          have(b.statement) by Weakening(b)
        case _ => 
          return proof.InvalidProofTactic(s"The term should be of the form (λx. t) x")  
    }
  }

  object BETA_PRIM extends ProofTactic {
    def apply(using proof: Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      println("Entering BETA_PRIM")
      t match
        case (l:Abstraction)*(r: TypedVar) if l.bound == r => 
          val b = l.BETA
          val s1 = have(b.statement) by Weakening(b) //l*r =:= l.body
          val ctx = computeContext(Set(l*r, l.body))
          ctx._1.foreach(a => assume(a))
          ctx._2.foreach(a => assume(a))
          val bt = have((r::r.typ) |- ((l*r =:= l.body) === One)) by Restate.from(s1)
          val ptlr = have(ProofType(l*r))
          println("ptlr.statement: " + ptlr.statement)
          val ptlb = have(ProofType(l.body))
          println("ptlb.statement: " + ptlb.statement)
          val bth = have((r::r.typ, l*r :: l.defin.outType, l.body :: l.defin.outType) |- (l*r === l.body)) by Substitution.ApplyRules(
            eqCorrect of (HOLSteps.x := l*r, HOLSteps.y := l.body, A := l.defin.outType)
          )(bt)
          have(Discharge(ptlr)(lastStep))
          have(Discharge(ptlb)(lastStep))



        case _ => 
          return proof.InvalidProofTactic(s"The term should be of the form (λx. t) x")  
      println("Exiting BETA_PRIM")
    }
  }
/*
  val test_beta_1 = Theorem( λ(x, x)*x =:= x) {
    have(BETA(λ(x, x)*x))
  }

  val test_beta_2 = Theorem( λ(x, x)*x =:= (x)) {
    have(BETA(λ(x, x)*x))
  }
  
  val test_beta_3 = Theorem( λ(x, y)*x =:= (y)) {
    have(BETA(λ(x, y)*x))
  }
  
  val test_beta_4 = Theorem( λ(x, x =:= x)*x =:= (x =:= x)) {
    have(BETA(λ(x, x =:= x)*x))
  }
  
  val test_beta_5 = Theorem( λ(x, x =:= y)*x =:= (x =:= y)) {
    have(BETA(λ(x, x =:= y)*x))
  }
  
  val test_beta_6 = Theorem( λ(x, λ(y, x))*x =:= λ(y, x)) {
    have(BETA(λ(x, λ(y, x))*x))
  }
  
  val test_beta_7 = Theorem( λ(x, λ(y, y))*x =:= λ(y, y)) {
    have(BETA(λ(x, λ(y, y))*x))
  }

  val test_beta_8 = Theorem( λ(x, λ(y, x =:= y))*x =:= λ(y, x =:= y)) {
    have(BETA(λ(x, λ(y, x =:= y))*x))
  }


  val test_beta_9 = Theorem( λ(x, λ(y, λ(z, x)))*x =:= λ(y, λ(z, x))) {
    have(BETA(λ(x, λ(y, λ(z, x)))*x))
  }

  val test_beta_10 = Theorem( λ(x, λ(y, λ(z, y) =:= λ(w, x)))*x =:= λ(y, λ(z, y) =:= λ(w, x))) {
    have(BETA(λ(x, λ(y, λ(z, y) =:= λ(w, x)))*x))
  }
*/
  // λ(x, t*x) = t
  object ETA_PRIM extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVar, t: Term): proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      val lxtx = λ(x, t*x)
      val ctx = computeContext(Set(lxtx, t))
      ctx._1.foreach(a => assume(a))
      ctx._2.foreach(a => assume(a))
      have(BETA_PRIM(lxtx*x))
      thenHave((x :: x.typ) ==> (lxtx*x === t*x)) by Restate.from
      thenHave(tforall(x, lxtx*x === t*x)) by RightForall
      val r1 = have((lxtx:: lxtx.typ, t::lxtx.typ) |- (lxtx === t)) by Tautology.from(
        funcUnique of (f := lxtx, g := t, A := x.typ, B := lxtx.defin.outType),
        lastStep
      )
      val r2 = have((t::lxtx.typ) |- (lxtx === t)) by Cut(have(ProofType(lxtx)), r1)
      have((lxtx === t)) by Cut(have(ProofType(t)), r2)
    }
  }

  object ETA extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVar, t: Term): proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      val lxtx = λ(x, t*x)
      val ctx = computeContext(Set(lxtx, t))
      ctx._1.foreach(a => assume(a))
      ctx._2.foreach(a => assume(a))
      have(BETA_PRIM(lxtx*x))
      thenHave((x :: x.typ) ==> (lxtx*x === t*x)) by Restate.from
      thenHave(tforall(x, lxtx*x === t*x)) by RightForall
      val r1 = have((lxtx:: lxtx.typ, t::lxtx.typ) |- ((lxtx =:= t) === One)) by Tautology.from(
        funcUnique2 of (f := lxtx, g := t, A := x.typ, B := lxtx.defin.outType),
        lastStep
      )

      val r2 = have((t::lxtx.typ) |- ((lxtx =:= t) === One)) by Cut(have(ProofType(lxtx)), r1)
      have((lxtx =:= t) === One) by Cut(have(ProofType(t)), r2)

    }
  }

  val test_eta_1 = Theorem(λ(x, f*x) =:= f) {
    have(ETA(x, f))
  }
  val test_eta_prim_1 = Theorem(withCTX(λ(x, f*x) === f)) {
    have(ETA_PRIM(x, f))
    println("lastStep.statement: " + lastStep.statement)
    println("thesis            : " + thesis)
  }

  val f2 = λ(y, y)
  val test_eta_2 = Theorem(λ(x, f2*x) =:= f2) {
    have(ETA(x, f2))
  }
  val test_eta_prim_2 = Theorem(withCTX(λ(x, f2*x) === f2)) {
    have(ETA_PRIM(x, f2))
  }

  val f3 = λ(y, y =:= x) // ??? require(!t.freeVariables.contains(x))
  val test_eta_3 = Theorem(λ(x, f3*x) =:= f3) {
    have(ETA(x, f3))
  }
  val test_eta_prim_3 = Theorem(withCTX(λ(x, f3*x) === f3)) {
    have(ETA_PRIM(x, f3))
  }

  val f4 = λ(y, λ(z, f*y))
  val test_eta_4 = Theorem(λ(x, f4*x) =:= f4) {
    have(ETA(x, f4))
  }
  val test_eta_prim_4 = Theorem(withCTX(λ(x, f4*x) === f4)) {
    have(ETA_PRIM(x, f4))
  }

  val f5 = f2
  val test_eta_5 = Theorem(λ(y, f5*y) =:= f5) {
    have(ETA(y, f5))
  }
  val test_eta_prim_5 = Theorem(withCTX(λ(y, f5*y) === f5)) {
    have(ETA_PRIM(y, f5))
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
