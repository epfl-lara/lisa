package lisa.hol
import VarsAndFunctions.*
import lisa.fol.FOL as F
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.* 
import lisa.prooflib.ProofTacticLib.*
import lisa.automation.*

import lisa.maths.settheory.SetTheory.{singleton, app}
import ap.Prover.Proof
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.utils.KernelHelpers.checkProof

/**
  * Here we define and implement all the basic steps from HOL Light
  */
object HOLSteps extends lisa.HOL {
  import lisa.SetTheoryLibrary.*

  //draft()
  
  //REFL
  //_TRANS
  //MK_COMB
  //ABS
  //BETA
  //ETA
  //ASSUME
  //_EQ_MP
  //DEDUCT_ANTISYM_RULE
  //INST
  //INST_TYPE

  



  import lisa.hol.HOLTest.=:=

  val A = variable
  val B = variable
  val v = typedvar(B)
  val w = typedvar(A)
  val x = typedvar(A)
  val y = typedvar(A)
  val z = typedvar(A) 
  val e = typedvar(A |=> A)
  val f = typedvar(A |=> B)
  val g = typedvar(A |=> B)
  val h = typedvar(B |=> A)

  val p = typedvar(𝔹)
  val q = typedvar(𝔹)

  val eqCorrect = Theorem(((x::A), (y::A)) |- ((x =:= y)===One) <=> (x===y)) {sorry}
  val eqRefl = Theorem((x =:= x)) {sorry}

  val eqTrans = Theorem( ((x =:= y),  (y =:= z))  |- (x =:= z) )  {sorry}

  val funcUnique = Theorem((f :: (A |=> B), g :: (A |=> B), tforall(x, f*x === g*x)) |- (f === g)) {sorry}
  val funcUnique2 =  Lemma((f :: (A |=> B), g :: (A |=> B), tforall(x, f*x === g*x)) |- ((f =:= g) === One)) {
    have(thesis) by Substitution.ApplyRules(eqCorrect of (HOLSteps.x := f, HOLSteps.y := g, A := (A |=> B)))(funcUnique)
  }

  val propExt = Theorem((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- (p === q)) {sorry}

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
  object _TRANS extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      val s1 = t1.statement
      val s2 = t2.statement
      println("s1: " + s1)
      println("s2: " + s2)
      (s1, s2) match {
        case (HOLSequent(left1, =:=(aa)*s*ta), HOLSequent(left2, =:=(ab)*tb*u) ) => //equality is too strict
          if ta == tb then
            if aa == ab then
              println("eqTrans: " + (eqTrans of (x := s, y := ta, z := u)).statement)
              val r0 = have((s1.left ++ s2.left + (s::aa) + (ta :: aa) + (u :: aa) ) |- ((s =:= u) === One)) by Tautology.from(eqTrans of (x := s, y := ta, z := u), t1, t2)
              val r1 = have(Discharge(have(ProofType(s)))(r0))
              val r2 = have(Discharge(have(ProofType(ta)))(r1))
              have(Discharge(have(ProofType(u)))(r2))
            else 
              return proof.InvalidProofTactic(s"Types don't agree: $aa and $ab")
          else 
            return proof.InvalidProofTactic(s"Middle elements don't agree: $ta and $tb")

        case (HOLSequent(left1, right1), HOLSequent(left2, right2) ) => 
          return proof.InvalidProofTactic(s"The facts should have equalities")
        case _ => 
          s1 match 
            case HOLSequent(left1, right1) => 
              return proof.InvalidProofTactic(s"The second fact is not parsable as an HOL sequent")
            case _ =>
              return proof.InvalidProofTactic(s"The first fact is not parsable as an HOL sequent")

      }

    }
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


  /**
    *     |- t =:= u
    * ---------------------
    *  |- λx. t =:= λx. u
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
      t match
        case (l:Abstraction)*(r: TypedVar) if l.bound == r => 
          val b = l.BETA
          val s1 = have(b.statement) by Weakening(b) //l*r =:= l.body
          val ctx = computeContext(Set(l*r, l.body))
          ctx._1.foreach(a => assume(a))
          ctx._2.foreach(a => assume(a))
          val bt = have((r::r.typ) |- ((l*r =:= l.body) === One)) by Restate.from(s1)
          val ptlr = have(ProofType(l*r))
          val ptlb = have(ProofType(l.body))
          val bth = have((r::r.typ, l*r :: l.defin.outType, l.body :: l.defin.outType) |- (l*r === l.body)) by Substitution.ApplyRules(
            eqCorrect of (HOLSteps.x := l*r, HOLSteps.y := l.body, A := l.defin.outType)
          )(bt)
          have(Discharge(ptlr)(lastStep))
          have(Discharge(ptlb)(lastStep))



        case _ => 
          return proof.InvalidProofTactic(s"The term should be of the form (λx. t) x")
    }
  }


  // λ(x, t*x) === t
  object ETA_PRIM extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVar, t: Term): proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      if t.freeVariables.contains(x) then
      return proof.InvalidProofTactic(s"Variable $x is free in the term $t")
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
  // λ(x, t*x) =:= t
  object ETA extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVar, t: Term): proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      if t.freeVariables.contains(x) then
      return proof.InvalidProofTactic(s"Variable $x is free in the term $t")
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

  /**
    * ---------------
    *     t |- t
    */
  object ASSUME extends ProofTactic {
    def apply(using proof: Proof)(t:Term): proof.ProofTacticJudgement = TacticSubproof {
      val typ = computeType(t)
      if typ == 𝔹 then
        have(t |- t) by Restate
      else
        return proof.InvalidProofTactic(s"Term $t is not a boolean")
    }

  }


  /**
    *  |- t = u    |- t
    * -------------------
    *       |- u
    */
  object _EQ_MP extends ProofTactic {
    def apply(using proof: Proof)(eq: proof.Fact, p: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      if eq.statement.right.size != 1 then
        return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One")
      eq.statement.right.head match
        case (=:=(`𝔹`)*t*u) === One => 
          if p.statement.right.size != 1 then
            return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
          p.statement.right.head match
            case eqOne(`t`) =>
              eq.statement.left.foreach(f => assume(f))
              val h1 = have((t :: 𝔹, u :: 𝔹) |- t === u) by Substitution.ApplyRules(eqCorrect of (x := t, y := u, A := 𝔹))(eq)
              p.statement.left.foreach(f => assume(f))
              val h2 = have((t :: 𝔹, u :: 𝔹) |- (u === One)) by Substitution.ApplyRules(h1)(p)
              val pt = have(ProofType(t))
              val h3 = have(Discharge(pt)(h2))
              val h4 = have(Discharge(have(ProofType(u)))(h3))
    
            case _ =>
              return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
        case _ =>
          return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One ")
          
    }

  }

  /**
    *      A |- p   B |- q
    * -------------------------
    *   A - p, B - q |- p = q
    */
  object DEDUCT_ANTISYM_RULE extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      if t1.statement.right.size != 1 || t2.statement.right.size != 1 then
        return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
      val left1 = t1.statement.left
      val c1 = t1.statement.right.head
      val left2 = t2.statement.left
      val c2 = t2.statement.right.head
      (c1, c2) match 
        case (eqOne(p), eqOne(q)) =>
          (left1 - c2).foreach(f => assume(f))
          (left2 - c1).foreach(f => assume(f))
          val h1 = have(((p :: 𝔹): F.Formula, (q :: 𝔹): F.Formula) |- ((p=:=q) === One)) by Substitution.ApplyRules(
              eqCorrect of (x := p, y := q, A := 𝔹)
            )(propExt of (HOLSteps.p := p, HOLSteps.q := q))
          val h2 = have(Discharge(have(ProofType(p)))(h1))
          have(Discharge(have(ProofType(q)))(h2))

        
        case _ =>
          return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
        
    }

  }

  object INST extends ProofTactic {
    def apply(using proof: Proof)(inst: Seq[(TypedVar, Term)], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      /*
      prem.statement match
        case HOLSequent(left, right) =>
          have(HOLSequent(left.map(p => HOLSubst(p, x, t)), HOLSubst(right, x, t))) by Sorry
          */
      val r = prem.of(inst.map(_ := _): _*)
      have(r.statement) by Restate.from(r)

    }
      
        
  }

  object INST_TYPE extends ProofTactic {

    def apply(using proof: Proof)(x: F.Variable, t:Term, prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      val r = prem of (x := t)
      have(r.statement) by Restate.from(r)
    }

  }

  /*
  def HOLSubstType(t:Term, A:F.Variable, u:Term): Term = {
    t match
      case v: TypedVar if v.typ == A => TypedVar(v.id, u.typ)
  }
*/

  def HOLSubst(t:Term, x:TypedVar, u:Term): Term = {
    t match
      case v:TypedVar if v.id == x.id && v.typ == x.typ  => u
      case a:Abstraction => 
        if a.bound == x then a
        else λ(a.bound, HOLSubst(a.body, x, u))
      case a:AppliedFunction => HOLSubst(a.func, x, u)*HOLSubst(a.arg, x, u)
      case _ => t
  }

}
