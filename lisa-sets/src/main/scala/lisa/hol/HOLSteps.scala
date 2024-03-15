package lisa.hol
import VarsAndFunctions.*
import lisa.fol.FOL as F
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.* 
import lisa.prooflib.ProofTacticLib.*
import lisa.automation.*

import lisa.maths.settheory.SetTheory.{singleton, app}
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.utils.KernelHelpers.checkProof
import lisa.fol.FOLHelpers.freshVariable
import lisa.utils.Serialization.instSchema
import lisa.prooflib.BasicStepTactic
import lisa.prooflib.SimpleDeducedSteps.Discharge
import lisa.hol.VarsAndFunctions.computeType
import lisa.automation.Tableau.pr
import lisa.maths.settheory.SetTheory.definition
import lisa.maths.settheory.SetTheory.singletonNonEmpty

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
  val r = typedvar(𝔹)

  val eqCorrect = Theorem((x::A, y::A) |- ((x =:= y)===One) <=> (x===y)) {
    have(thesis) by Restate.from(eqDefin)
  }
  val eqRefl = Theorem((x =:= x)) {
    have(x::A |- (x === x)) by Restate
    thenHave(x =:= x) by Substitution.ApplyRules(eqCorrect of (HOLSteps.y := x))

  }

  val eqTrans = Theorem( ((x =:= y),  (y =:= z))  |- (x =:= z) )  {
    have((x::A, y::A, z::A, x === y, y === z)|- (x === y)) by Restate
    thenHave((x::A, y::A, z::A, x === y, y === z)|- (x === z)) by Substitution.ApplyRules(y === z)
    thenHave(((x::A, y::A, z::A, eqOne(x =:= y), y === z)|- (x === z))) by Substitution.ApplyRules(eqCorrect)
    thenHave(((x::A, y::A, z::A, eqOne(x =:= y), eqOne(y =:= z))|- (x === z))) by Substitution.ApplyRules(eqCorrect of (x := y, y := z))
    thenHave(((x::A, y::A, z::A, eqOne(x =:= y), eqOne(y =:= z))|- eqOne(x =:= z))) by Substitution.ApplyRules(eqCorrect of (y := z))
  }

  val funcUnique = Theorem((f :: (A |=> B), g :: (A |=> B), tforall(x, f*x === g*x)) |- (f === g)) {have(thesis) by Restate.from(functionalExtentionality)}
  val funcUnique2 =  Lemma((f :: (A |=> B), g :: (A |=> B), tforall(x, f*x === g*x)) |- ((f =:= g) === One)) {
    have(thesis) by Substitution.ApplyRules(eqCorrect of (HOLSteps.x := f, HOLSteps.y := g, A := (A |=> B)))(funcUnique)
  }

  val Bdef = Theorem((x ∈ 𝔹) |- ((x === Zero) \/ (x === One))) {
    val s1 = have    ((x ∈ unorderedPair(∅, singleton(∅))) |- ((x === ∅ )\/ (x === singleton(∅)))) by Weakening(pairAxiom of (z := x, x := ∅ , y := singleton(∅)))
    val beq = have(unorderedPair(∅, singleton(∅)) === 𝔹) by Weakening(𝔹.definition of 𝔹)
    val s2 = have((x ∈ 𝔹) |- ((x === ∅) \/ (x === singleton(∅)))) by Substitution.ApplyRules(beq)(s1)
    val zeq = have(∅ === Zero) by Weakening(Zero.definition of Zero)
    val s3 = have((x ∈ 𝔹) |- ((x === Zero) \/ (x === singleton(∅)))) by Substitution.ApplyRules(zeq)(s2)
    val oeq = have(singleton(∅) === One) by Weakening(One.definition of One)
    have((x ∈ 𝔹) |- ((x === Zero) \/ (x === One))) by Substitution.ApplyRules(oeq)(s3)
  }

  val propExt = Theorem((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- (p === q)) {

    val h2 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (p === One)) by Restate
    val h3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (q === One)) by Restate
    val h4 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (p === q)) by Substitution.ApplyRules(h3)(h2)

    val neq = have ((p === Zero, p === One )|- ()) subproof {
      val zeq = have(∅ === Zero) by Weakening(Zero.definition of Zero)
      val oeq = have(singleton(∅) === One) by Weakening(One.definition of One)
      have(∅ ∈ singleton(∅)) by Weakening(pairAxiom of (x:= ∅, y := ∅, z := ∅))
      have((∅ === singleton(∅)) |- ()) by Restate.from(singletonNonEmpty of (x:= ∅))

      thenHave ((p === singleton(∅), p === ∅) |- ()) by Substitution.ApplyRules(p === ∅)
      thenHave ((p === singleton(∅), p === Zero) |- ()) by Substitution.ApplyRules(zeq)
      thenHave ((p === One, p === Zero) |- ()) by Substitution.ApplyRules(oeq)
    }
    val i1 = have((p :: 𝔹  |- (!(p === One)) <=> (p === Zero))) by Tautology.from(Bdef of ( x:= p), neq)
    val i2 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- !(q === One) <=> !(p === One)) by Tautology
    val i3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- (q === Zero) <=> (p === Zero)) by Tautology.from(i2, i1, i1 of (p:=q))

    val j2 = have    ((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- p === Zero) by Tautology.from(Bdef of (x := p))
    val j3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- q === Zero) by Tautology.from(lastStep)
    val j4 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- (p === q)) by Substitution.ApplyRules(j3)(j2)

    have(thesis) by Tautology.from(j4, i3, h4)

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
  object _TRANS extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      val s1 = t1.statement
      val s2 = t2.statement
      (s1, s2) match {
        case (HOLSequent(left1, =:=(aa)*s*ta), HOLSequent(left2, =:=(ab)*tb*u) ) => //equality is too strict
          if ta == tb then
            if aa == ab then
              val r0 = have((s1.left ++ s2.left + (s::aa) + (ta :: aa) + (u :: aa) ) |- ((s =:= u) === One)) by Tautology.from(eqTrans of (x := s, y := ta, z := u), t1, t2)
              val r1 = have(Discharge(have(ProofType(s)))(r0))
              val r2 = have(Discharge(have(ProofType(ta)))(r1))
              val r3 = have(Discharge(have(ProofType(u)))(r2))
              have(Clean.all(r3))
              
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
            (f1.statement.left ++ f2.statement.left).foreach(assume(_))
            val vx = typedvar(computeType(x))
            val vf = typedvar(computeType(f))
            val s1 = have(REFL(f*x))
            val s2 = have((f :: typ1, g::typ1) |- (f===g)) by Tautology.from(f1, eqCorrect of (HOLSteps.x := f, HOLSteps.y := g, A := typ1))
            val s3 = have((x :: typ2, y::typ2) |- (x===y)) by Tautology.from(f2, eqCorrect of (HOLSteps.x := x, HOLSteps.y := y, A := typ2))
            val s4 = have((x === y) |- (f*x =:= f*y) === One) by RightSubstEq.withParametersSimple(List((x, y)), F.lambda(vx, f*x =:= f*vx))(s1)
            val s5 = have(((x === y), (f === g)) |- (f*x =:= g*y) === One) by RightSubstEq.withParametersSimple(List((f, g)), F.lambda(vf, f*x =:= vf*y))(s4)
            val s6 = have((x :: typ2, y::typ2, (f === g)) |- (f*x =:= g*y) === One) by Cut(s3, s5)
            val s7 = have((x :: typ2, y::typ2, f :: typ1, g::typ1) |- (f*x =:= g*y) === One) by Cut(s2, s6)
            val d1 = have( Discharge(have(ProofType(x)))(s7) )
            val d2 = have( Discharge(have(ProofType(y)))(d1) )
            val d3 = have( Discharge(have(ProofType(f)))(d2) )
            val d4 = have( Discharge(have(ProofType(g)))(d3) )
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
          (s1.left - (x :: x.typ)).foreach(assume(_))
          val lt = λ(x, t)
          val lu = λ(x, u)
          val lctx12 = computeContext(Set(lt, lu))
          val lctx = lctx12._1 ++ lctx12._2
          lctx.foreach(a => 
            assume(a))
          val typjudgt = have(ProofType(t))

          val typjudgltx = have(ProofType(lt*x))

          val typjudgu = have(ProofType(u))

          val typjudglux = have(ProofType(lu*x))


          val ctx12 = computeContext(Set(t, u))
          val ctx = ctx12._1 ++ ctx12._2
          (ctx - (x:: x.typ)).foreach(a => assume(a))
          val ltx_lux = have((x::x.typ) |- (lt*x === lu*x)) subproof { iip ?=>
            Seq(typjudgt, typjudgltx, typjudgu, typjudglux).foreach( a =>
              assume(a.statement.right.head)
              iip.addDischarge(a)
            )
            assume(x :: x.typ)
            
            val ltprop = assume(lt.defin.bodyProp)
            val luprop = assume(lu.defin.bodyProp)
            val bt1 = have(BETA(lt*x))
            val bt = have((x :: x.typ) |- ((lt*x =:= t) === One)) by Weakening(bt1)
            val bth = {
              val phi = F.formulaVariable
              val sl = (lt*x =:= t) === One
              val sr = lt*x === t
              val bth0 = have((x :: x.typ, sl <=> sr ) |- (lt*x === t)) by RightSubstIff.withParametersSimple(List((sl, sr)), F.lambda(phi, phi))(bt)
              have(Discharge(eqCorrect of (HOLSteps.x := lt*x, HOLSteps.y := t, A := typ1))(bth0))
            }
            
            val btc = lastStep.statement // x::x.typ |- lt(a)...(z)(x) = t

            val bu1 = have(BETA(lu*x))
            val bu = have((x :: x.typ) |- ((lu*x =:= u) === One)) by Restate.from(bu1)
            //val buh = have((x :: x.typ) |- (lu*x === u)) by Substitution.ApplyRules(eqCorrect of (HOLSteps.x := lu*x, HOLSteps.y := u, A := typ1))(bu)
            val buh = {
              val phi = F.formulaVariable
              val sl = (lu*x =:= u) === One
              val sr = lu*x === u
              val buh0 = have((x :: x.typ, sl <=> sr) |- (lu*x === u)) by RightSubstIff.withParametersSimple(List(((lu*x =:= u) === One, lu*x === u)), F.lambda(phi, phi))(bu)
              have(Discharge(eqCorrect of (HOLSteps.x := lu*x, HOLSteps.y := u, A := typ1))(buh0))
            }
            val buc = lastStep.statement // x::x.typ |- lt(a)...(z)(x) = u

            val s0 = have(t===u) by Tautology.from(prem, eqCorrect of (HOLSteps.x := t, HOLSteps.y := u, A := typ1))
            val s1 = {
              val xx = freshVariable(Seq(lt*x), "xx")
              val s10 = have((x :: x.typ, t === u) |- (lt*x === u)) by RightSubstEq.withParametersSimple(List((t, u)), F.lambda(xx, lt*x === xx))(bth)
              have(Discharge(s0)(s10))
            }
            //val s1 = have((x :: x.typ) |- ((lt*x)===u)) by Substitution.ApplyRules(s0)(bth)
            val s2 = {
              val xx = freshVariable(Seq(lt*x), "xx")
              val s20 = have((x :: x.typ, u === lu*x) |- (lt*x === lu*x)) by RightSubstEq.withParametersSimple(List((u, lu*x)), F.lambda(xx, lt*x === xx))(s1)
              have(Discharge(buh)(s20))
            }
            //val s2 = have((x :: x.typ) |- ((lt*x)===(lu*x))) by Substitution.ApplyRules(buh)(s1)
            

            //by RightSubstEq.withParametersSimple(List((r, r2)), F.lambda(xx, t*x === xx))(i0) //Substitution.ApplyRules(def_red_r)(i0)
            //      val i2 = have(Discharge(def_red_r)(i1))

          }
          val s2c = lastStep.statement.right.head // lt*x = lu*x
          val is2 = have(((x::x.typ) ==> s2c)) by Restate.from(lastStep)
          val qs2 = have(tforall(x, (lt*x)===(lu*x))) by RightForall(is2)
          val h1 = have((lt:: (x.typ |=> typ1), lu:: (x.typ |=> typ1)) |- ((lt =:= lu) === One)) by Tautology.from(funcUnique2 of (f := lt, g := lu, HOLSteps.x := x, A := x.typ, B := typ1), qs2)

          val h2 = have( Discharge(have(ProofType(lt)))(h1) )
          val h3 = have( Discharge(have(ProofType(lu)))(h2) )
          have(Clean.all(h3))


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
              p.statement.left.foreach(f => assume(f))
              val vt = typedvar(𝔹)
              val hp = have((t :: 𝔹, u :: 𝔹) |- p.statement.right) by Weakening(p)
              val h1 = have((t :: 𝔹, u :: 𝔹) |- t === u) by Tautology.from(eqCorrect of (x := t, y := u, A := 𝔹), eq)
              val hc = have((t :: 𝔹, u :: 𝔹, (t === u)) |- (u === One)) by RightSubstEq.withParametersSimple(List((t, u)), F.lambda(vt, vt === One))(hp)
              val h2 = have((t :: 𝔹, u :: 𝔹) |- (u === One)) by Cut(h1, hc)
              val pt = have(ProofType(t))
              val h3 = have(Discharge(pt)(h2))
              val h4 = have(Discharge(have(ProofType(u)))(h3))
              proof.cleanAssumptions
              have(Clean.all(h4))
    
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
          val qp = have((p :: 𝔹, q :: 𝔹) |- (q === One) ==> (p === One)) by Weakening(t1)
          val pq = have((p :: 𝔹, q :: 𝔹) |- (p === One) ==> (q === One)) by Weakening(t2)
          val pivot = have((p :: 𝔹, q :: 𝔹) |- (q === One) <=> (p === One)) by RightAnd(pq, qp)

          val h0 = have((p :: 𝔹, q :: 𝔹) |- (p === q)) by Cut(pivot, propExt of (HOLSteps.p -> p, HOLSteps.q -> q))
          val h1 = have((p :: 𝔹, q :: 𝔹) |- (p =:= q === One)) by Tautology.from(h0, eqCorrect of (A -> 𝔹, x -> p, y -> q))
          val h2 = have(Discharge(have(ProofType(p)))(h1))
          have(Discharge(have(ProofType(q)))(h2))

        
        case _ =>
          return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
        
    }

  }



  object INST extends ProofTactic {
    def apply(using proof: Proof)(inst: Seq[(TypedVar, Term)], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>

      val h0 = prem.of(inst.map(_ := _): _*)
      val h1 = inst.foldLeft(h0: ip.Fact)((acc, p) => 
        have( Discharge(have( ProofType(p._2) ))(acc) ) 
      )
      h0.statement.right.head match
        case eqOne(r) =>
          val def_red_r = have(DEF_RED(r)) // r === r2
          def_red_r.statement.right.head match {
            case `r` === r2 =>
              val s = have((h1.statement.left ++ def_red_r.statement.left) |- eqOne(r2)) by Substitution.ApplyRules(def_red_r)(h1)
              val s1 = have(Clean.all(s))
            case fail === _ =>
              throw new Exception(s"Was expecting an equation with left hand side $r but got $fail")
            case _ =>
              throw new Exception(s"Was expecting an equation as return of DEF_RED but got ${def_red_r.statement.right.head}")
          }

        case _ => 
          throw new Exception(s"Was expecting an r === One but got ${h0.statement.right.head}")


    }
      
        
  }

  object INST_TYPE extends ProofTactic {

    def apply(using proof: Proof)(x: F.Variable, t:Term, prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof{
      val r = prem of (x := t)
      have(r.statement) by Restate.from(r)
    }

  }

  object DEF_RED extends ProofTactic {
    def apply(using proof: Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      t match
        case ia: InstAbstraction => //  $λ*a*b*c...
          val base = ia.base
          val insts = ia.insts
          val a1 = assume(base.defin.bodyProp)
          val eq = insts.foldLeft(a1: ip.Fact)((acc, inst) =>
            val i1 = acc of inst
            i1.statement.right.head match
              case F.==>(left, right) =>  //   |- inst :: x.typ    --- not checking that type of insts match types freevars

                val i2 = have((i1.statement.left + left) |- right) by Restate.from(i1)
                val b1 = have(ProofType(inst._2))
                if b1.statement.right.head != left then
                  throw new Exception(s"Can't instantiate variable $left with term ${inst} of type  ${b1.statement.right.head}.")
                val b2 = have(Discharge(b1)(i2))
                b2
              case _ =>
                throw new Exception(s"Was expecting an implication  while unfolfing instantiations, but got ${i1.statement.right.head}." +
                  s"\n The instantiation was $inst. \n The formula was ${a1.statement}." )
          )
          eq.statement.right.head match
            case F.forall(x2: F.Variable, F.==>(v is (tp: Term), l === r)) => //ia.repr*insts...*x = ir.repr.body
              val x = x2 match
                case x: TypedVar => x
                case _ => TypedVar(x2.id, tp)
              val def_red_r = have(DEF_RED(r)) // r === r2
              def_red_r.statement.right.head match
                case `r` === r2 => 
                  val lambdar = λ(x, r2)
                  val ctx = computeContext(Set(t, lambdar))
                  val assump = ctx._1 ++ ctx._2
                  val ctxlr = computeContext(Set(lambdar, r2))
                  val goal = have((assump + (x::x.typ)) |- (t*x === r)).by.bot
                  val i0 = have((assump + (x::x.typ)) |- (t*x === r)) by Weakening(eq of x)
                  val xx = freshVariable[F.Sequent](Seq(i0.statement, def_red_r.statement), "xx")
                  val i1 = have((assump + (x::x.typ) + (r === r2)) |- (t*x === r2)) by RightSubstEq.withParametersSimple(List((r, r2)), F.lambda(xx, t*x === xx))(i0) //Substitution.ApplyRules(def_red_r)(i0)
                  val i2 = have(Discharge(def_red_r)(i1))
                  val h = have((assump + (x::x.typ) + (r2 === lambdar*x)) |- t*x === lambdar*x) by RightSubstEq.withParametersSimple(List((r2, lambdar*x)), F.lambda(xx, t*x === xx))(i2)  // Substitution.ApplyRules(pure)(i2)
                  val pure = have(BETA_PRIM(lambdar*x)) // λ(x, r)*x === r
                  val h0 = have(Discharge(pure)(h))
                  thenHave(assump |- (x::x.typ ==> (t*x === lambdar*x))) by Restate.from
                  val h1 = thenHave(assump |- tforall(x, t*x === lambdar*x)) by RightForall
                  val iatyp = x.typ |=> base.defin.outType
                  val fu = funcUnique of (f := lambdar, g := t, A := x.typ, B := base.defin.outType)
                  val h2 = have((assump + (t :: iatyp) + (lambdar :: iatyp))  |- (t === lambdar)) by Tautology.from(
                    fu,
                    eq,
                    h1
                  )
                  val h3 = have(Discharge(have(ProofType(lambdar)))(h2))
                  val ptt = have(ProofType(t))
                  val h4 = have(Discharge(ptt)(h3))

                  val prop_bodyprop = have(Restate(base.defin |- base.defin.bodyProp))
                  val h5 = have(Discharge(prop_bodyprop)(h4))
                  
                case fail === _ => 
                  throw new Exception(s"Was expecting an equation with left hand side $r but got $fail")
                case fail => 
                  throw new Exception(s"Was expecting an equation as return of DEF_RED but got $fail")
            case F.forall(x: TypedVar, F.==>(tp, r)) =>
              throw new Exception("Was expecting something of the form ∀(x, x::T => l === r) but got" + eq.statement)
            case F.forall(x: TypedVar, r) =>
              throw new Exception("Was expecting something of the form ∀(x,  x::T => f) but got" + eq.statement)
            case F.forall(x: F.Variable, r) =>
              throw new Exception("Was expecting something of the form ∀(x:TypedVar,  x::T => f) but got" + eq.statement)
            case r => 
              throw new Exception(s"Was expecting a formula of the form ∀(x, f) but got $r")


        case abs: Abstraction => 
          have(abs === abs) by Restate
        case v: TypedVar => 
          have(v === v) by Restate
        case f*u =>
          val s1 = have(DEF_RED(f))
          val s2 = have(DEF_RED(u))
          (s1.statement.left ++ s2.statement.left).foreach(f => assume(f))
          (s1.statement.right.head, s2.statement.right.head) match
            case (`f` === f2, `u` === u2) =>
              have(f*u === f*u) by Restate
              thenHave(f*u ===f2*u2) by Substitution.ApplyRules(s1, s2)
            case (fail1, fail2) =>
              throw new Exception(s"Was expecting two equations with left hand side $f but got $fail1 and with left hand side $u but got $fail2")
        case t => 
          have(t === t) by Restate
    }
  }


  object Clean {
    def lambda(using proof: Proof)(defin: AbstractionDefinition)(prem: proof.Fact) : proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      ip.cleanAssumptions
      val lctx12 = computeContextOfFormulas(Set(defin), Set())
      val lctx = lctx12._1 ++ lctx12._2
      val exdefin = F.exists(defin.reprVar, defin)

      val goal = ((prem.statement -<< defin) +<< exdefin)
    
      val s2 = have(LeftExists(prem)(((prem.statement -<< defin) +<< exdefin)))
      lctx.foreach(a => 
        assume(a)
      )
      val s1 = defin.elim
      val s3 = have(Discharge(s1)(s2))
    }

    def allLambdas(using proof: Proof)(prem: proof.Fact) : proof.ProofTacticJudgement = TacticSubproof{ ip ?=> 
      val statement = prem.statement
      val defins = statement.left.collect{case d: AbstractionDefinition => d}
      val candidate = defins.find(d => !(statement -<< d).freeVariables.contains(d.reprVar))

      candidate match
        case Some(defin: AbstractionDefinition) => 
          val h = have(Clean.lambda(defin)(prem))
          allLambdas(h)
        case None => 
          have(prem.statement) by Weakening(prem)
    }

    def variable(using proof: Proof)(ta: TypeAssignment[Term])(prem: proof.Fact) : proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      ip.cleanAssumptions
      val (v, typ) = ta.t match
        case v: F.Variable => (v, ta.typ)
        case _ => return proof.InvalidProofTactic(s"Can only eliminate type assignment of variables")

      if (prem.statement -<< ta).freeVariables.contains(v) then
        return proof.InvalidProofTactic(s"The variable ${v} is used in the premise and it's type assignment can't be eliminated")

      val exv = F.exists(v, ta)

      val p1 = have(TypeNonEmptyProof(ta.typ))
      val p2 = have(LeftExists(prem)(prem.statement -<< ta +<< exv))
      val p3 = have(Discharge(p1)(p2))
    }


    def allVariables(using proof: Proof)(prem:proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val statement = prem.statement
      val vars = statement.left.collectFirst[TypeAssignment[Term]]{case f @ ((v:F.Variable) is (typ:Term)) if !(statement -<< f).freeVariables.contains(v) => (v :: typ)}
      if vars.nonEmpty then
        val h = have(Clean.variable(vars.head)(prem))
        allVariables(h)
      else
        have(prem.statement) by Weakening(prem)
    }

    def typeVar(using proof: Proof)(net: NonEmptyType)(prem: proof.Fact) : proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val p2 = have(LeftExists(prem)(prem.statement -<< net ++<< nonEmptyTypeExists.statement))
      val p3 = have(Discharge(nonEmptyTypeExists)(p2))
    }

    def allTypeVars(using proof: Proof)(prem:proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      val statement = prem.statement
      val types = statement.left.collectFirst[NonEmptyType]{case net: NonEmptyType => net}
      if types.nonEmpty then
        val h = have(Clean.typeVar(types.head)(prem))
        allTypeVars(h)
      else
        have(prem.statement) by Weakening(prem)
    }

    def all(using proof: Proof)(prem:proof.Fact): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      ip.cleanAssumptions
      val h1 = have(Clean.allLambdas(prem))
      val h2 = have(Clean.allVariables(h1))
      val h3 = have(Clean.allTypeVars(h2))
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
