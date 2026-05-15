package lisa.hol
import lisa.SetTheoryLibrary
import lisa.automation._
import lisa.hol.Import.Transformers.mkTypedVar
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import lisa.maths.SetTheory.Types
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.K
import lisa.utils.UserLisaException
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.hol.HOLSteps.{HOLProofType}

import scala.collection.mutable

import SetTheoryLibrary.{have, JUSTIFICATION, thesis, THM, Proof, Theorem}

object ExtendedHOLSteps extends lisa._HOL {

  import lisa.hol.HOLHelperTheorems.{One, nonEmptyFuncSpace, assume, eqRefl}
  import K.repr
  
  private val A = typevar
  private val B = typevar
  private val t, u = variable[Ind >>: Ind]
  // Helpers for instantiating library theorems (some are stated using these names).
  private val Gf, Hf = variable[Ind >>: Ind]
  private val v = typedvar(B)
  private val w = typedvar(A)
  private val x = typedvar(A)
  private val y = typedvar(A)
  private val z = typedvar(A)
  private val e = typedvar(A ->: A)
  private val f = typedvar(A ->: B)
  private val g = typedvar(A ->: B)
  private val h = typedvar(B ->: A)

  private val p = typedvar(𝔹)
  private val q = typedvar(𝔹)
  private val r = typedvar(𝔹)

  import SetTheoryLibrary.{have, thenHave, lastStep}
  import lisa.utils.prooflib.SimpleDeducedSteps.Discharge

  object _REFL extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      // Extract typing context from current proof assumptions
      val pp = HOLProofType(t)
      val s1 = have(pp) // t::A
      val typ = s1.statement.right.head match
        case _ ∈ typ => typ
        case _ => return proof.InvalidProofTactic(s"Could not compute type of $t")
      val s2 = have(Discharge(s1)(eqRefl of (x := t, A := typ)))
    }
  }

  object _TRANS extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val s1 = t1.statement
      val s2 = t2.statement

      (s1, s2) match {
        case (HOLSequent(_, _, *(*(=:= #@ (aa), s), ta)), HOLSequent(_, _, *(*(=:= #@ (ab), tb), u))) => // equality is too strict
          if isSame(ta, tb) then
            if isSame(aa, ab) then
              (s1.left ++ s2.left).foreach(ip.addAssumption)
              val p0 = have(((s :: aa), (ta :: aa), (u :: aa)) |- (holeq(aa) * s * ta)) by Weakening(t1)
              val r0 = have(((s :: aa), (ta :: aa), (u :: aa), (holeq(aa) * ta * u) === One) |- (holeq(aa) * s * u) === One) by Cut.withParameters(holeq(aa) * s * ta)(p0, HOLHelperTheorems.eqTrans of (x := s, y := ta, z := u, A := aa))
              val r1 = have(((s :: aa), (ta :: aa), (u :: aa)) |- (holeq(aa) * s * u) === One) by Cut(t2, r0)
              val r2 = have(Discharge(HOLProofType(s), HOLProofType(ta), HOLProofType(u))(r1))
            else return proof.InvalidProofTactic(s"Types don't agree: $aa and $ab")
          else return proof.InvalidProofTactic(s"Middle elements don't agree: $ta and $tb")

        case (HOLSequent(_, _, _), HOLSequent(_, _, _)) =>
          return proof.InvalidProofTactic(s"The facts should have equalities")
        case _ =>
          s1 match
            case HOLSequent(_, _, _) =>
              return proof.InvalidProofTactic(s"The second fact is not parseable as an HOL sequent")
            case _ =>
              return proof.InvalidProofTactic(s"The first fact is not parseable as an HOL sequent")
      }
    }
  }

  object _MK_COMB extends ProofTactic {
    def apply(using proof: Proof)(f1: proof.Fact, f2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val fg = f1.statement
      val xy = f2.statement
      (fg, xy) match {
        case (HOLSequent(_, _, (=:= #@ typ1) * ff * gg), HOLSequent(_, _, (=:= #@ typ2) * xx * yy)) => // equality is too strict
          typ1 match {
            case ->:(inner, b) if isSame(typ2, inner) => // this CANNOT use equality because of alpha equivalence
              (f1.statement.left ++ f2.statement.left).foreach(ip.addAssumption)
              val s1 = have((xx :: typ2, yy :: typ2, ff :: typ1, gg :: typ1, ff =:= gg, xx =:= yy, ∃(x, x ∈ typ2), ∃(x, x ∈ b)) |- (ff * xx =:= gg * yy)) by Weakening(HOLSteps.mk_comTHM of (f := ff, g := gg, x := xx, y := yy, A := typ2, B := b))
              val d1 = have(Discharge(f1)(lastStep))
              val d2 = have(Discharge(f2)(d1))
              val d3 = have(Discharge(HOLProofType(xx), HOLProofType(yy), HOLProofType(ff), HOLProofType(gg))(d2))
            case _ =>
              return proof.InvalidProofTactic(s"Types don't agree: fun types are $typ1 and arg types are $typ2")
          }
        case _ =>
          return proof.InvalidProofTactic(s"The facts should be of the form f =:= g and x =:= y")
      }
    }
  }

  object _ABS extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVariable)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val xTyp = x.typ
      val s1 = prem.statement
      s1 match {
        case HOLSequent(left, _, (=:= #@ typ1) * tt * uu) =>
          // Assume everything except the binding variable's type
          prem.statement.left.filterNot(isSame(_, x :: xTyp)).foreach(ip.addAssumption)
          val lt = abs(xTyp)(λ(x, tt))
          val lu = abs(xTyp)(λ(x, uu))

          val xta = x :: xTyp

          // Extract context without x for typing proofs

          have((tforall(xta, tt :: typ1), tforall(xta, uu :: typ1)) |- (x :: xTyp) ==> (holeq(typ1) * (tt) * (uu) === One)) by Weakening(prem)
          val h1 = thenHave((tforall(xta, tt :: typ1), tforall(xta, uu :: typ1)) |- forall(x, (x :: xTyp) ==> (holeq(typ1) * (tt) * (uu) === One))) by RightForall
          have((tforall(xta, tt :: typ1), tforall(xta, uu :: typ1), tforall(xta, holeq(typ1) * (tt) * (uu) === One)) |- (holeq(xTyp ->: typ1) * lt * lu === One)) by Weakening(
            HOLSteps.absTHM of (t := λ(x, tt), u := λ(x, uu), A := xTyp, B := typ1)
          )
          val h2 = have(Discharge(h1)(lastStep))
          have(HOLProofType(tt))
          thenHave(lastStep.statement.left.filterNot(isSame(_, x :: xTyp)) |- (x :: xTyp) ==> (tt :: typ1)) by Weakening

          val h3 = thenHave(lastStep.statement.left |- tforall(xta, tt :: typ1)) by RightForall
          have(HOLProofType(uu))
          thenHave(lastStep.statement.left.filterNot(isSame(_, x :: xTyp)) |- (x :: xTyp) ==> (uu :: typ1)) by Weakening
          val h4 = thenHave(lastStep.statement.left |- tforall(xta, uu :: typ1)) by RightForall
          val h5 = have(h2.statement -<? (h3.statement.right.head) ++<< h3.statement) by Cut(h3, h2)
          val h6 = if h5.statement.left.exists(isSame(_, h4.statement.right.head)) then have(h5.statement -<? (h4.statement.right.head) ++<< h4.statement) by Cut(h4, h5) else h5

        case _ =>
          return proof.InvalidProofTactic(s"The fact should be of the form t =:= u")
      }
    }
  }

  object _BETA_CONV extends ProofTactic {
    def apply(using proof: Proof)(tin: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      tin match
        case Sabs(typ1, Abs(xx, tt)) * (r: Expr[Ind]) =>
          val typ2 = computeType(tin)
          val T = variable[Ind]
          val vx = xx
          val s1 = have((r :: typ1, tforall(vx :: typ1, tt :: typ2)) |- (holeq(typ2) * (fun(vx :: typ1, tt) * r) * tt.substitute(vx := r))) by Weakening(
            HOLSteps.betaConv of (A := typ1, B := typ2, t := λ(vx, tt), x := r)
          )
          // Prove typing for tt: build tforall (may have free variable assumptions)
          val ttPre = HOLProofType(tt)
          val ttImp = have(ttPre.statement.left.filterNot(isSame(_, vx :: typ1)) |- (vx :: typ1) ==> (tt :: typ2)) by Weakening(ttPre)
          val ttypForall = have(ttImp.statement.left.filterNot(isSame(_, vx :: typ1)) |- tforall(vx :: typ1, tt :: typ2)) by RightForall(ttImp)
          val h1 = have(Discharge(ttypForall, HOLProofType(r))(s1))
        case _ =>
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) v")
    }
  }

  object _BETA extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      t match
        case Sabs(typ1, tt) * (r: Variable[Ind]) =>
          // assure the right shape is present, and pass to the general case
          have(_BETA_CONV(t))
        case _ =>
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) y")

    }
  }

  object _ETA extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVariable, t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>

      if t.freeVars.contains(x) then return proof.InvalidProofTactic(s"Variable $x is free in the Expr[Ind] $t")
      val lxtx = λ(x, t * x)
      val restype = computeType(t * x)
      val ttype = x.typ ->: restype
      val s1 = have((t :: ttype, x :: x.typ, ∃(x, x :: x.typ), ∃(x, x :: restype)) |- holeq(ttype) * (fun(x :: x.typ, t * x)) * t) by Weakening(HOLSteps.etaConv of (ExtendedHOLSteps.x := x, f := t, A := x.typ, B := restype))
      have(Discharge(HOLProofType(t))(s1))
    }
  }

  object _ASSUME extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      val typ = computeType(t)
      if typ == 𝔹 then
        val s0 = have(t |- t) by Restate
      else return proof.InvalidProofTactic(s"Expr[Ind] $t is not a boolean")
    }

  }

  object _EQ_MP extends ProofTactic {
    def apply(using proof: Proof)(eq: proof.Fact, p: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      if eq.statement.right.size != 1 then return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One")
      eq.statement match
        case HOLSequent(left, _, ((=:= #@ `𝔹`) * t * u)) =>
          if p.statement.right.size != 1 then return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
          p.statement.right.head match
            case f if isSame(f, eqOne(t)) =>
              val assumptions = eq.statement.left ++ p.statement.left
              val vt = variable[Ind]
              val hp = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- p.statement.right) by Weakening(p)
              val h1 = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- t === u) by Tautology.from(HOLHelperTheorems.eqAlign of (x := t, y := u, A := 𝔹), eq)
              val hc = have((assumptions + (t :: 𝔹) + (u :: 𝔹) + (t === u)) |- (u === One)) by RightSubstEq.withParameters(List((t, u)), (Seq(vt), vt === One))(hp)
              val h2 = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- (u === One)) by Cut(h1, hc)
              val pt = have(HOLProofType(t))
              val h3 = have(Discharge(pt, HOLProofType(u))(h2))

            case _ =>
              return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
        case _ =>
          return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One ")

    }

  }

  object _DEDUCT_ANTISYM_RULE extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      if t1.statement.right.size != 1 || t2.statement.right.size != 1 then return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
      val left1 = t1.statement.left
      val c1 = t1.statement.right.head
      val left2 = t2.statement.left
      val c2 = t2.statement.right.head
      (c1, c2) match
        case (eqOne(p), eqOne(q)) =>
          (left1.filterNot(isSame(_, c2)) ++ left2.filterNot(isSame(_, c1))).foreach(ip.addAssumption)
          val qp = have((p :: 𝔹, q :: 𝔹) |- (q === One) ==> (p === One)) by Weakening(t1)
          val pq = have((p :: 𝔹, q :: 𝔹) |- (p === One) ==> (q === One)) by Weakening(t2)
          val pivot = have((p :: 𝔹, q :: 𝔹) |- (q === One) <=> (p === One)) by RightAnd(pq, qp)
          val h0 = have((p :: 𝔹, q :: 𝔹) |- (p === q)) by Cut.withParameters((q === One) <=> (p === One))(pivot, HOLSteps.propExt of (ExtendedHOLSteps.p -> p, ExtendedHOLSteps.q -> q))
          val h1 = have((p :: 𝔹, q :: 𝔹, p === q) |- (p =:= q === One)) by Weakening(HOLHelperTheorems.eqAlign of (A -> 𝔹, x -> p, y -> q))
          val h2 = have((p :: 𝔹, q :: 𝔹) |- (p =:= q === One)) by Cut.withParameters(p === q)(h0, h1)
          val h3 = have(Discharge(HOLProofType(p), HOLProofType(q))(h2))

        case _ =>
          return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
    }

  }

  object _INST_TYPE_RENAME extends ProofTactic {
    def allTypedVars(e: Expr[?]): Set[(TypedVariable, Expr[Ind])] = e match
      case v: TypedVariable => Set((v, v.typ))
      case App(func, arg) => allTypedVars(func) ++ allTypedVars(arg)
      case Abs(v: TypedVariable, body) =>
        allTypedVars(body) + ((v, v.typ): (TypedVariable, Expr[Ind]))
      case Abs(v, body) => allTypedVars(v) ++ allTypedVars(body)
      case _ => Set.empty

    def variableTypesNames(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val variablesSubst: mutable.Map[Variable[Ind], Variable[Ind]] = mutable.Map.empty
      val allvars = prem.statement.left.flatMap(allTypedVars) ++ prem.statement.right.flatMap(allTypedVars)
      val varsToChange: Map[Variable[Ind], TypedVariable] =
        allvars.collect { case (v, typ) if v.id.no != typ.hashCode().abs => (v, mkTypedVar(v.id.name, typ)) }.toMap

      def changeVarInExpr[A](e: Expr[A]): Expr[A] = e match
        case v: Variable[?] =>
          varsToChange.toMap.getOrElse(v, v).asInstanceOf[Variable[A]]
        case Abs(v: Variable[?], body) =>
          val targetVar = varsToChange.toMap.getOrElse(v, v)
          val targetBody = changeVarInExpr(body)
          if (targetVar eq v) && (targetBody eq body) then e else Abs(targetVar, targetBody).asInstanceOf[Expr[A]]
        case App(func, arg) =>
          val targetFunc = changeVarInExpr(func)
          val targetArg = changeVarInExpr(arg)
          if (targetFunc eq func) && (targetArg eq arg) then e else App(targetFunc, targetArg)
        case cst: Constant[A] => cst
      val targetSequent = prem.statement.left.map(changeVarInExpr) |- prem.statement.right.map(changeVarInExpr)
      val instPrem = prem.of((varsToChange.map { case (from, to) => from := to }).toSeq*)
      have(targetSequent) by Restate.from(instPrem)
    }

    def apply(using proof: Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val s1 = have(lisa.hol.HOLSteps._INST_TYPE(inst, prem))
      have(variableTypesNames(s1))
    }

  }
}

