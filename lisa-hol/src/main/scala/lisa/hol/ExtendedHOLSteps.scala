package lisa.hol
import lisa.SetTheoryLibrary
import lisa.hol.Import.Transformers.mkTypedVar
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import lisa.maths.SetTheory.Types
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.K
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.SimpleDeducedSteps.*
import SetTheoryLibrary.{have, thenHave, lastStep, Proof}
import lisa.hol.HOLSteps.{HOLProofType}

object ExtendedHOLSteps extends lisa._HOL {

  import lisa.hol.HOLHelperTheorems.{One, nonEmptyFuncSpace, assume, eqFromHol, eqRefl}

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

  /** Discharge a derived typing fact, retaining an explicit variable assignment. */
  private def dischargeTyping(using proof: Proof)(term: Expr[Ind], from: proof.Fact): proof.Fact =
    term match
      case _: TypedVariable => from
      case _ => have(Discharge(HOLProofType(term))(from))

  object _REFL {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      t match
        case variable: TypedVariable =>
          have(HOLSteps.Clean.all(eqRefl of (x := t, A := variable.typ)))
        case _ =>
          val typing = HOLProofType(t)
          val typ = typing.statement.right.head match
            case _ ∈ typ => typ
            case _ => return proof.InvalidProofTactic(s"Could not compute type of $t")
          val reflexivity = have(Discharge(typing)(eqRefl of (x := t, A := typ)))
          have(HOLSteps.Clean.all(reflexivity))
    }
  }

  object _TRANS {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val s1 = t1.statement
      val s2 = t2.statement

      (s1, s2) match {
        case (HOLSequent(_, _, *(*(=:= #@ (aa), s), ta)), HOLSequent(_, _, *(*(=:= #@ (ab), tb), u))) => // equality is too strict
          if isSame(ta, tb) then
            if isSame(aa, ab) then
              (s1.left ++ s2.left).foreach(ip.addAssumption)
              val firstEquality = (holeq(aa) * s * ta) === One
              val secondEquality = (holeq(aa) * ta * u) === One
              val result = (holeq(aa) * s * u) === One
              val typings = Set(s :: aa, ta :: aa, u :: aa)
              val transitivity = HOLHelperTheorems.eqTrans of (x := s, y := ta, z := u, A := aa)
              val r0 = have((s1.left ++ typings + secondEquality) |- result) by
                Cut.withParameters(firstEquality)(t1, transitivity)
              val r1 = have((s1.left ++ s2.left ++ typings) |- result) by
                Cut.withParameters((holeq(aa) * ta * u) === One)(t2, r0)
              val r2 = dischargeTyping(s, r1)
              val r3 = dischargeTyping(ta, r2)
              dischargeTyping(u, r3)
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

  object _MK_COMB {
    def apply(using proof: Proof)(f1: proof.Fact, f2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val fg = f1.statement
      val xy = f2.statement
      (fg, xy) match {
        case (HOLSequent(_, _, (=:= #@ typ1) * ff * gg), HOLSequent(_, _, (=:= #@ typ2) * xx * yy)) => // equality is too strict
          typ1 match {
            case ->:(inner, b) if isSame(typ2, inner) => // this CANNOT use equality because of alpha equivalence
              (f1.statement.left ++ f2.statement.left).foreach(ip.addAssumption)
              val rule = HOLSteps.mk_comTHM of (f := ff, g := gg, x := xx, y := yy, A := typ2, B := b)
              val d1 = have(Discharge(f1)(rule))
              val d2 = have(Discharge(f2)(d1))
              val d3 = dischargeTyping(xx, d2)
              val yyTyping = HOLProofType(yy)
              val d4 = yy match
                case _: TypedVariable => d3
                case _ => have(Discharge(yyTyping)(d3))
              val d5 = dischargeTyping(ff, d4)
              val d6 = dischargeTyping(gg, d5)
              have(HOLSteps.Clean.all(d6))
            case _ =>
              return proof.InvalidProofTactic(s"Types don't agree: fun types are $typ1 and arg types are $typ2")
          }
        case _ =>
          return proof.InvalidProofTactic(s"The facts should be of the form f =:= g and x =:= y")
      }
    }
  }

  object _ABS {
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

          have((tforall(xta, tt :: typ1), tforall(xta, uu :: typ1)) |- xta ==> (holeq(typ1) * tt * uu === One)) by
            RightImplies.withParameters(xta, (holeq(typ1) * tt * uu) === One)(prem)
          val equality = (holeq(typ1) * tt * uu) === One
          val h1 = have((tforall(xta, tt :: typ1), tforall(xta, uu :: typ1)) |- forall(x, xta ==> equality)) by
            RightForall.withParameters(xta ==> equality, x)(lastStep)
          val abstraction = HOLSteps.absTHM of (t := λ(x, tt), u := λ(x, uu), A := xTyp, B := typ1)
          val h2 = have(Discharge(h1)(abstraction))
          val ttTyping = HOLProofType(tt)
          val ttImp = have(ttTyping.statement.left.filterNot(isSame(_, x :: xTyp)) |- xta ==> (tt :: typ1)) by
            RightImplies.withParameters(xta, tt :: typ1)(ttTyping)
          val h3 = have(ttImp.statement.left |- tforall(xta, tt :: typ1)) by
            RightForall.withParameters(xta ==> (tt :: typ1), x)(ttImp)
          val uuTyping = HOLProofType(uu)
          val uuImp = have(uuTyping.statement.left.filterNot(isSame(_, x :: xTyp)) |- xta ==> (uu :: typ1)) by
            RightImplies.withParameters(xta, uu :: typ1)(uuTyping)
          val h4 = have(uuImp.statement.left |- tforall(xta, uu :: typ1)) by
            RightForall.withParameters(xta ==> (uu :: typ1), x)(uuImp)
          val h5 = have(h2.statement -<? h3.statement.right.head ++<< h3.statement) by
            Cut.withParameters(h3.statement.right.head)(h3, h2)
          if h5.statement.left.exists(isSame(_, h4.statement.right.head)) then
            have(h5.statement -<? h4.statement.right.head ++<< h4.statement) by Cut.withParameters(h4.statement.right.head)(h4, h5)
          else () // h5 already concludes the subproof.

        case _ =>
          return proof.InvalidProofTactic(s"The fact should be of the form t =:= u")
      }
    }
  }

  object _BETA_CONV {
    def apply(using proof: Proof)(tin: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      tin match
        case Sabs(typ1, Abs(xx, tt)) * (r: Expr[Ind]) =>
          val typ2 = computeType(tin)
          val T = variable[Ind]
          val vx = xx
          val result = holeq(typ2) * (fun(vx :: typ1, tt) * r) * tt.substitute(vx := r)
          val s1 = have((r :: typ1, tforall(vx :: typ1, tt :: typ2)) |- result) by
            Weakening(HOLSteps.betaConv of (A := typ1, B := typ2, t := λ(vx, tt), HOLSteps.betaArgument := r))
          // Prove typing for tt: build tforall (may have free variable assumptions)
          val ttPre = HOLProofType(tt)
          val ttImp = have(ttPre.statement.left.filterNot(isSame(_, vx :: typ1)) |- (vx :: typ1) ==> (tt :: typ2)) by
            RightImplies.withParameters(vx :: typ1, tt :: typ2)(ttPre)
          val ttypForall = have(ttImp.statement.left.filterNot(isSame(_, vx :: typ1)) |- tforall(vx :: typ1, tt :: typ2)) by
            RightForall.withParameters((vx :: typ1) ==> (tt :: typ2), vx)(ttImp)
          val bodyTyped = have(Discharge(ttypForall)(s1))
          dischargeTyping(r, bodyTyped)
        case _ =>
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) v")
    }
  }

  object _BETA {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      t match
        case Sabs(typ1, tt) * (r: Variable[Ind]) =>
          // assure the right shape is present, and pass to the general case
          have(_BETA_CONV(t))
        case _ =>
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) y")

    }
  }

  object _ETA {
    def apply(using proof: Proof)(x: TypedVariable, t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>

      if t.freeVars.contains(x) then return proof.InvalidProofTactic(s"Variable $x is free in the Expr[Ind] $t")
      val lxtx = λ(x, t * x)
      val restype = computeType(t * x)
      val ttype = x.typ ->: restype
      val s1 = have((t :: ttype, x :: x.typ, ∃(x, x :: x.typ), ∃(x, x :: restype)) |- holeq(ttype) * (fun(x :: x.typ, t * x)) * t) by Weakening(HOLSteps.etaConv of (ExtendedHOLSteps.x := x, f := t, A := x.typ, B := restype))
      have(Discharge(HOLProofType(t))(s1))
    }
  }

  object _ASSUME {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      val typ = computeType(t)
      if typ == 𝔹 then
        have(t |- t) by Hypothesis
      else return proof.InvalidProofTactic(s"Expr[Ind] $t is not a boolean")
    }

  }

  object _EQ_MP {
    def apply(using proof: Proof)(eq: proof.Fact, p: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      if eq.statement.right.size != 1 then return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One")
      eq.statement match
        case HOLSequent(left, _, ((=:= #@ `𝔹`) * t * u)) =>
          if p.statement.right.size != 1 then return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
          p.statement.right.head match
            case f if isSame(f, eqOne(t)) =>
              val assumptions = eq.statement.left ++ p.statement.left
              val vt = variable[Ind]
              val nativeEquality = t === u
              val equalityBridge = eqFromHol of (x := t, y := u, A := 𝔹)
              val h1 = have(Discharge(eq)(equalityBridge))
              val hc = have((assumptions + (t :: 𝔹) + (u :: 𝔹) + nativeEquality) |- (u === One)) by
                RightSubstEq.withParameters(List((t, u)), (Seq(vt), vt === One))(p)
              val h2 = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- (u === One)) by Cut.withParameters(nativeEquality)(h1, hc)
              val h3 = dischargeTyping(t, h2)
              val h4 = dischargeTyping(u, h3)
              have(HOLSteps.Clean.all(h4))

            case _ =>
              return proof.InvalidProofTactic(s"The second premise should prove $t but proves ${p.statement.right}")
        case _ =>
          return proof.InvalidProofTactic(s"The first premise should be of the form (t =:= u) === One ")

    }

  }

  object _DEDUCT_ANTISYM_RULE {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      if t1.statement.right.size != 1 || t2.statement.right.size != 1 then return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
      val left1 = t1.statement.left
      val c1 = t1.statement.right.head
      val left2 = t2.statement.left
      val c2 = t2.statement.right.head
      (c1, c2) match
        case (eqOne(p), eqOne(q)) =>
          (left1.filterNot(isSame(_, c2)) ++ left2.filterNot(isSame(_, c1))).foreach(ip.addAssumption)
          val qp = have((p :: 𝔹, q :: 𝔹) |- (q === One) ==> (p === One)) by
            RightImplies.withParameters(q === One, p === One)(t1)
          val pq = have((p :: 𝔹, q :: 𝔹) |- (p === One) ==> (q === One)) by
            RightImplies.withParameters(p === One, q === One)(t2)
          val rule = HOLSteps.deductAntisym of (ExtendedHOLSteps.p := p, ExtendedHOLSteps.q := q)
          val h1 = have(Discharge(qp, pq)(rule))
          val h2 = dischargeTyping(p, h1)
          val h3 = dischargeTyping(q, h2)
          have(HOLSteps.Clean.all(h3))

        case _ =>
          return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
    }

  }

  object _INST_TYPE_RENAME {
    /** Canonicalize free variables without merging distinct bound scopes. */
    def variableTypesNames(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      // Type instantiation can merge free HOL variables; binders must remain scoped.
      val renamings = prem.statement.freeVars.iterator.collect { case v: TypedVariable => v }
          .map(v => v -> mkTypedVar(v.id.name, v.typ))
          .collect { case (v, target) if v.id != target.id => v -> target }
          .map((from, to) => from := to).toSeq
      if renamings.isEmpty then have(prem.statement) by Restate.from(prem)
      else
        val renamed = prem.of(renamings*)
        have(renamed.statement) by Restate.from(renamed)
    }

    def apply(using proof: Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val s1 = have(lisa.hol.HOLSteps._INST_TYPE(inst, prem))
      have(variableTypesNames(s1))
    }

  }
}
