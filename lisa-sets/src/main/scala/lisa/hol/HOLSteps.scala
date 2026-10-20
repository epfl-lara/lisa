package lisa.hol
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation._
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Functions.BasicTheorems.absBodyEq
import lisa.maths.SetTheory.Functions.BasicTheorems.funcBetweenEqInFuncSpace
import lisa.maths.SetTheory.Functions.BasicTheorems.functionalExtentionality
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

import F.{_, given}
import Singleton.singleton
import HOLHelperTheorems.{nonEmptyTypeExists, nonEmptyFuncSpace, nonEmptyCodomain, eqAlign, eqRefl, eqFromHol, eqToHol, eqTrans, eqSym}

/**
 * Here we define and implement all the basic steps from HOL Light
 */
object HOLSteps extends lisa._HOL {
  import lisa.SetTheoryLibrary.{*, given}

  val lib = lisa.SetTheoryLibrary

  // Helper to extract typing context from a sequent
  @deprecated
  def extractContext(s: F.Sequent): Map[Variable[Ind], Typ] = ???

  // draft()

  // REFL
  // TRANS
  // MK_COMB
  // ABS
  // BETA
  // ETA
  // ASSUME
  // _EQ_MP
  // DEDUCT_ANTISYM_RULE
  // INST
  // INST_TYPE

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
  private[hol] val betaArgument = typedvar(A)


  val funcUnique = Theorem((f :: (A ->: B), g :: (A ->: B), x :: A, tforall(x :: A, f * x === g * x)) |- (f === g)) {
    assume(f :: (A ->: B))
    assume(g :: (A ->: B))
    assume(tforall(x :: A, f * x === g * x))

    val fIn = have(f ∈ (A ->: B)) by Hypothesis
    val gIn = have(g ∈ (A ->: B)) by Hypothesis

    val fBetween = have(functionBetween(f)(A)(B)) by Tautology.from(
      funcBetweenEqInFuncSpace of (lisa.maths.SetTheory.Base.Predef.f := f, A := A, B := B),
      fIn
    )
    val gBetween = have(functionBetween(g)(A)(B)) by Tautology.from(
      funcBetweenEqInFuncSpace of (lisa.maths.SetTheory.Base.Predef.f := g, A := A, B := B),
      gIn
    )

    val pointwise = have(forall(x, (x ∈ A) ==> (f * x === g * x))) by Hypothesis
    val conj = have(functionBetween(f)(A)(B) /\ functionBetween(g)(A)(B) /\ forall(x, (x ∈ A) ==> (f * x === g * x))) by Tautology.from(
      fBetween,
      gBetween,
      pointwise
    )

    have(thesis) by Tautology.from(
      functionalExtentionality of (lisa.maths.SetTheory.Base.Predef.f := f, g := g, A := A, B := B),
      conj
    )
  }
  val funcUnique2 = Lemma((f :: (A ->: B), g :: (A ->: B), x :: A, tforall(x :: A, f * x === g * x)) |- ((f =:= g) === One)) {
    have(thesis) by Substitute(eqAlign of (HOLSteps.x := f, HOLSteps.y := g, A := (A ->: B)))(funcUnique)
  }

  val Bdef = Theorem((p ∈ 𝔹) |- ((p === Zero) \/ (p === One))) {
    val s1 = have((p ∈ unorderedPair(∅, singleton(∅))) |- ((p === ∅) \/ (p === singleton(∅)))) by Weakening(pairAxiom of (z := p, x := ∅, y := singleton(∅)))
    val s2 = have((p ∈ 𝔹) |- ((p === ∅) \/ (p === singleton(∅)))) by Substitute(𝔹.definition)(s1)
    val s3 = have((p ∈ 𝔹) |- ((p === Zero) \/ (p === singleton(∅)))) by Substitute(Zero.definition)(s2)
    have((p ∈ 𝔹) |- ((p === Zero) \/ (p === One))) by Substitute(One.definition)(s3)
  }

  val propExt = Theorem((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- (p === q)) {

    val h2 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (p === One)) by Restate
    val h3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (q === One)) by Restate
    val h4 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), p === One) |- (p === q)) by Substitute(h3)(h2)

    val neq = have((p === Zero, p === One) |- ()) subproof {
      val zeq = have(∅ === Zero) by Weakening(Zero.definition)
      val oeq = have(singleton(∅) === One) by Weakening(One.definition)
      have(∅ ∈ singleton(∅)) by Weakening(Singleton.membership of (y := ∅, x := ∅))
      have((∅ === singleton(∅)) |- ()) by Restate.from(Singleton.nonEmpty of (x := ∅))

      thenHave((p === singleton(∅), p === ∅) |- ()) by Substitute(p === ∅)
      thenHave((p === singleton(∅), p === Zero) |- ()) by Substitute(zeq)
      thenHave((p === One, p === Zero) |- ()) by Substitute(oeq)
    }
    val i1 = have((p :: 𝔹 |- (!(p === One)) <=> (p === Zero))) by Tautology.from(Bdef of (p := p), neq)
    val i2 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- !(q === One) <=> !(p === One)) by Tautology
    val i3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One)) |- (q === Zero) <=> (p === Zero)) by Tautology.from(i2, i1, i1 of (p := q))

    val j2 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- p === Zero) by Tautology.from(Bdef of (p := p))
    val j3 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- q === Zero) by Tautology.from(lastStep)
    val j4WithEquality = have(
      (p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero), q === Zero) |- (p === q)
    ) by RightSubstEq.withParameters(Seq(Zero -> q), Seq(q) -> (p === q))(j2)
    val j4 = have((p :: 𝔹, q :: 𝔹, (q === One) <=> (p === One), !(p === One), (q === Zero) <=> (p === Zero)) |- (p === q)) by
      Cut.withParameters(q === Zero)(j3, j4WithEquality)

    have(thesis) by Tautology.from(j4, i3, h4)

  }

  /** Transport a true Boolean through HOL equality without re-inferring its type. */
  val eqMp = Theorem((p === One, q :: 𝔹, (holeq(𝔹) * p * q) === One) |- (q === One)) {
    val vt = variable[Ind]
    val sourceTyping = have(p === One |- (p :: 𝔹)) by
      RightSubstEq.withParameters(Seq((One, p)), (Seq(vt), vt :: 𝔹))(One.justif)
    val equality = have(Discharge(sourceTyping)(eqFromHol of (x := p, y := q, A := 𝔹)))
    val source = have(p === One |- (p === One)) by Hypothesis
    val transported = have((p === One, p === q) |- (q === One)) by
      RightSubstEq.withParameters(Seq((p, q)), (Seq(vt), vt === One))(source)
    have(thesis) by Cut.withParameters(p === q)(equality, transported)
  }

  val deductAntisym = Theorem(
    (p :: 𝔹, q :: 𝔹, (q === One) ==> (p === One), (p === One) ==> (q === One)) |- (p =:= q)
  ) {
    val qImpliesP = (q === One) ==> (p === One)
    val pImpliesQ = (p === One) ==> (q === One)
    val qp = have(qImpliesP |- qImpliesP) by Hypothesis
    val pq = have(pImpliesQ |- pImpliesQ) by Hypothesis
    val equivalence = have((qImpliesP, pImpliesQ) |- (q === One) <=> (p === One)) by
      RightAnd.withParameters(qImpliesP, pImpliesQ)(qp, pq)
    val nativeEquality = have(Discharge(equivalence)(propExt))
    have(Discharge(nativeEquality)(eqToHol of (HOLSteps.x := p, HOLSteps.y := q, A := 𝔹)))
  }

  val absTHM = Theorem(
    (tforall(x :: A, t(x) :: B), tforall(x :: A, u(x) :: B), tforall(x :: A, holeq(B) * (t(x)) * (u(x)) === One)) |-
      (holeq(A ->: B) * (abs(A)(t)) * (abs(A)(u)) === One)
  ) {
    val aT = assume(tforall(x :: A, t(x) :: B))
    val aU = assume(tforall(x :: A, u(x) :: B))
    val aEq = assume(tforall(x :: A, holeq(B) * (t(x)) * (u(x)) === One))

    val pointwiseEq = have(forall(x, (x ∈ A) ==> (t(x) === u(x)))) subproof {
      val holeqTyped = have((x ∈ A, t(x) ∈ B, u(x) ∈ B) |- holeq(B) * (t(x)) * (u(x)) === One) by InstantiateForall(x)(aEq)
      val eqTyped = thenHave((x ∈ A, t(x) ∈ B, u(x) ∈ B) |- (t(x) === u(x))) by Substitute(
        eqAlign of (HOLSteps.x := t(x), HOLSteps.y := u(x), A := B)
      )
      val tTyped = have(x ∈ A |- t(x) ∈ B) by InstantiateForall(x)(aT)
      val uTyped = have(x ∈ A |- u(x) ∈ B) by InstantiateForall(x)(aU)
      have(x ∈ A ==> (t(x) === u(x))) by Tautology.from(eqTyped, tTyped, uTyped)
      thenHave(thesis) by RightForall
    }

    val absEq = have(abs(A)(t) === abs(A)(u)) by Tautology.from(
      absBodyEq of (Gf := t, Hf := u),
      pointwiseEq
    )

    // Use TAbs to get typing from the tforall hypotheses
    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val e = variable[Ind >>: Ind]
    have(thesis) by Tautology.from(
      eqAlign of (HOLSteps.x := abs(A)(t), HOLSteps.y := abs(A)(u), A := (A ->: B)),
      absEq,
      lisa.maths.SetTheory.Types.TypingRules.TAbs of (T1 := A, T2 := λ(x, B), e := t),
      lisa.maths.SetTheory.Types.TypingRules.TAbs of (T1 := A, T2 := λ(x, B), e := u)
    )
  }

  val betaConv = Theorem(
    ((betaArgument :: A), tforall(betaArgument :: A, t(betaArgument) :: B)) |- holeq(B) * (abs(A)(t) * betaArgument) * t(betaArgument)
  ) {
    val T, T1, e1, e2 = variable[Ind]
    val T2, e = variable[Ind >>: Ind]
    val bodyForall = assume(tforall(betaArgument :: A, t(betaArgument) :: B))
    val bodyTyped = have(betaArgument :: A |- t(betaArgument) :: B) by InstantiateForall(betaArgument)(bodyForall)
    val argumentTyped = have(betaArgument :: A |- betaArgument :: A) by Hypothesis

    val abstractionTyped = lisa.maths.SetTheory.Types.TypingRules.TAbs of (T1 := A, T2 := λ(x, B), e := t)
    val applicationRule = lisa.maths.SetTheory.Types.TypingRules.TApp of (e1 := abs(A)(t), e2 := betaArgument, T1 := A, T2 := λ(x, B))
    val applicationTyped = have(Discharge(abstractionTyped, argumentTyped)(applicationRule))

    val betaEquality = BetaReduction of (T := A, e := t, e2 := betaArgument)
    val encodedEquality = eqToHol of (HOLSteps.x := abs(A)(t) * betaArgument, HOLSteps.y := t(betaArgument), A := B)
    have(Discharge(applicationTyped, bodyTyped, betaEquality)(encodedEquality))
  }

  val etaConvEq = Theorem((f :: (A ->: B), x :: A, nonEmpty(A), nonEmpty(B)) |- (abs(A)(λ(x, f * x)) === f)) {
    assume(f :: (A ->: B), nonEmpty(A), nonEmpty(B))

    val lam = λ(x, f * x)

    val pointwise = have(tforall(x :: A, abs(A)(lam) * x === f * x)) subproof {
      val T, e2 = variable[Ind]
      val e = variable[Ind >>: Ind]

      have((x :: A) ==> (abs(A)(lam) * x === f * x)) subproof {
        assume(x :: A)
        val betaEq = have(abs(A)(lam) * x === lam(x)) by Tautology.from(
          BetaReduction of (T := A, e := lam, e2 := x)
        )
        val lamApp = have(lam(x) === f * x) by Restate
        have(abs(A)(lam) * x === f * x) by Tautology.from(betaEq, lamApp)
      }
      thenHave(thesis) by RightForall
    }

    val absTyped = HOLProofType(abs(A)(lam))

    have(thesis) by Tautology.from(
      funcUnique of (f := abs(A)(lam), g := f, A := A, B := B),
      absTyped,
      pointwise
    )
  }

  val etaConv = Theorem((f :: (A ->: B), x :: A, nonEmpty(A), nonEmpty(B)) |- holeq(A ->: B) * (fun(x :: A, f * x)) * f) {
    assume(f :: (A ->: B), nonEmpty(A), nonEmpty(B))

    val lam = abs(A)(λ(x, f * x))
    val absT = HOLProofType(lam)
    have(thesis) by Tautology.from(
      etaConvEq,
      absT,
      eqAlign of (HOLSteps.x := lam, HOLSteps.y := f, A := (A ->: B))
    )
  }

  val mk_comTHM = Theorem((f :: (A ->: B), g :: (A ->: B), x :: A, y :: A, f =:= g, x =:= y) |- (f * x =:= g * y)) {
    val typ1 = A ->: B
    val typ2 = A
    val vx = typedvar(A)
    val vf = typedvar(A ->: B)

    assumeAll

    val p0 = HOLProofType(f * x)
    val p1 = have(f * x :: B |- f * x =:= f * x) by Tautology.from(eqRefl of (HOLSteps.x := f * x, A := B))
    val s1 = have(f * x =:= f * x) by Cut(p0, p1)
    val s2 = have((f :: typ1, g :: typ1) |- (f === g)) by Tautology.from(eqAlign of (HOLSteps.x := f, HOLSteps.y := g, A := typ1))
    val s3 = have((x :: typ2, y :: typ2) |- (x === y)) by Tautology.from(eqAlign of (HOLSteps.x := x, HOLSteps.y := y, A := typ2))

    val s4 = have((x :: typ2, f :: typ1, x === y) |- (f * x =:= f * y) === One) by RightSubstEq.withParameters(List((x, y)), (Seq(vx), f * x =:= f * vx))(s1)
    val s5 = have(((x :: typ2, f :: typ1, x === y, f === g)) |- (f * x =:= g * y) === One) by RightSubstEq.withParameters(List((f, g)), (Seq(vf), f * x =:= vf * y))(s4)

    val s6 = have((x :: typ2, y :: typ2, f :: typ1, (f === g)) |- (f * x =:= g * y) === One) by Cut(s3, s5)
    val s7 = have((x :: typ2, y :: typ2, f :: typ1, g :: typ1) |- (f * x =:= g * y) === One) by Cut(s2, s6)

    val witness = Variable.fresh[Ind](s7.statement.freeVars, "w")
    val bNonEmpty = have(p0.statement.left |- exists(witness, witness ∈ B)) by
      RightExists.withParameters(witness ∈ B, witness, f * x)(p0)
    val s8 = have(Discharge(bNonEmpty)(s7))
    have(Clean.all(s8))
  }

  /**
   *  ------------------
   *     |- t = t
   */
  object _REFL extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      // Extract typing context from current proof assumptions
      val s1 = HOLProofType(t) // t::A
      val typ = s1.statement.right.head match
        case _ ∈ typ => typ
        case _ => return proof.InvalidProofTactic(s"Could not compute type of $t")
      val s2 = have(Discharge(s1)(eqRefl of (x := t, A := typ)))
      have(Clean.all(s2))
    }
  }



  /**
   *  |- s = t    |- t = u
   *  ---------------------
   *        |- s = u
   */
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
              val r0 = have(((s :: aa), (ta :: aa), (u :: aa), (holeq(aa) * ta * u) === One) |- (holeq(aa) * s * u) === One) by Cut.withParameters(holeq(aa) * s * ta)(p0, eqTrans of (x := s, y := ta, z := u, A := aa))
              val r1 = have(((s :: aa), (ta :: aa), (u :: aa)) |- (holeq(aa) * s * u) === One) by Cut(t2, r0)
              val r2 = have(Discharge(HOLProofType(s))(r1))
              val r3 = have(Discharge(HOLProofType(ta))(r2))
              val r4 = have(Discharge(HOLProofType(u))(r3))
              have(Clean.all(r4))
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

  /*

  /**
   * Apply transitivity of equality, but with alpha equivalence.
   */
  object TRANS extends ProofTactic {
    def apply(using proof: Proof)(t1: proof.Fact, t2: proof.Fact): proof.ProofTacticJudgement =
      val s1 = t1.statement
      val s2 = t2.statement

      (s1, s2) match {
        case (HOLSequent(left1, (=:= #@aa)*s*ta), HOLSequent(left2, (=:= #@ab)*tb*u) ) => //equality is too strict
            if aa == ab then
              if ta == tb then
                TRANS(t1, t2)
              else
                // try to see if ta alpha_eq tb
                TacticSubproof:
                  val alpha = have(ALPHA_EQUIVALENCE(ta, tb))
                  val s1 = have(TRANS(t1, alpha))
                  val s2 = have(TRANS(s1, t2))
            else
              return proof.InvalidProofTactic(s"Types don't agree: $aa and $ab")

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


   */

  /**
   *  |- f = g    |- x = y
   *  ---------------------
   *        |- f x = g y
   */
  object _MK_COMB extends ProofTactic {
    def apply(using proof: Proof)(f1: proof.Fact, f2: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val fg = f1.statement
      val xy = f2.statement
      (fg, xy) match {
        case (HOLSequent(_, _, (=:= #@ typ1) * ff * gg), HOLSequent(_, _, (=:= #@ typ2) * xx * yy)) => // equality is too strict
          typ1 match {
            case ->:(inner, b) if isSame(typ2, inner) => // this CANNOT use equality because of alpha equivalence
              (f1.statement.left ++ f2.statement.left).foreach(ip.addAssumption)
              val s1 = have((xx :: typ2, yy :: typ2, ff :: typ1, gg :: typ1, ff =:= gg, xx =:= yy, ∃(x, x ∈ typ2), ∃(x, x ∈ b)) |- (ff * xx =:= gg * yy)) by Weakening(mk_comTHM of (f := ff, g := gg, x := xx, y := yy, A := typ2, B := b))
              val d1 = have(Discharge(f1)(lastStep))
              val d2 = have(Discharge(f2)(d1))
              val d3 = have(Discharge(HOLProofType(xx))(d2))
              val d4 = have(Discharge(HOLProofType(yy))(d3))
              val d5 = have(Discharge(HOLProofType(ff))(d4))
              val d6 = have(Discharge(HOLProofType(gg))(d5))
              have(Clean.all(d6))

            case _ =>
              return proof.InvalidProofTactic(s"Types don't agree: fun types are $typ1 and arg types are $typ2")
          }
        case _ =>
          println(s"fg: $fg")
          println(s"xy: $xy")
          return proof.InvalidProofTactic(s"The facts should be of the form f =:= g and x =:= y")
      }
    }
  }

  /**
   *     |- t =:= u
   * ---------------------
   *  |- λx. t =:= λx. u
   */
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
            absTHM of (t := λ(x, tt), u := λ(x, uu), A := xTyp, B := typ1)
          )
          val h2 = have(Discharge(h1)(lastStep))
          HOLProofType(tt)
          thenHave(lastStep.statement.left.filterNot(isSame(_, x :: xTyp)) |- (x :: xTyp) ==> (tt :: typ1)) by Weakening

          val h3 = thenHave(lastStep.statement.left |- tforall(xta, tt :: typ1)) by RightForall
          HOLProofType(uu)
          thenHave(lastStep.statement.left.filterNot(isSame(_, x :: xTyp)) |- (x :: xTyp) ==> (uu :: typ1)) by Weakening
          val h4 = thenHave(lastStep.statement.left |- tforall(xta, uu :: typ1)) by RightForall
          val h5 = have(h2.statement -<? (h3.statement.right.head) ++<< h3.statement) by Cut(h3, h2)
          val h6 = if h5.statement.left.exists(isSame(_, h4.statement.right.head)) then have(h5.statement -<? (h4.statement.right.head) ++<< h4.statement) by Cut(h4, h5) else h5
          have(Clean.all(h6))

        case _ =>
          return proof.InvalidProofTactic(s"The fact should be of the form t =:= u")
      }
    }
  }

  /**
   * BETA_CONV((λx. t) u) produces |- (λx. t) u =:= t[x := u]
   */
  object _BETA_CONV extends ProofTactic {
    def apply(using proof: Proof)(tin: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      tin match
        case Sabs(typ1, Abs(xx, tt)) * (r: Expr[Ind]) =>
          // val betaConv = Theorem(((x :: A), tforall(x :: A, t(x)::B))|- holeq(B)*(abs(A)(t) * x) *t(x))
          val typ2 = computeType(tin)
          val T = variable[Ind]
          val vx = xx
          val s1 = have((r :: typ1, tforall(vx :: typ1, tt :: typ2)) |- (holeq(typ2) * (fun(vx :: typ1, tt) * r) * tt.substitute(vx := r))) by Weakening(
            betaConv of (A := typ1, B := typ2, t := λ(vx, tt), betaArgument := r)
          )
          // Prove typing for tt: build tforall (may have free variable assumptions)
          val ttPre = HOLProofType(tt)
          val ttImp = have(ttPre.statement.left.filterNot(isSame(_, vx :: typ1)) |- (vx :: typ1) ==> (tt :: typ2)) by Weakening(ttPre)
          val ttypForall = have(ttImp.statement.left.filterNot(isSame(_, vx :: typ1)) |- tforall(vx :: typ1, tt :: typ2)) by RightForall(ttImp)
          val h1 = have(Discharge(ttypForall)(s1))
          val h2 = have(Discharge(HOLProofType(r))(h1))
          have(Clean.all(h2))
        case _ =>
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) v")
    }
  }

  /**
   * BETA((λx. t) x) produces |- (λx. t) x =:= t
   */
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

  /*
  object BETA_PRIM extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      t match
        case (l:Abstraction)*(r: TypedVar) if l.bound == r =>
          val b = l.BETA
          val s1 = have(b.statement) by Weakening(b) //l*r =:= l.body
          val ctx = computeContext(Set(l*r, l.body))
          ctx._1.foreach(a => assume(a))
          ctx._2.foreach(a => assume(a))
          val bt = have((r::r.typ) |- ((l*r =:= l.body) === One)) by Restate.from(s1)
          val ptlr = HOLProofType(l*r)
          val ptlb = HOLProofType(l.body)
          val bth = have((r::r.typ, l*r :: l.defin.outType, l.body :: l.defin.outType) |- (l*r === l.body)) by Substitute(
            eqCorrect of (HOLSteps.x := l*r, HOLSteps.y := l.body, A := l.defin.outType)
          )(bt)
          have(Discharge(ptlr)(lastStep))
          have(Discharge(ptlb)(lastStep))
        case _ =>
          return proof.InvalidProofTactic(s"The Expr[Ind] should be of the form (λx. t) x")
    }
  }


  // λ(x, t*x) === t
  object ETA_PRIM extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVar, t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      if t.freeVariables.contains(x) then
      return proof.InvalidProofTactic(s"Variable $x is free in the Expr[Ind] $t")
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
      val r2 = have((t::lxtx.typ) |- (lxtx === t)) by Cut(HOLProofType(lxtx), r1)
      have((lxtx === t)) by Cut(HOLProofType(t), r2)
    }
  }

   */

  // λ(x, t*x) =:= t
  object _ETA extends ProofTactic {
    def apply(using proof: Proof)(x: TypedVariable, t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>

      if t.freeVars.contains(x) then return proof.InvalidProofTactic(s"Variable $x is free in the Expr[Ind] $t")
      val lxtx = λ(x, t * x)
      val ttype_step = HOLProofType(t)
      val restype = computeType(t * x)
      val ttype = x.typ ->: restype
      val s1 = have((t :: ttype, x :: x.typ, ∃(x, x :: x.typ), ∃(x, x :: restype)) |- holeq(ttype) * (fun(x :: x.typ, t * x)) * t) by Weakening(etaConv of (HOLSteps.x := x, f := t, A := x.typ, B := restype))
      have(Discharge(ttype_step)(s1))
      have(Clean.all(lastStep))
    }
  }

  /**
   * ---------------
   *     t |- t
   */
  object _ASSUME extends ProofTactic {
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      val typ = computeType(t)
      if typ == 𝔹 then
        val s0 = have(t |- t) by Restate
        have(Clean.all(s0))
      else return proof.InvalidProofTactic(s"Expr[Ind] $t is not a boolean")
    }

  }

  /**
   *  |- t = u    |- t
   * -------------------
   *       |- u
   */
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
              val h1 = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- t === u) by Tautology.from(eqAlign of (x := t, y := u, A := 𝔹), eq)
              val hc = have((assumptions + (t :: 𝔹) + (u :: 𝔹) + (t === u)) |- (u === One)) by RightSubstEq.withParameters(List((t, u)), (Seq(vt), vt === One))(hp)
              val h2 = have((assumptions + (t :: 𝔹) + (u :: 𝔹)) |- (u === One)) by Cut(h1, hc)
              val pt = HOLProofType(t)
              val h3 = have(Discharge(pt)(h2))
              val h4 = have(Discharge(HOLProofType(u))(h3))
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
          val h0 = have((p :: 𝔹, q :: 𝔹) |- (p === q)) by Cut.withParameters((q === One) <=> (p === One))(pivot, propExt of (HOLSteps.p -> p, HOLSteps.q -> q))
          val h1 = have((p :: 𝔹, q :: 𝔹, p === q) |- (p =:= q === One)) by Weakening(eqAlign of (A -> 𝔹, x -> p, y -> q))
          val h2 = have((p :: 𝔹, q :: 𝔹) |- (p =:= q === One)) by Cut.withParameters(p === q)(h0, h1)
          val h3 = have(Discharge(HOLProofType(p))(h2))
          val h4 = have(Discharge(HOLProofType(q))(h3))
          have(Clean.all(h4))

        case _ =>
          return proof.InvalidProofTactic(s"The premises should be of the form p === One and q === One")
    }

  }

  object _INST extends ProofTactic {
    def apply(using proof: Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val k = prem.of(inst.map(_ := _)*)
      val h0 = have(k.statement) by Restate.from(k) // to avoid laststep failing
      val violating = inst.iterator.collect { case (v: TypedVariable, t) if prem.statement.hasFree(v) =>
        (v, t, computeType(t))
      }.find { case (v, _, typ) => v.typ != typ && !isSame(v.typ, typ) }
      violating match
        case Some((v, t, typ)) => return proof.InvalidProofTactic(s"Type mismatch in instantiation: ${v} has type ${v.typ} but term ${t} has type $typ")
        case None => ()
      val instWithProofs = inst.flatMap((v, t) =>
        if !prem.statement.hasFree(v) then None // no need to discharge if the variable isn't free in the statement
        else
          val typProof = HOLProofType(t)
          Some((v, t, typProof))
      )
      instWithProofs.foldLeft(h0: ip.Fact) { case (h, (v, t, typProof)) =>
        have(Discharge(typProof)(h))
      }
      have(Clean.all(lastStep))
    }
  }

  object _INST_TYPE extends ProofTactic {

    def apply(using proof: Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val k = prem.of(inst.map(_ := _)*)
      val h0 = have(k.statement) by Restate.from(k) // to avoid laststep failing

      val instWithProofs = inst.flatMap((v, t) =>
        if !prem.statement.hasFree(v) then None // no need to discharge if the variable isn't free in the statement
        else
          val typProof = have(TypeNonEmptyProof(t))
          Some((v, t, typProof))
      )
      instWithProofs.foldLeft(h0: ip.Fact) { case (h, (v, t, typProof)) =>
        have(Discharge(typProof)(h))
      }
      have(Clean.all(lastStep))
    }

  }

  object HOLProofType extends ProofTactic {

    private case class CacheKey(term: Long, variableTypes: Vector[Long])

    private def code[S: Sort](t: Expr[S]): CacheKey =
      val variableTypes = Vector.newBuilder[Long]
      def collect(expression: Expr[?]): Unit = expression match
        case variable: TypedVariable => variableTypes += variable.typ.underlying.uniqueNumber
        case App(function, argument) =>
          collect(function)
          collect(argument)
        case Abs(variable, body) =>
          collect(variable)
          collect(body)
        case _ => ()
      collect(t)
      CacheKey(t.underlying.uniqueNumber, variableTypes.result())

    def cacheSize(using proof: Proof): Int = proof.cachedRootStepCount

    private def application(using proof: Proof)(t: Expr[Ind]): Option[proof.ProofTacticJudgement] = t match
      case Sapp(function: Expr[Ind], argument: Expr[Ind]) =>
        val functionTyping = canonical(function)
        functionTyping.statement.right.head match
          case _ ∈ (functionType @ SPi(domain: Expr[Ind], Abs(bound: Variable[Ind], codomain: Expr[Ind])))
              if !codomain.underlying.freeVariables.contains(bound.underlying) =>
            val argumentTyping = canonical(argument)
            argumentTyping.statement.right.head match
              case _ ∈ argumentType if isSame(argumentType, domain) =>
                Some(Typecheck.applicationProof(function, argument, functionType)(functionTyping, argumentTyping))
              case _ => None
          case _ => None
      case _ => None

    private def abstraction(using proof: Proof)(t: Expr[Ind]): Option[proof.ProofTacticJudgement] = t match
      case Sabs(domain: Expr[Ind], Abs(bound: TypedVariable, body: Expr[Ind])) if isSame(bound.typ, domain) =>
        val bodyTyping = canonical(body)
        bodyTyping.statement.right.head match
          case _ ∈ bodyType if !bodyType.underlying.freeVariables.contains(bound.underlying) =>
            Some(Typecheck.abstractionProof(bound, domain, body, bodyType)(bodyTyping))
          case _ => None
      case _ => None

    /** Infer a cleaned typing step without inheriting the enclosing assumptions. */
    private def infer(using proof: Proof)(context: => Set[Expr[Prop]], t: Expr[Ind], reuse: Boolean = true): proof.ProofStep =
      val result = TacticSubproof { ip ?=>
        ip.cleanAssumptions
        val reused = if reuse then application(t).orElse(abstraction(t)) else None
        val typed = have(reused.getOrElse(Typecheck.inferProof(context, t)))
        have(Clean.all(typed))
      }
      result.validate(summon[sourcecode.Line], summon[sourcecode.File])

    // Constants supply their own type-parameter requirements. Annotations
    // alone must not introduce unrelated non-emptiness hypotheses.
    private def context(t: Expr[Ind]): Set[Expr[Prop]] =
      getContext(t).collect { case assignment @ TypeAssign(_, _) => assignment }

    // Subterm reuse must not fall back to the caller's assumptions.
    private def canonical(using proof: Proof)(t: Expr[Ind]): proof.Fact = t match
      case tc: TypedConstant => proof.asOutsideFact(tc.justif)
      case _ => proof.cachedRootStep((this, code(t))): root =>
        infer(using root)(context(t), t)

    private def localStep(using proof: Proof)(fact: proof.Fact): proof.ProofStep = fact match
      case step: proof.ProofStep => step
      case _ =>
        val statement = proof.sequentOfFact(fact)
        proof.newProofStep(proof.ValidProofTactic(statement, Seq(SC.Restate(statement.underlying, -1)), Seq(fact)))

    /**
     * Prove typing in the current proof, sharing canonical derivations within its root proof.
     *
     * @throws LisaHOLException if typing cannot be derived from the term or the local assumptions
     */
    def apply(using proof: Proof)(t: Expr[Ind]): proof.ProofStep =
      try localStep(canonical(t))
      catch
        case error: Exception =>
          val assignments = context(t)
          val localContext = assignments ++ proof.getAssumptions
          if localContext.size == assignments.size then
            throw LisaHOLException(s"Failed to compute and prove typing for term $t: ${error.getMessage}")
          // This derivation depends on the caller's assumptions: never cache it.
          try infer(localContext.toSet, t, reuse = false)
          catch case local: Exception =>
            throw LisaHOLException(s"Failed to compute and prove typing for term $t: ${local.getMessage}")

  }

  object Clean {

    // Match non-emptiness assumptions directly, independently of frontend sugar.
    private object NonEmpty:
      def unapply(formula: Expr[Prop]): Option[(Variable[Ind], Expr[Ind], Expr[Ind])] = formula match
        case App(quantifier, Abs(bound: Variable[Ind] @unchecked, App(App(membership, element), typ)))
            if isSame(quantifier, exists) && isSame(membership, ∈) =>
          Some((bound, element.asInstanceOf[Expr[Ind]], typ.asInstanceOf[Expr[Ind]]))
        case _ => None

    // Eliminate an unused term-variable typing assumption through type non-emptiness.
    def variable(using proof: Proof)(ta: TypeAssign[Variable[Ind]])(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      val (v, typ) = (ta.vari, ta.typ)

      v match
        case typed: TypedVariable if !isSame(typed.typ, typ) =>
          throw LisaHOLException(s"Mismatched typing assumption $ta while cleaning ${prem.statement}.")
        case _ => ()

      if (prem.statement -<< ta).hasFree(v) then return proof.InvalidProofTactic(s"The variable ${v} is used in the sequent and its type assignment cannot be eliminated")

      val p1 = have(TypeNonEmptyProof(ta.typ))
      val p2 = have(prem.statement -<? ta +<? F.exists(v, ta)) by LeftExists.withParameters(ta, v)(prem)
      have(Discharge(p1)(p2))
    }

    def allVariables(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      val statement = prem.statement
      val vars = statement.left.collectFirst[TypeAssign[Variable[Ind]]] {
        case f @ ((v: Variable[Ind] @unchecked) ∈ (typ: Expr[Ind])) if !(statement -<< f).hasFree(v) => (v :: typ)
      }
      if vars.nonEmpty then
        val h = have(Clean.variable(vars.head)(prem))
        have(allVariables(h))
      else have(prem.statement) by Restate.from(prem)
    }

    // Eliminate a type-variable non-emptiness assumption using HOL's inhabited universe.
    def typeVar(using proof: Proof)(net: Expr[Prop], tv: Variable[Ind])(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      val p2 = have(prem.statement -<? net +<< nonEmptyTypeExists.statement.right.head) by LeftExists.withParameters(net, tv)(prem)
      have(Discharge(nonEmptyTypeExists)(p2))
    }

    /** Discharge type non-emptiness using a typed term already in the context. */
    private def inhabitedType(using proof: Proof)(net: Expr[Prop], bound: Variable[Ind], assignment: TypeAssign[Variable[Ind]])(prem: proof.Fact): proof.ProofTacticJudgement =
      TacticSubproof { ip ?=>
        ip.cleanAssumptions
        val witnessTyping = have(assignment |- assignment) by Hypothesis
        val nonEmpty = have(assignment |- net) by RightExists.withParameters(bound ∈ assignment.typ, bound, assignment.vari)(witnessTyping)
        have(prem.statement -<? net) by Cut.withParameters(net)(nonEmpty, prem)
      }

    /** Remove every non-emptiness premise already witnessed by a typed variable. */
    private def allInhabited(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      val removable = prem.statement.left.iterator.flatMap:
        case net @ NonEmpty(bound, element, typ) if isSame(bound, element) =>
          val exact = prem.statement.left.collectFirst:
            case TypeAssign(v: Variable[Ind], assignedType) if isSame(assignedType, typ) =>
              Left((net, bound, v :: assignedType))
          exact.orElse:
            prem.statement.left.iterator.flatMap:
              case TypeAssign(function: Variable[Ind], domain ->: codomain) if isSame(codomain, typ) =>
                prem.statement.left.collectFirst:
                  case domainNet @ NonEmpty(domainBound, domainElement, domainType)
                      if !isSame(domainNet, net) && isSame(domainBound, domainElement) && isSame(domainType, domain) =>
                    Right((net, function, domain, codomain))
              case _ => None
            .nextOption()
        case _ => None
      .nextOption()

      removable match
        case Some(Left((net, bound, assignment))) =>
          val h = have(inhabitedType(net, bound, assignment)(prem))
          have(allInhabited(h))
        case Some(Right((_, function, domain, codomain))) =>
          val instance = nonEmptyCodomain of (f := function, A := domain, B := codomain)
          val witness = have(instance.statement) by Restate.from(instance)
          val h = have(Discharge(witness)(prem))
          have(allInhabited(h))
        case None => have(prem.statement) by Restate.from(prem)
    }

    def allTypeVars(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      val statement = prem.statement
      val typ = statement.left.iterator.flatMap:
        case f @ NonEmpty(x, y, tv: Variable[Ind]) if isSame(x, y) =>
          val witness = statement.left.collectFirst:
            case TypeAssign(v: Variable[Ind], typ) if isSame(typ, tv) => v :: typ
          if witness.nonEmpty || !(statement -<? f).hasFree(tv) then Some((f, x, tv, witness))
          else None
        case _ => None
      .nextOption()

      typ match {
        case Some((f, x, _, Some(assignment))) =>
          val h = have(inhabitedType(f, x, assignment)(prem))
          have(allTypeVars(h))
        case Some((f, _, tv, None)) =>
          val h = have(Clean.typeVar(f, tv)(prem))
          if h.statement.left.exists({
              case candidate @ NonEmpty(x, y, _: Variable[Ind]) if isSame(x, y) => isSame(candidate, f)
              case _ => false
            })
          then throw new Exception(s"Could not eliminate type variable ${f} from the premise.")
          have(allTypeVars(h))
        case _ => have(prem.statement) by Restate.from(prem)
      }
    }

    /**
     * Recursively collect all constant types / type functors appearing in a term
     * instantiating polymorphic constants, and create a sequence of discharges
     * to eliminate their respective non-emptiness assumptions.
     *
     * Non emptiness assumptions for constants are of the form
     *
     * ```
     *   |- ∃ x. x ∈ C
     * ```
     *
     * and for type functors of the form
     *
     * ```
     * /\_i (∃x. x ∈ Ai) |- ∃x. x ∈ F(A1,...,An)
     * ```
     *
     * The non-emptiness of the set of returned expressions (+ free variables)
     * are sufficient to prove that the typing of the input term is valid.
     */
    def collectInstantiatingConstants(using proof: lib.Proof)(term: Expr[?]): Seq[(Expr[Ind], proof.Fact)] = {

      val (justMap, ordMap) = collectIncremental(term, 0, Map.empty, Map.empty)

      justMap.toSeq.sortBy((k, v) => ordMap(k))
    }

    private type JMap[T] = Map[Expr[Ind], T]
    private type OMap = Map[Expr[Ind], Int]

    /**
     * Apply [[collectIncremental]] to a sequence of terms at a given depth.
     */
    private inline def foldIncremental(using
        proof: lib.Proof
    )(
        terms: Iterable[Expr[?]],
        depth: Int,
        justMap: JMap[proof.Fact],
        ordMap: OMap
    ): (JMap[proof.Fact], OMap) =
      terms.foldLeft((justMap, ordMap)):
        case ((jmap, omap), nextT) =>
          collectIncremental(nextT, depth, jmap, omap)

    private def collectIncremental(using
        proof: lib.Proof
    )(
        term: Expr[?],
        depth: Int,
        /**
         * Mapping from types to their non-emptiness justification
         */
        justMap: JMap[proof.Fact],
        /**
         * Mapping from types to the MAX DEPTH we have seen them at
         *
         * Depth is not necessarily in the term, but rather as dependencies in
         * proofs of non-emptiness
         *
         * This is effectively incrementally producing a topological ordering of
         * the keys of justMap
         */
        ordMap: OMap
    ): (JMap[proof.Fact], OMap) = {
      // invariant:
      // justMap.keySet == ordMap.keySet

      // shorthand for the many places when we know this is a safe cast
      inline def tt: Expr[Ind] = term.asInstanceOf

      if term.sort == K.Ind && justMap.contains(tt) then
        if ordMap(tt) >= depth then (justMap, ordMap)
        else
          val nextOrd = ordMap.updated(tt, depth)
          // A known composite can be rediscovered deeper through another root.
          // Propagate that depth so its dependencies remain ordered after it.
          term match
            case a `->:` b => foldIncremental(Seq(a, b), depth + 1, justMap, nextOrd)
            case Multiapp(f: HOLPolymorphicType[?], args) if f.freeTypeVars.nonEmpty =>
              foldIncremental(args, depth + 1, justMap, nextOrd)
            case _ => (justMap, nextOrd)
      else
        term match
          case HOLConstantType(cst) =>
            // we need to add the non-emptiness proof for this constant type, and all
            // of its dependencies (i.e. the types appearing in its own non-emptiness proof)
            val just = cst.nonEmptyThm
            val nextJ = justMap + (cst -> just)
            val nextOrd = ordMap + (cst -> depth)

            foldIncremental(just.statement.right, depth + 1, nextJ, nextOrd)

          case a `->:` b =>
            val just = nonEmptyFuncSpace.of(A := a, B := b)
            val nextJ = justMap + (tt -> just)
            val nextOrd = ordMap + (tt -> depth)

            foldIncremental(Seq(a, b), depth + 1, nextJ, nextOrd)

          case Multiapp(typ: HOLPolymorphicType[?], args) =>
            val just = typ.nonEmptyThm.of(typ.freeTypeVars.zip(args).map { case (v, a) => v := a.asInstanceOf }*)
            val nextJ = justMap + (tt -> just)
            val nextOrd = ordMap + (tt -> depth)

            val preds = just.statement.right.toSeq ++ args

            foldIncremental(preds, depth + 1, nextJ, nextOrd)

          case App(f, arg) =>
            foldIncremental(Seq(f, arg), depth, justMap, ordMap)
          case Abs(v, body) =>
            ///////////////////////////////////////////////////////////////////////
            // NOTE ::::
            // This is a bit shady as we completely disregard the free variable
            // though the types here SHOULD NOT be dependent, so it should be fine.
            // fix this nicely when you need dependent types
            collectIncremental(body, depth, justMap, ordMap)
          case _ =>
            // other constants or variables
            // should not contribute to non-emptiness assumptions
            (justMap, ordMap)
    }

    /**
     * Remove non-emptiness assumptions about all HOL constant and instantiated
     * polymorphic types appearing in the assumption of the premise.
     */
    def allComposites(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      def composite(typ: Expr[Ind]): Boolean = typ match
        case _: HOLConstantType => true
        case _ ->: _ => true
        case Multiapp(_: HOLPolymorphicType[?], _) => true
        case _ => false

      // Resolve one visible composite assumption at a time and stop when none remain.
      prem.statement.left.collectFirst:
        case formula @ NonEmpty(bound, element, typ) if isSame(bound, element) && composite(typ) => formula -> typ
      match
        case None => have(prem.statement) by Restate.from(prem)
        case Some((formula, typ)) =>
          val generic = have(TypeNonEmptyProof(typ))
          val exact =
            if generic.statement.right.exists(isSame(_, formula)) then generic
            else have(generic.statement.left |- formula) by Restate.from(generic)
          val conclusion = prem.statement.copy(
            left = prem.statement.left.filterNot(isSame(_, formula)) ++ exact.statement.left
          )
          val discharged = have(conclusion) by Cut.withParameters(formula)(exact, prem)
          have(allComposites(discharged))
    }

    // Clean assumptions from cheapest and most local to recursively derived types.
    def all(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      ip.cleanAssumptions
      val h1 = have(Clean.allVariables(prem))
      val h2 = have(allInhabited(h1))
      val h3 = have(Clean.allTypeVars(h2))
      val h4 = have(Clean.allComposites(h3))
      val h5 = have(allInhabited(h4))
      val h6 = have(Clean.allTypeVars(h5))

      val distinctLeft = h6.statement.left.foldLeft(Set.empty[Expr[Prop]]): (seen, formula) =>
        if seen.exists(isSame(_, formula)) then seen else seen + formula
      val withoutDuplicates =
        if distinctLeft.size == h6.statement.left.size then h6
        else have(h6.statement.copy(left = distinctLeft)) by Restate.from(h6)

      val leftWithoutTruth = withoutDuplicates.statement.left.filterNot(isSame(_, ⊤))
      val withoutTruth =
        if leftWithoutTruth.size == withoutDuplicates.statement.left.size then withoutDuplicates
        else have(withoutDuplicates.statement.copy(left = leftWithoutTruth)) by Restate.from(withoutDuplicates)

      have(withoutTruth.statement) by Restate.from(withoutTruth)
    }
  }

}
