package lisa.hol

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Replacement.|
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightAnd
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.SimpleDeducedSteps.Discharge
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStepTactic.LeftSubstEq
import lisa.maths.SetTheory.Base.FoundationAxiom

object HOLBasics extends lisa.HOL {

  val A = typevar
  val B = typevar
  val T = typevar

  val x = typedvar(A)
  val y = typedvar(A)
  val z = typedvar(A)
  val P = typedvar(A ->: 𝔹)

  val f = typedvar(A ->: B)
  val g = typedvar(A ->: B)

  val p = typedvar(𝔹)
  val q = typedvar(𝔹)

  val φ = variable[Prop]

  val lib = summon[Library]

  ////////////////////////////////////////////////////
  // HOL Light preliminaries
  //
  // the section defines the basic HOL Light operators so as to prove the axioms
  // from its library as theorems.
  
  /**
   *     |- t = u
   *  ------------------
   *     |- u = t
   */
  object _SYM extends ProofTactic {
    def apply(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      prem.statement match {
        case HOLSequent(_, _, *(*(=:= #@ (typ), t), u)) =>
          prem.statement.left.foreach(ip.addAssumption(_))
          val s1 = have((t :: typ, u :: typ, t =:= u) |- u =:= t) by Weakening(eqSym of (A := typ, x := t, y := u))
          val s2 = have(Discharge(prem)(s1))
          val s3 = have(Discharge(have(HOLProofType(t)))(s2))
          val s4 = have(Discharge(have(HOLProofType(u)))(s3))
          have(Clean.all(s4))

        case _ =>
          return proof.InvalidProofTactic(s"The premise is not parseable as an HOL sequent") 
      }
    }
  } 

  /** SYM: t = u |- u = t */
  def SYM(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(prem: proof.Fact) = 
    have(_SYM(prem))

  /**
   * Truth as defined in HOL Light
   * 
   * ```
   *  let T_DEF = new_basic_definition
   *   `T = ((\p:bool. p) = (\p:bool. p))`;;
   * ```
   */
  val holT : HOLConstant = {
    val holT = DEF(fun(p, p) =:= fun(p, p))

    val typing_of_T = Theorem(holT :: 𝔹) {
      have((fun(p, p) =:= fun(p, p)) :: 𝔹) by Typecheck.prove
      thenHave(thesis) by Substitute(holT.definition)
    }
    HOLConstant(holT.id, 𝔹, typing_of_T)
  }

  val holTruth = HOLTheorem(holT):
    REFL(fun(p, p))
    thenHave(thesis) by Substitute(holT.definition)

  val oneTrue = HOLTheorem(One):
    have(thesis) by RightRefl

  /**
    * Higher-order embedded universal quantifier.
    * 
    * ```
    * let FORALL_DEF = new_basic_definition
    *   `(!) = \P:A->bool. P = \x. T`;;
    * ```
    */
  val hforall : HOLPolymorphicConstant[Ind >>: Ind] = {

    val f = typedvar(A ->: 𝔹)
    val a = typedvar(A)
    val x = typedvar(A)

    val hforall = DEF(λ(A, fun(f, f =:= fun(a, holT))))

    val typing_of_forall = Theorem(∀(A, nonEmpty(A) ==> hforall(A) :: ((A ->: 𝔹) ->: 𝔹))) {
      have(fun(f, f =:= fun(a, holT)) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      thenHave(∃(x, x :: A) |- hforall(A) :: ((A ->: 𝔹) ->: 𝔹)) by Substitute(hforall.definition)
      thenHave(nonEmpty(A) ==> hforall(A) :: ((A ->: 𝔹) ->: 𝔹)) by Restate
      thenHave(thesis) by RightForall
    }

    HOLPolymorphicConstant[Ind >>: Ind](hforall.id, FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: 𝔹)), typing_of_forall)
  }

  val hforallCorrect = HOLTheorem(
    (hforall(A) * P) <=> ∀(x :: A, P * x)
  ): 
    assumeAll
    val f = typedvar(A ->: 𝔹)

    val beta = have(hforall(A) * P === (P =:= fun(x, holT))) subproof:
      BETA(fun(P, P =:= fun(x, holT)) * P)
      val heq = thenHave((hforall(A) * P) =:= (P =:= fun(x, holT))) by Substitute(hforall.definition)
      have(thesis) by Tautology.from(
        heq, 
        eqAlign of (A := 𝔹, x := hforall(A) * P, y := P =:= fun(x, holT)), 
        have(HOLProofType(hforall(A) * P)),
        have(HOLProofType(P =:= fun(x, holT)))
      )

    val fwd = have((hforall(A) * P) ==> ∀(x :: A, P * x)) subproof: ip ?=>
      val `P x one` = 
        TRANS( // P * x =:= holT 
          MK_COMB( // P * x =:= fun(x, holT) * x
            ASSUME(P =:= fun(x, holT)), 
            REFL(x)
          ),
          BETA_CONV(fun(x, holT) * x) // fun(x, holT) * x =:= holT
        )
      val `P x holds` = // |- P * x
        EQ_MP(SYM(`P x one`), holTruth)

      lib.have(P =:= fun(x, holT) |- (x :: A) ==> P * x) by Weakening(`P x holds`)
      thenHave(P =:= fun(x, holT) |- ∀(x :: A, P * x)) by RightForall
      thenHave(hforall(A) * P |- ∀(x :: A, P * x)) by Substitute(beta)
      thenHave(thesis) by Weakening

    val bwd = have(∀(x :: A, P * x) ==> (hforall(A) * P)) subproof:
      have(∀(x :: A, P * x) |- (x :: A) ==> P * x) by InstantiateForall
      val `P x holds` = have(∀(x :: A, P * x) |- P * x) by Weakening(lastStep)
      val `P x one` = have(∀(x :: A, P * x) |- P * x =:= One) by Tautology.from(`P x holds`, One.justif, have(HOLProofType(P * x)), eqAlign of (A := 𝔹, x := P * x, y := One))
      val `P x T` = have(∀(x :: A, P * x) |- P * x =:= holT) by Substitute(holTruth)(`P x one`)
      val Peq = have(Clean.all( // P =:= fun(x, holT)
        TRANS(
          SYM(ETA(x, P)),
          ABS(x)(`P x T`),
        )
      ))
      have(∀(x :: A, P * x) |- hforall(A) * P) by Substitute(beta)(Peq)
      thenHave(thesis) by Weakening

    have(thesis) by RightAnd(fwd, bwd)

  /**
   * False as defined in HOL Light
   * 
   * ```
   * let F_DEF = new_basic_definition
   *  `F = (!p:bool. p)`;;
   * ```
   */
  val holF : HOLConstant = {
    val holF = DEF(hforall(𝔹) * fun(p, p))

    val typing_of_F = Theorem(holF :: 𝔹) {
      have(∃(p, p :: 𝔹) |- hforall(𝔹) * fun(p, p) :: 𝔹) by Typecheck.prove
      have(hforall(𝔹) * fun(p, p) :: 𝔹) by Cut(𝔹.nonEmptyThm, lastStep)
      thenHave(thesis) by Substitute(holF.definition)
    }

    HOLConstant(holF.id, 𝔹, typing_of_F)
  }

  val holFalseZero = HOLTheorem(holF === Zero):
    lib.have(∀(p :: 𝔹, fun(p, p) * p) |- ()) subproof:
      val beta = have((Zero :: 𝔹) |- (fun(p, p) * Zero === Zero)) subproof:
        BETA_CONV(fun(p, p) * Zero) 
        val conditional = thenHave(((fun(p, p) * Zero) :: 𝔹, Zero :: 𝔹) |- fun(p, p) * Zero === Zero) by Substitute(eqAlign)
        have(Discharge(have(HOLProofType(fun(p, p) * Zero)))(conditional))
      have(!(Zero === One)) by Weakening(`0 != 1`)
      thenHave((Zero :: 𝔹) |- !(fun(p, p) * Zero === One)) by Substitute(beta)
      lib.have((Zero :: 𝔹) /\ !(fun(p, p) * Zero === One)) by Tautology.from(Zero.justif, lastStep)
      thenHave(∃(p :: 𝔹, !(fun(p, p) * p))) by RightExists

    val conditional = thenHave((∃(p, p :: 𝔹), fun(p, p) :: (𝔹 ->: 𝔹), hforall(𝔹) * fun(p, p)) |- ()) by Substitute(hforallCorrect)
    have(Discharge(𝔹.nonEmptyThm, have(HOLProofType(fun(p, p))))(conditional))
    thenHave(holF |- ()) by Substitute(holF.definition)
    have(thesis) by Tautology.from(boolZeroXorOne of (x := holF), holF.justif, lastStep)

  /**
    * Higher-order embedded conjunction.
    * 
    * Defined as in HOL Light:
    * `(/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)`
    */
  val hand : HOLPolymorphicConstant[Ind] = {
    val f = typedvar(𝔹 ->: 𝔹 ->: 𝔹)

    val hand = DEF(fun(p, fun(q, fun(f, f * p * q) =:= fun(f, f * holT * holT))))

    val typing_of_and = Theorem(hand :: (𝔹 ->: 𝔹 ->: 𝔹)) {
      have(fun(p, fun(q, fun(f, f * p * q) =:= fun(f, f * holT * holT))) :: (𝔹 ->: 𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(hand.definition)
    }

    HOLPolymorphicConstant[Ind](hand.id, FunctionalClass(List(), List(), (𝔹 ->: 𝔹 ->: 𝔹)), typing_of_and)
  }

  val handCorrect = HOLTheorem(
    (hand * p * q === One) <=> ((p === One) /\ (q === One))
  ):
    assumeAll

    val f = typedvar(𝔹 ->: 𝔹 ->: 𝔹)
    val proj1 = fun(p, fun(q, p))
    val proj2 = fun(p, fun(q, q))

    val `beta f` = BETA(fun(f, f * p * q) * f) 

    val leftProjection = // proj1 * p * q = p
      TRANS(
        MK_COMB(BETA(proj1 * p), REFL(q)),
        BETA(fun(q, p) * q)
      )
    val rightProjection = // proj2 * p * q = q
      TRANS(
        MK_COMB(BETA(proj2 * p), REFL(q)),
        BETA(fun(q, q) * q)
      )

    val `beta hand` = have(
      hand * p * q === (fun(f, f * p * q) =:= fun(f, f * holT * holT))
    ) subproof {
      val inner = fun(f, f * p * q) =:= fun(f, f * holT * holT)
      val lq = fun(q, inner)
      val lp = fun(p, lq)
      val betaLp = // lp * p * q =:= inner
        TRANS(
          MK_COMB(
            BETA_CONV(lp * p), // lp * p = lq
            REFL(q)
          ),
          BETA_CONV(lq * q) // lq * q = inner
        )
      have(lp * p * q === inner) by Tautology.from(
        betaLp,
        have(HOLProofType(lp * p * q)),
        have(HOLProofType(inner)),
        eqAlign of (A := 𝔹, x := lp * p * q, y := inner)
      )
      thenHave(hand === lp |- hand * p * q === inner) by RightSubstEq.withParameters(Seq((hand, lp)), (Seq(x), x * p * q === inner))
      have(hand * p * q === inner) by Cut(hand.definition, lastStep)
    }

    val fwd = lib.have((hand * p * q === One) ==> ((p === One) /\ (q === One))) subproof:
      val reducedProof = have(fun(f, f * p * q) =:= fun(f, f * holT * holT) |- (p === One) /\ (q === One)) subproof {
        assumeAll
        val andEq = have(fun(f, f * p * q) =:= fun(f, f * holT * holT)) by Restate
        
        // ((\p q. f p q) f) holT holT = ((\p q. f p q) f) p q
        val appliedEq =
          have(Clean.all(
            // f holT holT = f p q
            SYM(TRANS(
              // (\p q. f p q) f holT holT = f p q
              TRANS(
                SYM(`beta f`),
                MK_COMB(andEq, REFL(f))
              ),
              have(Discharge(holT.justif)(`beta f` of (p := holT, q := holT)))
            ))
          ))
        val `p is true` = have(p) subproof:
          // project appliedEq onto first argument
          val proj1Eq = 
            have(Discharge(have(HOLProofType(proj1)))(appliedEq of (f := proj1)))
          // T =:= p
          val tEq = TRANS(
            SYM(
              have(Discharge(holT.justif)(leftProjection of (p := holT, q := holT)))
            ),
            TRANS(proj1Eq, leftProjection)
          )
          EQ_MP(tEq, holTruth)
          thenHave(thesis) by Weakening

        val `q is true` = have(q) subproof:
          // project appliedEq onto second argument
          val proj2Eq = 
            have(Discharge(have(HOLProofType(proj2)))(appliedEq of (f := proj2)))
          // T =:= q
          val tEq = TRANS(
            SYM(
              have(Discharge(holT.justif)(rightProjection of (p := holT, q := holT)))
            ),
            TRANS(proj2Eq, rightProjection)
          )
          EQ_MP(tEq, holTruth)
          thenHave(thesis) by Weakening

        have(p /\ q) by RightAnd(`p is true`, `q is true`)
        have(Clean.all(lastStep))
      }

      have((hand * p * q === One) |- ((p === One) /\ (q === One))) by Substitute(`beta hand`)(reducedProof)
    
    val bwd = have(((p === One) /\ (q === One)) ==> (hand * p * q === One)) subproof:
      val rfl = have(fun(f, f * holT * holT) :: (𝔹 ->: 𝔹 ->: 𝔹) ->: 𝔹 |- fun(f, f * holT * holT) =:= fun(f, f * holT * holT)) by Tautology.from(HOLHelperTheorems.eqRefl of (A := (𝔹 ->: 𝔹 ->: 𝔹) ->: 𝔹, x := fun(f, f * holT * holT)))
      have(fun(f, f * holT * holT) =:= fun(f, f * holT * holT)) by Cut(have(HOLProofType(fun(f, f * holT * holT))), rfl)
      thenHave((p === holT, q === holT) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by RightSubstEq.withParameters(Seq(p -> holT, q -> holT), (Seq(p, q), fun(f, f * p * q) =:= fun(f, f * holT * holT)))
      thenHave((holT === One, p === One, q === holT) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by LeftSubstEq.withParameters(Seq(holT -> One), (Seq(x), p === x))
      thenHave((holT === One, p === One, q === One) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by LeftSubstEq.withParameters(Seq(holT -> One), (Seq(x), q === x))
      lib.have((p === One, q === One) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by Cut(holTruth, lastStep)
      thenHave((p === One, q === One) |- hand * p * q === One) by Substitute(`beta hand`)
      have(Clean.all(lastStep))

    have(thesis) by RightAnd(fwd, bwd)

  /**
    * Higher-order embedded implication.
    * 
    * Defined as in HOL Light:
    * `(==>) = \p q. p /\ q <=> p`
    */
  val himp : HOLPolymorphicConstant[Ind] = {

    val p = typedvar(𝔹)
    val q = typedvar(𝔹)

    val himp = DEF(fun(p, fun(q, (hand * p * q) =:= p)))

    val typing_of_imp = Theorem(himp :: (𝔹 ->: 𝔹 ->: 𝔹)) {
      have(fun(p, fun(q, (hand * p * q) =:= p)) :: (𝔹 ->: 𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(himp.definition)
    }

    HOLPolymorphicConstant[Ind](himp.id, FunctionalClass(List(), List(), (𝔹 ->: 𝔹 ->: 𝔹)), typing_of_imp)
  }

  val himpCorrect = HOLTheorem(
    (himp * p * q === One) <=> ((p === One) ==> (q === One))
  ):
    assumeAll

    val apq = hand * p * q
    val apqtyping = have(HOLProofType(apq))

    val beta = have(
      (himp * p * q) === ((hand * p * q) =:= p)
    ) subproof:
      val inner = (hand * p * q) =:= p
      val lq = fun(q, inner)
      val lp = fun(p, lq)
      val betaLp = // lp * p * q =:= inner
        TRANS(
          MK_COMB(
            BETA_CONV(lp * p), // lp * p = lq
            REFL(q)
          ),
          BETA_CONV(lq * q) // lq * q = inner
        )
      have(lp * p * q === inner) by Tautology.from(
        betaLp,
        have(HOLProofType(lp * p * q)),
        have(HOLProofType(inner)),
        eqAlign of (A := 𝔹, x := lp * p * q, y := inner)
      )
      thenHave(thesis) by Substitute(himp.definition)

    val restricted = have((hand * p * q === p) <=> (p ==> q)) subproof:
      // case split on hand p  q 0 or 1, in each case it follows by
      // propositional reasoning on handCorrect
      val cases = have((apq === One) \/ (apq === Zero)) by Tautology.from(apqtyping, boolBivalence of (x := apq))

      val `and true` = have(apq === One |- (apq === p) <=> (p ==> q)) subproof:
        have(apq === One |- (One === p) <=> (p ==> q)) by Tautology.from(handCorrect)
        thenHave(apq === One |- (apq === p) <=> (p ==> q)) by RightSubstEq.withParameters(Seq(apq -> One), (Seq(x), (x === p) <=> (p ==> q)))

      val `and false` = have(apq === Zero |- (apq === p) <=> (p ==> q)) subproof:
        have(apq === Zero |- (Zero === p) <=> (p ==> q)) by Tautology.from(
          handCorrect, 
          boolBivalence of (x := p), 
          boolBivalence of (x := q), 
          boolBivalence of (x := apq), 
          boolZeroXorOne of (x := p),
          boolZeroXorOne of (x := q),
          boolZeroXorOne of (x := apq),
        )
        thenHave(apq === Zero |- (apq === p) <=> (p ==> q)) by RightSubstEq.withParameters(Seq(apq -> Zero), (Seq(x), (x === p) <=> (p ==> q)))

      have(thesis) by Tautology.from(cases, `and true`, `and false`)

    have((apq :: 𝔹) |- (hand * p * q =:= p) <=> (p ==> q)) by Substitute(eqAlign)(restricted)
    thenHave(apq :: 𝔹 |- (himp * p * q) <=> (p ==> q)) by Substitute(beta)
    have(thesis) by Cut(apqtyping, lastStep)

  /**
    * Higher-order embedded negation.
    * 
    * Defined as in HOL Light:
    * `(~) = \p. p ==> F`
    * where F (HOL False) is Zero in the set-theoretic embedding.
    */
  val hnot : HOLPolymorphicConstant[Ind] = {
    val p = typedvar(𝔹)

    val hnot = DEF(fun(p, himp * p * holF))

    val typing_of_not = Theorem(hnot :: (𝔹 ->: 𝔹)) {
      have(fun(p, himp * p * holF) :: (𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(hnot.definition)
    }

    HOLPolymorphicConstant[Ind](hnot.id, FunctionalClass(List(), List(), (𝔹 ->: 𝔹)), typing_of_not)
  }

  val hnotCorrect = HOLTheorem(
    (hnot * p === One) <=> !(p === One)
  ):
    assumeAll

    val hnoteq = 
      have(hnot === fun(p, himp * p * holF)) by Weakening(hnot.definition)
      have(hnot =:= fun(p, himp * p * holF)) by Tautology.from(
        lastStep, 
        have(HOLProofType(hnot)), 
        have(HOLProofType(fun(p, himp * p * holF))), 
        eqAlign of (A := (𝔹 ->: 𝔹), x := hnot, y := fun(p, himp * p * holF))
      )

    val beta = // hnot * p = himp * p * holF
      val betaConv = 
        TRANS(
          MK_COMB( // hnot * p = (\p. himp * p * holF) * p
            hnoteq,
            REFL(p)
          ),
          BETA_CONV(fun(p, himp * p * holF) * p)
        )
      have(hnot * p === himp * p * holF) by Tautology.from(
        betaConv,
        have(HOLProofType(hnot * p)),
        have(HOLProofType(himp * p * holF)),
        eqAlign of (A := 𝔹, x := hnot * p, y := himp * p * holF)
      )

    val impCorrect =
      have((p ==> Zero) <=> (p ==> Zero)) by Restate
      thenHave((Zero ∈ 𝔹) |- (himp * p * Zero) <=> (p ==> Zero)) by Substitute(himpCorrect)
      have((himp * p * Zero) <=> (p ==> Zero)) by Cut(Zero.justif, lastStep)
      thenHave((himp * p * holF) <=> (p ==> Zero)) by Substitute(holFalseZero)

    have((p ==> Zero) <=> !(p === One)) by Tautology.from(
      `0 != 1`,
      boolBivalence of (x := p),
      boolZeroXorOne of (x := p)
    )
    thenHave((himp * p * holF) <=> !(p === One)) by Substitute(impCorrect)
    thenHave((hnot * p) <=> !(p === One)) by Substitute(beta)

  /**
    * Higher-order embedded existential quantifier.
    * 
    * Defined as in HOL Light:
    * `(?) = \P:A->bool. !q. (!x. P x ==> q) ==> q`
    */
  val hexists : HOLPolymorphicConstant[Ind >>: Ind] = {

    val P = typedvar(A ->: 𝔹)
    val q = typedvar(𝔹)
    val x = typedvar(A)
    val y = typedvar(𝔹)
    val z = variable[Ind]

    val hexists = DEF(λ(A, fun(P, hforall(𝔹) * fun(q, himp * (hforall(A) * fun(x, himp * (P * x) * q)) * q))))
    val typing_of_exists = Theorem(∀(A, nonEmpty(A) ==> hexists(A) :: ((A ->: 𝔹) ->: 𝔹))):

      val faType = hforall(A) :: ((A ->: 𝔹) ->: 𝔹)
      val fbType = hforall(𝔹) :: ((𝔹 ->: 𝔹) ->: 𝔹)
      val impType = himp :: (𝔹 ->: 𝔹 ->: 𝔹)

      val faStep = have(faType) by Restate.from(hforall.justif of A)
      val fbStep = have(fbType) by Tautology.from(hforall.justif of 𝔹, 𝔹.nonEmptyThm)
      val imStep = have(impType) by Restate.from(himp.justif)

      have((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- fun(P, hforall(𝔹) * fun(q, himp * (hforall(A) * fun(x, himp * (P * x) * q)) * q)) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      thenHave((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- hexists(A) :: ((A ->: 𝔹) ->: 𝔹)) by Substitute(hexists.definition)
      lib.have(nonEmpty(A) ==> hexists(A) :: ((A ->: 𝔹) ->: 𝔹)) by Tautology.from(lastStep, hforall.justif of A, hforall.justif of 𝔹, himp.justif, 𝔹.nonEmptyThm)
      thenHave(thesis) by RightForall
    

    HOLPolymorphicConstant[Ind >>: Ind](hexists.id, FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: 𝔹)), typing_of_exists)
  }

  val hexistsCorrect = HOLTheorem(
    (hexists(A) * P) <=> ∃(x :: A, P * x)
  ):
    assumeAll

    // Abbreviations for the body of hexists(A) * P
    val innerImp = himp * (P * x) * q        // himp (P x) q
    val innerPred = fun(x, innerImp)          // λx. himp (P x) q
    val innerFA = hforall(A) * innerPred      // hforall A (λx. himp (P x) q)
    val outerImp = himp * innerFA * q         // himp (hforall A (λx. himp (P x) q)) q
    val outerPred = fun(q, outerImp)          // λq. himp (hforall A (λx. himp (P x) q)) q
    val body = hforall(𝔹) * outerPred        // hforall 𝔹 (λq. ...)

    // Step 1: Beta-reduce hexists(A) * P to body
    val beta = have(hexists(A) * P === body) subproof:
      BETA_CONV(fun(P, body) * P)
      val betaRed = thenHave((hexists(A) * P) =:= body) by Substitute(hexists.definition)
      have(thesis) by Tautology.from(
        betaRed,
        eqAlign of (A := 𝔹, x := hexists(A) * P, y := body),
        have(HOLProofType(hexists(A) * P)),
        have(HOLProofType(body))
      )

    // Correctness lemmas for the HOL connectives
    // Note: these use the outer (free) variables x, q

    // himp * (P * x) * q <=> (P * x ==> q)
    val innerImpLift = have(innerImp <=> (P * x ==> q)) subproof:
      have(thesis) by Tautology.from(
        himpCorrect of (p := P * x, q := q),
        have(HOLProofType(P * x)),
        have(HOLProofType(q))
      )

    // hforall(A) * innerPred <=> ∀(x :: A, innerPred * x)
    val innerFALift = have(innerFA <=> ∀(x :: A, innerPred * x)) subproof:
      val typing = have(HOLProofType(innerPred))
      val inst = have((innerPred :: (A ->: 𝔹), nonEmpty(A)) |- (innerFA <=> ∀(x :: A, innerPred * x))) by Weakening(hforallCorrect of (P := innerPred, x := x))
      have(thesis) by Cut(typing, inst)

    // himp * innerFA * q <=> (innerFA ==> q)
    val outerImpLift = have(outerImp <=> (innerFA ==> q)) subproof:
      have(thesis) by Tautology.from(
        himpCorrect of (p := innerFA, q := q),
        have(HOLProofType(innerFA)),
        have(HOLProofType(q))
      )

    // hforall(𝔹) * outerPred <=> ∀(q :: 𝔹, outerPred * q)
    val outerFALift = have(body <=> ∀(q :: 𝔹, outerPred * q)) subproof:
      val typing = have(HOLProofType(outerPred))
      have(thesis) by Tautology.from(
        hforallCorrect of (A := 𝔹, P := outerPred, x := q),
        typing,
        𝔹.nonEmptyThm
      )

    // Beta reductions
    val outerBeta = have(outerPred * q === outerImp) subproof:
      val bc = BETA_CONV(outerPred * q)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := outerPred * q, y := outerImp),
        have(HOLProofType(outerPred * q)),
        have(HOLProofType(outerImp))
      )

    val innerBeta = have(innerPred * x === innerImp) subproof:
      val bc = BETA_CONV(innerPred * x)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := innerPred * x, y := innerImp),
        have(HOLProofType(innerPred * x)),
        have(HOLProofType(innerImp))
      )

    // Forward direction: hexists(A) * P |- ∃(x :: A, P * x)
    val fwd = have((hexists(A) * P) ==> ∃(x :: A, P * x)) subproof:
      // Instantiate q := Zero for the forward direction
      val innerImp0 = himp * (P * x) * Zero
      val innerPred0 = fun(x, innerImp0)
      val innerFA0 = hforall(A) * innerPred0
      val outerImp0 = himp * innerFA0 * Zero

      // Beta and correctness with q=Zero
      val outerBeta0 = have(outerPred * Zero === outerImp0) subproof:
        val bc = BETA_CONV(outerPred * Zero)
        have(thesis) by Tautology.from(
          bc,
          eqAlign of (A := 𝔹, x := outerPred * Zero, y := outerImp0),
          have(HOLProofType(outerPred * Zero)),
          have(HOLProofType(outerImp0))
        )

      val outerImpLift0 = have(outerImp0 <=> (innerFA0 ==> Zero)) subproof:
        have(thesis) by Tautology.from(
          himpCorrect of (p := innerFA0, q := Zero),
          have(HOLProofType(innerFA0)),
          Zero.justif
        )

      val innerFALift0 = have(innerFA0 <=> ∀(x :: A, innerPred0 * x)) subproof:
        have(thesis) by Tautology.from(
          hforallCorrect of (P := innerPred0, x := x),
          have(HOLProofType(innerPred0))
        )

      val innerBeta0 = have(innerPred0 * x === innerImp0) subproof:
        val bc = BETA_CONV(innerPred0 * x)
        have(thesis) by Tautology.from(
          bc,
          eqAlign of (A := 𝔹, x := innerPred0 * x, y := innerImp0),
          have(HOLProofType(innerPred0 * x)),
          have(HOLProofType(innerImp0))
        )

      val innerImpLift0 = have(innerImp0 <=> (P * x ==> Zero)) subproof:
        have(thesis) by Tautology.from(
          himpCorrect of (p := P * x, q := Zero),
          have(HOLProofType(P * x)),
          Zero.justif
        )

      // innerPred0 * x <=> ¬(P * x)
      // because: innerPred0 * x === innerImp0 (by innerBeta0)
      //          innerImp0 <=> (P * x ==> Zero) (by innerImpLift0)
      //          (P * x ==> Zero) <=> ¬(P * x) (since 0 ≠ 1)
      val innerPredNeg = have(innerPred0 * x <=> !(P * x)) subproof:
        have(innerImp0 <=> !(P * x)) by Tautology.from(innerImpLift0, `0 != 1`)
        thenHave(thesis) by Substitute(innerBeta0)

      // Main argument:
      // From hexists(A) * P, derive body, then ∀(q :: 𝔹, outerPred * q)
      // Instantiate q := Zero: outerPred * Zero
      // outerPred * Zero === outerImp0, so outerImp0
      // outerImp0 <=> (innerFA0 ==> Zero), with 0 ≠ 1: ¬innerFA0
      // innerFA0 <=> ∀(x :: A, innerPred0 * x), so ¬∀(x :: A, innerPred0 * x)
      // innerPred0 * x <=> ¬(P * x), so ¬∀(x :: A, ¬(P * x))
      // Classically: ∃(x :: A, P * x)

      assume(hexists(A) * P)
      // hexists(A) * P |- body, using beta: hexists(A) * P === body
      have(hexists(A) * P) by Restate
      thenHave(body) by Substitute(beta)
      have(∀(q :: 𝔹, outerPred * q)) by Tautology.from(lastStep, outerFALift)
      thenHave((Zero :: 𝔹) ==> (outerPred * Zero)) by InstantiateForall(Zero)
      have(outerPred * Zero) by Tautology.from(lastStep, Zero.justif)
      // outerPred * Zero |- outerImp0, using outerBeta0: outerPred * Zero === outerImp0
      thenHave(outerImp0) by Substitute(outerBeta0)
      have(innerFA0 ==> Zero) by Tautology.from(lastStep, outerImpLift0)
      have(!(innerFA0)) by Tautology.from(lastStep, `0 != 1`)
      have(!(∀(x :: A, innerPred0 * x))) by Tautology.from(lastStep, innerFALift0)

      // Now: ¬∀(x :: A, innerPred0 * x) and innerPred0 * x <=> ¬(P * x)
      // Need: ∃(x :: A, P * x)
      // Strategy: convert ¬∀ to ∃¬ (quantifier duality via Restate),
      // then bridge ∃(x :: A, ¬(innerPred0 * x)) to ∃(x :: A, P * x)
      // using innerPredNeg + RightExists + LeftExists.

      // Step 1: ¬∀(x :: A, innerPred0 * x) ↔ ∃(x :: A, ¬(innerPred0 * x))
      // (Restate handles this since ∃ unfolds to ¬∀¬ in the equivalence checker)
      val existsNotInner = have(∃(x :: A, !(innerPred0 * x))) by Restate.from(lastStep)

      // Step 2: Bridge: ∃(x :: A, ¬(innerPred0 * x)) ⊢ ∃(x :: A, P * x)
      // From innerPredNeg: innerPred0 * x <=> ¬(P * x), so ¬(innerPred0 * x) <=> P * x
      have((x :: A, !(innerPred0 * x)) |- (x :: A) /\ (P * x)) by Tautology.from(innerPredNeg)
      thenHave((x :: A, !(innerPred0 * x)) |- ∃(x :: A, P * x)) by RightExists
      // Merge separate x ∈ A into the conjunction for LeftExists
      thenHave((x :: A) /\ !(innerPred0 * x) |- ∃(x :: A, P * x)) by Restate
      thenHave(∃(x :: A, !(innerPred0 * x)) |- ∃(x :: A, P * x)) by LeftExists

      // Step 3: Combine
      have(thesis) by Tautology.from(existsNotInner, lastStep)

    // Backward direction: ∃(x :: A, P * x) |- hexists(A) * P
    val bwd = have(∃(x :: A, P * x) ==> (hexists(A) * P)) subproof:
      // Goal: ∃(x :: A, P * x) |- hexists(A) * P
      // Strategy: prove FOL core ∃(x :: A, P * x) |- ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q)
      // then lift back to HOL terms.

      // FOL core:
      have((x :: A, q :: 𝔹, P * x, (x :: A) ==> ((P * x) ==> q)) |- q) by Restate
      thenHave((x :: A, q :: 𝔹, P * x, ∀(x :: A, (P * x) ==> q)) |- q) by LeftForall
      thenHave((x :: A) /\ (P * x) |- (q :: 𝔹) ==> (∀(x :: A, (P * x) ==> q) ==> q)) by Restate
      thenHave(∃(x, (x :: A) /\ (P * x)) |- (q :: 𝔹) ==> (∀(x :: A, (P * x) ==> q) ==> q)) by LeftExists
      thenHave(∃(x :: A, P * x) |- (q :: 𝔹) ==> (∀(x :: A, (P * x) ==> q) ==> q)) by Weakening
      thenHave(∃(x :: A, P * x) |- ∀(q :: 𝔹, ∀(x :: A, (P * x) ==> q) ==> q)) by RightForall
      val folResult = lastStep

      // Lift: convert ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q) to body (= hexists(A)*P via beta)
      // Key equivalences (all carry typing assumptions on the left):
      //   innerPred * x <=> (P * x ==> q)   [innerImpLift + innerBeta] — has x ∈ A, q ∈ 𝔹 on left
      //   innerFA <=> ∀(x :: A, innerPred * x)  [innerFALift]
      //   outerImp <=> (innerFA ==> q)       [outerImpLift] — has innerFA ∈ 𝔹, q ∈ 𝔹 on left
      //   outerPred * q === outerImp         [outerBeta]
      //   body <=> ∀(q :: 𝔹, outerPred * q) [outerFALift]

      // innerPredEquiv: innerPred * x <=> (P * x ==> q)
      val innerPredEquiv = have(innerPred * x <=> (P * x ==> q)) subproof:
        have(innerImp <=> (P * x ==> q)) by Restate.from(innerImpLift)
        thenHave(thesis) by Substitute(innerBeta)

      // Forward: ∀(x :: A, P * x ==> q) ⊢ innerFA  (with q ∈ 𝔹 on left)
      have(∀(x :: A, P * x ==> q) |- (x :: A) ==> (P * x ==> q)) by InstantiateForall
      // Combine with innerPredEquiv to get innerPred * x; need x ∈ A and q ∈ 𝔹 for innerPredEquiv
      have((∀(x :: A, P * x ==> q), x :: A, q :: 𝔹) |- innerPred * x) by Tautology.from(lastStep, innerPredEquiv)
      // Move x ∈ A to right so RightForall can generalize over x
      thenHave((∀(x :: A, P * x ==> q), q :: 𝔹) |- (x :: A) ==> innerPred * x) by Restate
      thenHave((∀(x :: A, P * x ==> q), q :: 𝔹) |- ∀(x :: A, innerPred * x)) by RightForall
      have((∀(x :: A, P * x ==> q), q :: 𝔹) |- innerFA) by Tautology.from(lastStep, innerFALift)
      val forallToInnerFA = lastStep

      // Reverse: innerFA ⊢ ∀(x :: A, P * x ==> q)  (with q ∈ 𝔹 on left)
      have(∀(x :: A, innerPred * x) |- (x :: A) ==> innerPred * x) by InstantiateForall
      have((∀(x :: A, innerPred * x), x :: A, q :: 𝔹) |- (P * x ==> q)) by Tautology.from(lastStep, innerPredEquiv)
      thenHave((∀(x :: A, innerPred * x), q :: 𝔹) |- (x :: A) ==> (P * x ==> q)) by Restate
      thenHave((∀(x :: A, innerPred * x), q :: 𝔹) |- ∀(x :: A, P * x ==> q)) by RightForall
      have((innerFA, q :: 𝔹) |- ∀(x :: A, P * x ==> q)) by Tautology.from(lastStep, innerFALift)
      val innerFAToForall = lastStep

      // outerImp <=> (∀(x :: A, P * x ==> q) ==> q)  — with q ∈ 𝔹 on left
      have((q :: 𝔹) |- outerImp <=> (∀(x :: A, P * x ==> q) ==> q)) by Tautology.from(
        outerImpLift, forallToInnerFA, innerFAToForall, HOLProofType(innerFA)
      )
      val outerImpFOL = lastStep

      // outerPred * q <=> outerImp
      val outerPredEquiv = have(outerPred * q <=> outerImp) subproof:
        have(outerImp <=> outerImp) by Restate
        thenHave(thesis) by Substitute(outerBeta)

      // outerPred * q <=> (∀(x :: A, P * x ==> q) ==> q) — with q ∈ 𝔹 on left
      have((q :: 𝔹) |- outerPred * q <=> (∀(x :: A, P * x ==> q) ==> q)) by Tautology.from(outerPredEquiv, outerImpFOL)
      val outerPredFOL = lastStep

      // Convert: ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q) |- ∀(q :: 𝔹, outerPred * q)
      have(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- (q :: 𝔹) ==> (∀(x :: A, P * x ==> q) ==> q)) by InstantiateForall
      // Combine with outerPredFOL: carry q ∈ 𝔹 explicitly
      have((∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q), q :: 𝔹) |- outerPred * q) by Tautology.from(lastStep, outerPredFOL)
      // Move q ∈ 𝔹 to right for RightForall
      thenHave(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- (q :: 𝔹) ==> outerPred * q) by Restate
      thenHave(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- ∀(q :: 𝔹, outerPred * q)) by RightForall

      // body
      have(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- body) by Tautology.from(lastStep, outerFALift)
      thenHave(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- hexists(A) * P) by Substitute(beta)

      // Cut folResult and lastStep on ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q)
      val cutResult = have(∃(x :: A, P * x) |- hexists(A) * P) by Cut(folResult, lastStep)
      have(thesis) by Restate.from(cutResult)

    have(thesis) by RightAnd(fwd, bwd)

  // defining select

  private def selectProp(x: Expr[Ind]) = (x :: A) /\ (∃(y, (y :: A) /\ (P * y === One)) ==> (P * x === One))
  private val selectTerm = ε(x, selectProp(x))

  private val selectWellDefined = HOLTheorem(selectProp(selectTerm)):
    assumeAll

    val existsCase = have(∃(y, (y :: A) /\ (P * y === One)) |- selectProp(selectTerm)) subproof:
      lib.have((y :: A) /\ (P * y === One) |- selectProp(y)) by Restate
      thenHave((y :: A) /\ (P * y === One) |- selectProp(selectTerm)) by RightEpsilon.withParameters(selectProp(y), y, y)
      thenHave(∃(y, (y :: A) /\ (P * y === One)) |- selectProp(selectTerm)) by LeftExists

    val emptyCase = have((nonEmpty(A), ! ∃(y, (y :: A) /\ (P * y === One))) |- selectProp(selectTerm)) subproof:
      assume(nonEmpty(A), ! ∃(y, (y :: A) /\ (P * y === One)))
      have((y :: A) |- selectProp(y)) by Restate
      thenHave((y :: A) |- selectProp(selectTerm)) by RightEpsilon.withParameters(selectProp(y), y, y)
      thenHave(∃(y, y :: A) |- selectProp(selectTerm)) by LeftExists

    have(thesis) by Tautology.from(existsCase, emptyCase)


  /**
   * Higher-order embedded choice operator.
   * 
   * Deferred to epsilon terms internally
   */
  val hselect : HOLPolymorphicConstant[Ind >>: Ind] = {
    val P = typedvar(A ->: 𝔹)
    val x = typedvar(A)
    val y = typedvar(A)

    val hselect = DEF(λ(A, fun(P, ε(x, 
      // the result is always in A
      (x :: A) /\
      // but if there is a witness, then the result satisfies P as well
      (∃(y, (y :: A) /\ (P * y === One)) ==> (P * x === One))
    ))))

    val typing_of_select = Theorem(∀(A, nonEmpty(A) ==> hselect(A) :: ((A ->: 𝔹) ->: A))):
      lib.have((nonEmpty(A), (P :: (A ->: 𝔹))) |- selectProp(selectTerm)) by Weakening(selectWellDefined)
      thenHave(nonEmpty(A) |- (P :: (A ->: 𝔹)) ==> (selectTerm :: A)) by Weakening
      val epsType = thenHave(nonEmpty(A) |- ∀(P :: (A ->: 𝔹), selectTerm :: A)) by RightForall

      val T1 = variable[Ind]
      val T2 = variable[Ind >>: Ind]
      val e = variable[Ind >>: Ind]

      lib.have(nonEmpty(A) |- fun(P, selectTerm) :: ((A ->: 𝔹) ->: A)) by Cut(epsType, TAbs of (T1 := (A ->: 𝔹), T2 := λ(x, A), e := λ(P, selectTerm)))
      thenHave(nonEmpty(A) |- hselect(A) :: ((A ->: 𝔹) ->: A)) by Substitute(hselect.definition)
      thenHave(nonEmpty(A) ==> hselect(A) :: ((A ->: 𝔹) ->: A)) by Restate
      thenHave(thesis) by RightForall

    HOLPolymorphicConstant[Ind >>: Ind](hselect.id, FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: A)), typing_of_select)
  }

  // define ONE_ONE
  // let ONE_ONE = new_definition
  //   `ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;
  val hOneOne : HOLPolymorphicConstant[Ind >>: Ind >>: Ind] = {
    
    val f = typedvar(A ->: B)
    val x = typedvar(A)
    val y = typedvar(A)

    val hOneOne = DEF(λ(A, λ(B, 
      fun(f, 
        hforall(A) * fun(x, // ∀ x 
          hforall(A) * fun(y, // ∀ y
            // f x = f y ==> x = y
            himp 
              * (f * x =:= f * y) 
              * (x =:= y)
    ))))))
    
    val typing_of_oneone = Theorem(∀(A, ∀(B, (nonEmpty(A) /\ nonEmpty(B)) ==> hOneOne(A)(B) :: ((A ->: B) ->: 𝔹)))) {
      lib.have((nonEmpty(A), nonEmpty(B)) |- fun(f, hforall(A) * fun(x, hforall(A) * fun(y, himp * ((f * x) =:= (f * y)) * (x =:= y)))) :: ((A ->: B) ->: 𝔹)) by Typecheck.prove
      thenHave((nonEmpty(A), nonEmpty(B)) |- hOneOne(A)(B) :: ((A ->: B) ->: 𝔹)) by Substitute(hOneOne.definition)
      thenHave((nonEmpty(A) /\ nonEmpty(B)) ==> hOneOne(A)(B) :: ((A ->: B) ->: 𝔹)) by Restate
      thenHave(thesis) by Generalize
    }

    HOLPolymorphicConstant[Ind >>: Ind >>: Ind](hOneOne.id, FunctionalClass(List(None, None), List(A, B), ((A ->: B) ->: 𝔹)), typing_of_oneone)
  }

  // define ONTO
  // let ONTO = new_definition
  //   `ONTO(f:A->B) = !y. ?x. y = f x`;;
  val hOnto : HOLPolymorphicConstant[Ind >>: Ind >>: Ind] = {

    val f = typedvar(A ->: B)
    val x = typedvar(A)
    val y = typedvar(B)

    val hOnto = DEF(λ(A, λ(B,
      fun(f,
        hforall(B) * fun(y, // ∀ y
          hexists(A) * fun(x, // ∃ x
            // y = f x
            y =:= (f * x) 
    ))))))

    val typing_of_onto = Theorem(∀(A, ∀(B, (nonEmpty(A) /\ nonEmpty(B)) ==> hOnto(A)(B) :: ((A ->: B) ->: 𝔹)))) {
      lib.have((nonEmpty(A), nonEmpty(B)) |- fun(f, hforall(B) * fun(y, hexists(A) * fun(x, y =:= (f * x)))) :: ((A ->: B) ->: 𝔹)) by Typecheck.prove
      thenHave((nonEmpty(A), nonEmpty(B)) |- hOnto(A)(B) :: ((A ->: B) ->: 𝔹)) by Substitute(hOnto.definition)
      thenHave((nonEmpty(A) /\ nonEmpty(B)) ==> hOnto(A)(B) :: ((A ->: B) ->: 𝔹)) by Restate
      thenHave(thesis) by Generalize
    }

    HOLPolymorphicConstant[Ind >>: Ind >>: Ind](hOnto.id, FunctionalClass(List(None, None), List(A, B), ((A ->: B) ->: 𝔹)), typing_of_onto)
  }

  def inductive(s: Expr[Ind]): Expr[Prop] = 
    (∅ ∈ s) /\ (∀(x, (x ∈ s) ==> ⋃(unorderedPair(x, unorderedPair(x, x))) ∈ s))

  val ind : HOLConstantType = {

    // ind is the set as defined by the set-theoretic infinity axiom
    val ind = DEF(ε(z, inductive(z)))

    val nonEmpty = Theorem(∃(x, x ∈ ind)):
      // the empty set is in any chosen inductive set
      lib.have(inductive(y) |- inductive(y)) by Restate
      thenHave(inductive(y) |- inductive(ε(z, inductive(z)))) by RightEpsilon.withParameters(inductive(z), z, y)
      thenHave(inductive(y) |- ∅ ∈ ε(z, inductive(z))) by Weakening

      thenHave((inductive(y), ind === ε(z, inductive(z))) |- ∅ ∈ ind) by RightSubstEq.withParameters(Seq((ε(z, inductive(z)), ind)), (Seq(z), ∅ ∈ z))
      lib.have(inductive(y) |- ∅ ∈ ind) by Cut(ind.definition, lastStep)

      // an inductive set actually exists, so our choice is justified
      thenHave(∃(y, inductive(y)) |- ∅ ∈ ind) by LeftExists
      lib.have(∅ ∈ ind) by Cut(lib.infinityAxiom, lastStep)

      thenHave(∃(x, x ∈ ind)) by RightExists

    HOLConstantType(ind.id, nonEmpty)
  }

  val indIsInductive = Theorem(inductive(ind)):
      lib.have(inductive(y) |- inductive(y)) by Restate
      thenHave(inductive(y) |- inductive(ε(z, inductive(z)))) by RightEpsilon.withParameters(inductive(z), z, y)

      thenHave((inductive(y), ind === ε(z, inductive(z))) |- inductive(ind)) by RightSubstEq.withParameters(Seq((ε(z, inductive(z)), ind)), (Seq(z), inductive(z)))
      lib.have(inductive(y) |- inductive(ind)) by Cut(ind.definition, lastStep)

      thenHave(∃(y, inductive(y)) |- inductive(ind)) by LeftExists
      lib.have(inductive(ind)) by Cut(lib.infinityAxiom, lastStep)

  val succ : TypedConstant = {
    val i = typedvar(ind)
    val succ = DEF(fun(i, ⋃(unorderedPair(i, unorderedPair(i, i)))))

    val succType = Theorem(succ :: (ind ->: ind)):
      val indClosed = lib.have(∀(i :: ind, ⋃(unorderedPair(i, unorderedPair(i, i))) :: ind)) by Weakening(indIsInductive)

      val T1 = variable[Ind]
      val T2 = variable[Ind >>: Ind]
      val e = variable[Ind >>: Ind]

      lib.have(fun(i, ⋃(unorderedPair(i, unorderedPair(i, i)))) :: (ind ->: ind)) by Cut(lastStep, TAbs of (T1 := ind, T2 := λ(x, ind), e := λ(i, ⋃(unorderedPair(i, unorderedPair(i, i))))))
      thenHave(succ :: (ind ->: ind)) by Substitute(succ.definition)

    TypedConstant(succ.id, ind ->: ind, succType)
  } 

  val succOneOne = HOLTheorem(hOneOne(ind)(ind) * succ):
    // target: succ x = succ y ==> x = y

    val i = typedvar(ind)
    val x = typedvar(ind)
    val y = typedvar(ind)
    val f = typedvar(ind ->: ind)

    def expanded(i: Expr[Ind]) = ⋃(unorderedPair(i, unorderedPair(i, i)))
    val expandedTyping = have(expanded(i) :: ind) subproof:
      have(∀(i :: ind, expanded(i) :: ind)) by Weakening(indIsInductive)
      thenHave(i :: ind ==> expanded(i) :: ind) by InstantiateForall(i)

    val betaSucc = have(succ * i === expanded(i)) subproof:
      val T = variable[Ind]
      val e = variable[Ind >>: Ind]
      val e2 = variable[Ind]
      have(fun(i, expanded(i)) * i === expanded(i)) by Weakening(BetaReduction of (T := ind, e2 := i, e := λ(i, expanded(i))))
      thenHave(thesis) by Substitute(succ.definition)

    val betaOneOne = have(hOneOne(ind)(ind) * succ === hforall(ind) * fun(x, hforall(ind) * fun(y, himp * ((succ * x) =:= (succ * y)) * (x =:= y)))) subproof:
      def ooDef(f: Expr[Ind]) = hforall(ind) * fun(x, hforall(ind) * fun(y, himp * ((f * x) =:= (f * y)) * (x =:= y)))
      val beta = BETA_CONV(fun(f, ooDef(f)) * succ)
      have(hOneOne(ind)(ind) * succ =:= ooDef(succ)) by Substitute(hOneOne.definition of (A := ind, B := ind))(beta)
      val cond = have(((hOneOne(ind)(ind) * succ) :: 𝔹, ooDef(succ) :: 𝔹) |- hOneOne(ind)(ind) * succ === ooDef(succ)) by Substitute(eqAlign)(lastStep)
      have(Discharge(HOLProofType(hOneOne(ind)(ind) * succ), HOLProofType(ooDef(succ)))(cond))

    val oneOneDirect = have((succ * x) === (succ * y) |- x === y) subproof:
      assume(x :: ind, y :: ind)
      have(expanded(x) === expanded(y) |- x === y) subproof:
        // Abbreviations
        val ux = unorderedPair(x, unorderedPair(x, x)) // {x, {x, x}}
        val uy = unorderedPair(y, unorderedPair(y, y)) // {y, {y, y}}
        val w = variable[Ind]

        // Lemma: x ∈ expanded(x)
        // Proof: x ∈ {x,x} by pairAxiom, and {x,x} ∈ {x, {x,x}} by pairAxiom,
        //        so x ∈ ⋃{x, {x,x}} by unionAxiom
        val xinex = have(x ∈ expanded(x)) subproof:
          have(x ∈ unorderedPair(x, x)) by Tautology.from(pairAxiom of (z := x, x := x, y := x))
          val xInSingleton = lastStep
          have(unorderedPair(x, x) ∈ ux) by Tautology.from(pairAxiom of (z := unorderedPair(x, x), x := x, y := unorderedPair(x, x)))
          have(x ∈ unorderedPair(x, x) /\ unorderedPair(x, x) ∈ ux) by Tautology.from(xInSingleton, lastStep)
          have(∃(w, x ∈ w /\ w ∈ ux)) by RightExists.withParameters(unorderedPair(x, x))(lastStep)
          have(x ∈ expanded(x)) by Tautology.from(lastStep, unionAxiom of (z := x, x := ux))

        // Lemma: x ∈ expanded(y) ⊢ x ∈ y ∨ x = y
        // Proof: By unionAxiom, ∃w. w ∈ {y, {y,y}} ∧ x ∈ w.
        //   - If w = y, then x ∈ y.
        //   - If w = {y,y}, then x ∈ {y,y}, so x = y by pairAxiom.
        val membershipLemma = have(x ∈ ⋃(uy) |- (x ∈ y) \/ (x === y)) subproof:
          // case w = y: x ∈ w gives x ∈ y
          val caseY = 
            have((x ∈ w, w === y) |- (x ∈ w) \/ (x === w)) by Restate
            have((x ∈ w, w === y) |- (x ∈ y) \/ (x === y)) by RightSubstEq.withParameters(Seq(w -> y), (Seq(w), (x ∈ w) \/ (x === w)))(lastStep)
          // case w = {y,y}: x ∈ w gives x ∈ {y,y}, hence x = y
          val caseSingleton = have((x ∈ w, w === unorderedPair(y, y)) |- (x ∈ y) \/ (x === y)) subproof:
            have((x ∈ w, w === unorderedPair(y, y)) |- x ∈ unorderedPair(y, y)) by Congruence
            lib.have(thesis) by Tautology.from(lastStep, pairAxiom of (z := x, x := y, y := y))
          // combine: w ∈ {y, {y,y}} means w = y ∨ w = {y,y}
          have((x ∈ w, w ∈ uy) |- (x ∈ y) \/ (x === y)) by Tautology.from(
            pairAxiom of (z := w, x := y, y := unorderedPair(y, y)),
            caseY, caseSingleton
          )
          have((x ∈ w) /\ (w ∈ uy) |- (x ∈ y) \/ (x === y)) by Weakening(lastStep)
          have(∃(w, (x ∈ w) /\ (w ∈ uy)) |- (x ∈ y) \/ (x === y)) by LeftExists.withParameters((x ∈ w) /\ (w ∈ uy), w)(lastStep)
          lib.have(thesis) by Tautology.from(lastStep, unionAxiom of (z := x, x := uy))

        val xToy = have(expanded(x) === expanded(y) |- (x ∈ y) \/ (x === y)) subproof:
          have(x ∈ ⋃(ux) |- x ∈ ⋃(ux)) by Hypothesis
          have((x ∈ ⋃(ux), ⋃(ux) === ⋃(uy)) |- x ∈ ⋃(uy)) by RightSubstEq.withParameters(
            Seq((⋃(ux), ⋃(uy))), (Seq(w), x ∈ w)
          )(lastStep)
          have(expanded(x) === expanded(y) |- x ∈ ⋃(uy)) by Cut(xinex, lastStep)
          lib.have(thesis) by Cut(lastStep, membershipLemma)

        val yTox = xToy of (x := y, y := x)
        val cycle = have(x ∈ y /\ y ∈ x |- ()) by Weakening(FoundationAxiom.membershipAsymmetric)
        have(thesis) by Tautology.from(xToy, yTox, cycle)
      thenHave((succ * x) === (succ * y) |- x === y) by Substitute(betaSucc)

    val oneOneImp = have(himp * ((succ * x) =:= (succ * y)) * (x =:= y)) subproof:
      have(((succ * x) :: ind, (succ * y) :: ind, (succ * x) =:= (succ * y)) |- (x =:= y)) by Substitute(eqAlign)(oneOneDirect)
      val cond1 = have(((succ * x) :: ind, (succ * y) :: ind) |- ((succ * x) =:= (succ * y)) ==> (x =:= y)) by Weakening(lastStep)
      have(Discharge(HOLProofType(succ * x), HOLProofType(succ * y))(cond1))
      val cond2 = have((((succ * x) =:= (succ * y)) :: 𝔹, (x =:= y) :: 𝔹) |- himp * ((succ * x) =:= (succ * y)) * (x =:= y)) by Substitute(himpCorrect)(lastStep)
      have(Discharge(HOLProofType((succ * x) =:= (succ * y)), HOLProofType(x =:= y))(cond2))

    val oneOneForall = have(hforall(ind) * fun(x, hforall(ind) * fun(y, himp * ((succ * x) =:= (succ * y)) * (x =:= y)))) subproof:
      val p1 = fun(y, himp * ((succ * x) =:= (succ * y)) * (x =:= y))
      val p2 = fun(x, hforall(ind) * p1)
      val inner1 =
        // (\y . himp * ((succ * x) =:= (succ * y)) * (x =:= y)) * y
        EQ_MP(
          SYM(BETA_CONV(p1 * y)),
          oneOneImp
        )
      thenHave((x :: ind, ∃(x, x :: ind)) |- (y :: ind) ==> (p1 * y)) by Weakening
      thenHave((x :: ind, ∃(x, x :: ind)) |- ∀(y :: ind, p1 * y)) by RightForall
      thenHave((x :: ind, ∃(x, x :: ind), p1 :: ind ->: 𝔹) |- hforall(ind) * p1) by Substitute(hforallCorrect)
      val forall1 = have((x :: ind, ∃(x, x :: ind)) |- hforall(ind) * p1) by Cut(HOLProofType(p1), lastStep)
      val inner2 = 
        // (\x. hforall(ind) * fun(y, himp * ((succ * x) =:= (succ * y)) * (x =:= y))) * x
        EQ_MP(
          SYM(BETA_CONV(p2 * x)),
          forall1
        )
      thenHave((∃(x, x :: ind)) |- (x :: ind) ==> (p2 * x)) by Weakening
      thenHave((∃(x, x :: ind)) |- ∀(x :: ind, p2 * x)) by RightForall
      val stmt = thenHave((∃(x, x :: ind), p2 :: ind ->: 𝔹) |- hforall(ind) * p2) by Substitute(hforallCorrect)
      
      lib.have(Discharge(HOLProofType(p2), ind.nonEmptyThm)(stmt))

    have(hOneOne(ind)(ind) * succ) by Substitute(betaOneOne)(oneOneForall)

  val succNotOnto = HOLTheorem(hnot * (hOnto(ind)(ind) * succ)):
    // target: ¬(∀y ∈ ind. ∃x ∈ ind. y = succ(x))
    // witness: y = ∅ — empty set is in ind but is never a successor

    val i = typedvar(ind)
    val x = typedvar(ind)
    val y = typedvar(ind)
    val f = typedvar(ind ->: ind)
    val w = variable[Ind]

    def expanded(i: Expr[Ind]) = ⋃(unorderedPair(i, unorderedPair(i, i)))

    // Step 1: Beta-reduce hOnto(ind)(ind) * succ
    def ontoDef(f: Expr[Ind]) = hforall(ind) * fun(y, hexists(ind) * fun(x, y =:= (f * x)))
    val ontoBody = ontoDef(succ)

    val betaOnto = have(hOnto(ind)(ind) * succ === ontoBody) subproof:
      val beta = BETA_CONV(fun(f, ontoDef(f)) * succ)
      have(hOnto(ind)(ind) * succ =:= ontoBody) by Substitute(hOnto.definition of (A := ind, B := ind))(beta)
      val cond = have(((hOnto(ind)(ind) * succ) :: 𝔹, ontoBody :: 𝔹) |- hOnto(ind)(ind) * succ === ontoBody) by Substitute(eqAlign)(lastStep)
      have(Discharge(HOLProofType(hOnto(ind)(ind) * succ), HOLProofType(ontoBody))(cond))

    // Step 2: betaSucc — succ * x === expanded(x)
    val betaSucc = have(succ * x === expanded(x)) subproof:
      val T = variable[Ind]
      val e = variable[Ind >>: Ind]
      val e2 = variable[Ind]
      have(fun(x, expanded(x)) * x === expanded(x)) by Weakening(BetaReduction of (T := ind, e2 := x, e := λ(x, expanded(x))))
      thenHave(thesis) by Substitute(succ.definition)

    // Step 3: Core set theory — ∅ ≠ succ(x)
    // Proof: x ∈ succ(x) = expanded(x), but x ∉ ∅, so ∅ ≠ expanded(x)
    val emptyNotSucc = have(!(∅ === expanded(x))) subproof:
      // x ∈ expanded(x) (same as xinex in succOneOne)
      val ux = unorderedPair(x, unorderedPair(x, x))
      val xinex = have(x ∈ expanded(x)) subproof:
        have(x ∈ unorderedPair(x, x)) by Tautology.from(pairAxiom of (z := x, x := x, y := x))
        val xInSingleton = lastStep
        have(unorderedPair(x, x) ∈ ux) by Tautology.from(pairAxiom of (z := unorderedPair(x, x), x := x, y := unorderedPair(x, x)))
        have(x ∈ unorderedPair(x, x) /\ unorderedPair(x, x) ∈ ux) by Tautology.from(xInSingleton, lastStep)
        have(∃(w, x ∈ w /\ w ∈ ux)) by RightExists.withParameters(unorderedPair(x, x))(lastStep)
        have(x ∈ expanded(x)) by Tautology.from(lastStep, unionAxiom of (z := x, x := ux))

      // x ∉ ∅
      val xNotInEmpty = have(!(x ∈ ∅)) by Weakening(emptySetAxiom of (x := x))

      // If expanded(x) = ∅, then x ∈ ∅ (since x ∈ expanded(x) and expanded(x) = ∅), contradiction
      have(x ∈ expanded(x) |- x ∈ expanded(x)) by Hypothesis
      have((x ∈ expanded(x), expanded(x) === ∅) |- x ∈ ∅) by RightSubstEq.withParameters(
        Seq((expanded(x), ∅)), (Seq(w), x ∈ w)
      )(lastStep)
      have(expanded(x) === ∅ |- x ∈ ∅) by Cut(xinex, lastStep)
      have(!(expanded(x) === ∅)) by Tautology.from(lastStep, xNotInEmpty)
      have(!(∅ === expanded(x))) by Restate.from(lastStep)

    // Step 4: ∅ ≠ succ * x (substitute betaSucc)
    val emptyNotSuccApp = have(!(∅ === (succ * x))) subproof:
      have(thesis) by Substitute(betaSucc)(emptyNotSucc)

    // Step 5: Lift to HOL  
    // Strategy: prove ¬∀(y :: ind, outerPred * y) at the FOL level, then lift.
    // outerPred = fun(y, hexists(ind) * fun(x, y =:= (succ * x)))
    // For y = ∅: outerPred * ∅ <=> ∃(x :: ind, ∅ = succ * x) (via hexistsCorrect + beta)
    // But ∅ ≠ succ * x for any x (emptyNotSuccApp), so outerPred * ∅ is false.

    val outerPred = fun(y, hexists(ind) * fun(x, y =:= (succ * x)))

    // Step 5a: hforall(ind) * outerPred <=> ∀(y :: ind, outerPred * y)
    val forallLift = have(hforall(ind) * outerPred <=> ∀(y :: ind, outerPred * y)) subproof:
      have(thesis) by Tautology.from(
        hforallCorrect of (A := ind, P := outerPred, x := y),
        have(HOLProofType(outerPred)),
        ind.nonEmptyThm
      )

    // Step 5b: Set up inner existential for arbitrary y
    // hexists(ind) * fun(x, y =:= (succ * x)) <=> ∃(x :: ind, fun(x, y =:= (succ * x)) * x)
    val innerExPred = fun(x, y =:= (succ * x))
    val innerExLift = have(hexists(ind) * innerExPred <=> ∃(x :: ind, innerExPred * x)) subproof:
      have(thesis) by Tautology.from(
        hexistsCorrect of (A := ind, P := innerExPred, x := x),
        have(HOLProofType(innerExPred)),
        ind.nonEmptyThm
      )

    // innerExPred * x === (y =:= (succ * x)) by beta reduction
    val innerExBeta = have(innerExPred * x === (y =:= (succ * x))) subproof:
      val bc = BETA_CONV(innerExPred * x)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := innerExPred * x, y := y =:= (succ * x)),
        have(HOLProofType(innerExPred * x)),
        have(HOLProofType(y =:= (succ * x)))
      )

    // outerPred * y === hexists(ind) * innerExPred by beta reduction
    val outerBeta = have(outerPred * y === hexists(ind) * innerExPred) subproof:
      val bc = BETA_CONV(outerPred * y)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := outerPred * y, y := hexists(ind) * innerExPred),
        have(HOLProofType(outerPred * y)),
        have(HOLProofType(hexists(ind) * innerExPred))
      )

    // Step 5c: outerPred * y <=> ∃(x :: ind, y === succ * x)
    // Via outerBeta + innerExLift + innerExBeta + eqAlign
    val outerPredFOL = have(outerPred * y <=> ∃(x :: ind, y === (succ * x))) subproof:
      // eqAlign: (y =:= (succ * x) === One) <=> (y === succ * x)
      val eqAlignInst = have((y =:= (succ * x) === One) <=> (y === (succ * x))) subproof:
        have(((y :: ind, (succ * x) :: ind) |- (y =:= (succ * x) === One) <=> (y === (succ * x)))) by Weakening(eqAlign of (A := ind, x := y, y := succ * x))
        have(Discharge(HOLProofType(y), HOLProofType(succ * x))(lastStep))
      
      // innerExPred * x <=> (y === succ * x)
      // From innerExBeta: innerExPred * x === (y =:= (succ * x))
      // Both are in 𝔹. If A === B and both ∈ 𝔹, then (A === One) <=> (B === One).
      val innerEquiv = have((innerExPred * x) <=> (y === (succ * x))) subproof:
        // innerExPred * x === (y =:= (succ * x)) means they're extensionally equal
        // innerExPred * x ∈ 𝔹 and (y =:= (succ * x)) ∈ 𝔹
        // so innerExPred * x <=> innerExPred * x === One
        // and innerExPred * x === One <=> (y =:= (succ * x)) === One  (by innerExBeta)
        // and (y =:= (succ * x)) === One <=> (y === succ * x)  (by eqAlignInst)
        have((y =:= (succ * x)) <=> (y === (succ * x))) by Tautology.from(
          eqAlignInst,
          boolBivalence of (x := y =:= (succ * x)),
          boolZeroXorOne of (x := y =:= (succ * x)),
          have(HOLProofType(y =:= (succ * x)))
        )
        thenHave(thesis) by Substitute(innerExBeta)

      // ∃(x :: ind, innerExPred * x) <=> ∃(x :: ind, y === succ * x)
      have((x :: ind, y :: ind, innerExPred * x) |- (x :: ind) /\ (y === (succ * x))) by Tautology.from(innerEquiv)
      thenHave((x :: ind, y :: ind, innerExPred * x) |- ∃(x :: ind, y === (succ * x))) by RightExists
      thenHave((y :: ind, (x :: ind) /\ (innerExPred * x)) |- ∃(x :: ind, y === (succ * x))) by Restate
      thenHave((y :: ind, ∃(x :: ind, innerExPred * x)) |- ∃(x :: ind, y === (succ * x))) by LeftExists
      val fwdEx = lastStep

      have((x :: ind, y :: ind, y === (succ * x)) |- (x :: ind) /\ (innerExPred * x)) by Tautology.from(innerEquiv)
      thenHave((x :: ind, y :: ind, y === (succ * x)) |- ∃(x :: ind, innerExPred * x)) by RightExists
      thenHave((y :: ind, (x :: ind) /\ (y === (succ * x))) |- ∃(x :: ind, innerExPred * x)) by Restate
      thenHave((y :: ind, ∃(x :: ind, y === (succ * x))) |- ∃(x :: ind, innerExPred * x)) by LeftExists
      val bwdEx = lastStep

      have((y :: ind) |- (hexists(ind) * innerExPred <=> ∃(x :: ind, y === (succ * x)))) by Tautology.from(innerExLift, fwdEx, bwdEx)
      have((y :: ind) |- (outerPred * y <=> ∃(x :: ind, y === (succ * x)))) by Substitute(outerBeta)(lastStep)

    // Step 6: Prove ∅ has no preimage: ¬∃(x :: ind, ∅ === succ * x)
    val emptyNoPreimage = have(!(∃(x :: ind, ∅ === (succ * x)))) subproof:
      // emptyNotSuccApp: x ∈ ind ⊢ ¬(∅ = succ(x))
      have((x :: ind, ∅ === (succ * x)) |- ()) by Tautology.from(emptyNotSuccApp)
      thenHave((x :: ind) /\ (∅ === (succ * x)) |- ()) by Restate
      thenHave(∃(x :: ind, ∅ === (succ * x)) |- ()) by LeftExists
      have(thesis) by Restate.from(lastStep)

    // Step 7: ¬(outerPred * ∅) using outerPredFOL instantiated at y = ∅
    // But outerPredFOL has free variable y — we substitute y := ∅ to get
    // outerPred * ∅ <=> ∃(x :: ind, ∅ === succ * x)
    // Actually, outerPredFOL is a fact with free y, and we need to check if y appears
    // as a typed var. The substitution of (y := ∅) won't work for `of` since ∅ is not typed.
    // Instead, we should prove ¬∀(y :: ind, outerPred * y) directly.

    // From outerPredFOL: outerPred * y <=> ∃(x :: ind, y === succ * x)
    // From emptyNotSuccApp: ¬(∅ === succ * x)
    // From emptyInInd: ∅ ∈ ind
    
    // Step 7: ¬∀(y :: ind, outerPred * y) 
    // Assume ∀(y :: ind, outerPred * y), instantiate y = ∅ to get outerPred * ∅
    // Use outerPredFOL of (y := ∅)... but ∅ is not a TypedVariable.
    // Instead: from ∀(y :: ind, outerPred * y), derive (∅ ∈ ind) ==> outerPred * ∅ by InstantiateForall
    // Then outerPred * ∅ (since ∅ ∈ ind). 
    // Then we need outerPred * ∅ <=> ∃(x :: ind, ∅ === succ * x). But outerPredFOL has y, not ∅.
    // We can use outerBeta of (y := ∅) but that involves ∅ in typedvar position...
    //
    // Alternative: show ∀(y :: ind, ∃(x :: ind, y === succ * x)) |- false, at the FOL level.
    // Then lift everything.

    // Actually outerPredFOL gives: outerPred * y <=> ∃(x :: ind, y === (succ * x))
    // This means: ∀(y :: ind, outerPred * y) <=> ∀(y :: ind, ∃(x :: ind, y === (succ * x)))
    // So if we show ¬∀(y :: ind, ∃(x :: ind, y === (succ * x))), we get ¬∀(y :: ind, outerPred * y)
    // Then ¬(hforall(ind) * outerPred) via forallLift.

    // Step 7: ¬∀(y :: ind, ∃(x :: ind, y === succ * x))
    // Assume ∀(y :: ind, ∃(x :: ind, y === succ * x)).
    // Instantiate y := ∅ (which is fine since ∅ is Expr[Ind], y in ∀ is a plain variable):
    val emptyInInd = have(∅ ∈ ind) subproof:
      have(thesis) by Weakening(indIsInductive)

    val folNotOnto = have(!(∀(y :: ind, ∃(x :: ind, y === (succ * x))))) subproof:
      // Assume ∀(y :: ind, ∃(x :: ind, y === succ * x)), instantiate y := ∅
      have(∀(y :: ind, ∃(x :: ind, y === (succ * x))) |- ∀(y :: ind, ∃(x :: ind, y === (succ * x)))) by Hypothesis
      thenHave(∀(y :: ind, ∃(x :: ind, y === (succ * x))) |- (∅ :: ind) ==> ∃(x :: ind, ∅ === (succ * x))) by InstantiateForall(∅)
      have(∀(y :: ind, ∃(x :: ind, y === (succ * x))) |- ∃(x :: ind, ∅ === (succ * x))) by Tautology.from(lastStep, emptyInInd)
      have(thesis) by Tautology.from(lastStep, emptyNoPreimage)

    // Step 8: Bridge FOL to HOL
    // outerPredFOL: y ∈ ind ⊢ outerPred * y <=> ∃(x :: ind, y === succ * x)
    // Need: ∀(y :: ind, outerPred * y) ⊢ ∀(y :: ind, ∃(x :: ind, y === succ * x))
    // Strategy: combine InstantiateForall + outerPredFOL, then move y ∈ ind to RHS for RightForall
    
    have(∀(y :: ind, outerPred * y) |- (y :: ind) ==> (outerPred * y)) by InstantiateForall
    have((∀(y :: ind, outerPred * y), y :: ind) |- ∃(x :: ind, y === (succ * x))) by Tautology.from(lastStep, outerPredFOL)
    thenHave(∀(y :: ind, outerPred * y) |- (y :: ind) ==> ∃(x :: ind, y === (succ * x))) by Restate
    thenHave(∀(y :: ind, outerPred * y) |- ∀(y :: ind, ∃(x :: ind, y === (succ * x)))) by RightForall
    val folFromHol = lastStep

    val forallFalse = have(!(hforall(ind) * outerPred)) subproof:
      have(∀(y :: ind, outerPred * y) |- ()) by Tautology.from(folFromHol, folNotOnto)
      have(!(∀(y :: ind, outerPred * y))) by Restate.from(lastStep)
      have(thesis) by Tautology.from(lastStep, forallLift)

    // ¬(ontoBody) means ontoBody === Zero (since ontoBody ∈ 𝔹)
    val ontoFalse = have(!(hOnto(ind)(ind) * succ)) subproof:
      have(thesis) by Substitute(betaOnto)(forallFalse)

    // Step 9: hnot * (hOnto(ind)(ind) * succ) using hnotCorrect
    val result = have(hnot * (hOnto(ind)(ind) * succ)) subproof:
      val onto = hOnto(ind)(ind) * succ
      have(onto :: 𝔹) by Restate.from(HOLProofType(onto))
      have(!(onto === One)) by Tautology.from(
        lastStep,
        boolBivalence of (x := onto),
        boolZeroXorOne of (x := onto),
        ontoFalse
      )
      have(hnot * onto === One) by Tautology.from(
        lastStep,
        hnotCorrect of (p := onto),
        have(HOLProofType(onto))
      )
      have(hnot * onto) by Tautology.from(
        lastStep,
        boolBivalence of (x := hnot * onto),
        boolZeroXorOne of (x := hnot * onto),
        have(HOLProofType(hnot * onto))
      )

  val holeqBetaReduced = HOLTheorem(
    holeq(A) =:= fun(x, fun(y, x =:= y))
  ):
    SYM(TRANS(
      ABS(x)( // fun(x, fun(y, x =:= y)) =:= fun(x, holeq(A) * x)
        ETA(y, holeq(A) * x) // fun(y, holeq(A) * x * y) =:= holeq(A) * x
      ),
      ETA(x, holeq(A)) // fun(x, holeq(A) * x) =:= holeq(A)
    ))

    
  ////////////////////////////////////////////////////
  // HOL Light axioms
  // ETA_AX, INFINITY_AX, SELECT_AX

  val t = typedvar(A ->: B)

  /**
   * ETA_AX 
   * 
   * ```ocaml
   * let ETA_AX = new_axiom
   *   `!t:A->B. (\x. t x) = t`;;
   * ```
   */
  val etaAx = HOLTheorem(hforall(A ->: B) * fun(t, fun(x, t * x) =:= t)):
    sorry
    // assumeAll

    // val pred = fun(t, fun(x, t * x) =:= t)
    // val predTy = pred :: ((A ->: B) ->: 𝔹)
    
    // val eta = ETA(x, t)
    // val eqT = // (fun(x, t * x) =:= t) =:= T
    //   val eqOne = have(((fun(x, t * x) =:= t) :: 𝔹, One :: 𝔹) |- (fun(x, t * x) =:= t) =:= One) by Substitute(eqAlign)(eta)
    //   val conditional = have(((fun(x, t * x) =:= t) :: 𝔹, holT :: 𝔹) |- (fun(x, t * x) =:= t) =:= holT) by Substitute(holTruth)(eqOne)
    //   have(Discharge(have(HOLProofType(fun(x, t * x) =:= t)), holT.justif)(conditional))

    // val abstracted = ABS(t)(eqT) // pred =:= fun(t, holT)

    // have(hforall(A ->: B) * pred) by Substitute(hforall.definition)(abstracted)

  val fi = typedvar(ind ->: ind)

  /**
   * INFINITY_AX
   * 
   * ```ocaml
   * let INFINITY_AX = new_axiom
   *  `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`;;
   * ```
   */
  val infinityAx = HOLTheorem(
    hexists(ind ->: ind) * fun(fi, 
      hand * 
        (hOneOne(ind)(ind) * fi) * 
        (hnot * (hOnto(ind)(ind) * fi))
    )
  ):
    sorry

  /**
   * SELECT_AX
   * 
   * ```ocaml
   * let SELECT_AX = new_axiom
   *  `!P (x:A). P x ==> P((@) P)`;;
   * ```
   */
  val selectAx = HOLTheorem(
    hforall(A ->: 𝔹) * fun(P,
      hforall(A) * fun(x, 
        himp * (P * x) * (P * (hselect(A) * P))
      )
    )
  ):
    sorry

}