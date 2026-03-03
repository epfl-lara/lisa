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
    sorry

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
    // have((succ * x) =:= (succ * y) |- x =:= y) subproof:
      // sorry
    sorry

  val succNotOnto = HOLTheorem(hnot * (hOnto(ind)(ind) * succ)):
    sorry

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
        himp * (P * x) * (P * hselect(A) * P)
      )
    )
  ):
    sorry

}