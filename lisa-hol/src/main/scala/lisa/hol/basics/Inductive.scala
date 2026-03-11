package lisa.hol.basics

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.VarsAndFunctions._
import lisa.hol.basics.Truth.{holT, holTruth, SYM}
import lisa.hol.basics.Forall.{hforall, hforallCorrect}
import lisa.hol.basics.Connectives.{hand, handCorrect, himp, himpCorrect, hnot, hnotCorrect, p, q}
import lisa.hol.basics.Exists.{hexists, hexistsCorrect}
import lisa.maths.SetTheory.Base.FoundationAxiom
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light inductive type, successor, ONE_ONE, ONTO,
 * and related theorems needed for the infinity axiom.
 */
object Inductive extends lisa.HOL {

  val A = typevar
  val B = typevar

  val x = typedvar(A)
  val y = typedvar(A)
  val P = typedvar(A ->: 𝔹)

  val lib = summon[Library]

  // define ONE_ONE
  // let ONE_ONE = new_definition
  //   `ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;
  val hOneOne: HOLPolymorphicConstant[Ind >>: Ind >>: Ind] = {

    val f = typedvar(A ->: B)
    val x = typedvar(A)
    val y = typedvar(A)

    val hOneOne = DEF(
      λ(
        A,
        λ(
          B,
          fun(
            f,
            hforall(A) * fun(
              x, // ∀ x
              hforall(A) * fun(
                y, // ∀ y
                // f x = f y ==> x = y
                himp
                  * (f * x =:= f * y)
                  * (x =:= y)
              )
            )
          )
        )
      )
    )

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
  val hOnto: HOLPolymorphicConstant[Ind >>: Ind >>: Ind] = {

    val f = typedvar(A ->: B)
    val x = typedvar(A)
    val y = typedvar(B)

    val hOnto = DEF(
      λ(
        A,
        λ(
          B,
          fun(
            f,
            hforall(B) * fun(
              y, // ∀ y
              hexists(A) * fun(
                x, // ∃ x
                // y = f x
                y =:= (f * x)
              )
            )
          )
        )
      )
    )

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

  val ind: HOLConstantType = {

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

  val succ: TypedConstant = {
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
            caseY,
            caseSingleton
          )
          have((x ∈ w) /\ (w ∈ uy) |- (x ∈ y) \/ (x === y)) by Weakening(lastStep)
          have(∃(w, (x ∈ w) /\ (w ∈ uy)) |- (x ∈ y) \/ (x === y)) by LeftExists.withParameters((x ∈ w) /\ (w ∈ uy), w)(lastStep)
          lib.have(thesis) by Tautology.from(lastStep, unionAxiom of (z := x, x := uy))

        val xToy = have(expanded(x) === expanded(y) |- (x ∈ y) \/ (x === y)) subproof:
          have(x ∈ ⋃(ux) |- x ∈ ⋃(ux)) by Hypothesis
          have((x ∈ ⋃(ux), ⋃(ux) === ⋃(uy)) |- x ∈ ⋃(uy)) by RightSubstEq.withParameters(
            Seq((⋃(ux), ⋃(uy))),
            (Seq(w), x ∈ w)
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
        Seq((expanded(x), ∅)),
        (Seq(w), x ∈ w)
      )(lastStep)
      have(expanded(x) === ∅ |- x ∈ ∅) by Cut(xinex, lastStep)
      have(!(expanded(x) === ∅)) by Tautology.from(lastStep, xNotInEmpty)
      have(!(∅ === expanded(x))) by Restate.from(lastStep)

    // Step 4: ∅ ≠ succ * x (substitute betaSucc)
    val emptyNotSuccApp = have(!(∅ === (succ * x))) subproof:
      have(thesis) by Substitute(betaSucc)(emptyNotSucc)

    // Step 5: Lift to HOL
    val outerPred = fun(y, hexists(ind) * fun(x, y =:= (succ * x)))

    // Step 5a: hforall(ind) * outerPred <=> ∀(y :: ind, outerPred * y)
    val forallLift = have(hforall(ind) * outerPred <=> ∀(y :: ind, outerPred * y)) subproof:
      have(thesis) by Tautology.from(
        hforallCorrect of (A := ind, P := outerPred, x := y),
        have(HOLProofType(outerPred)),
        ind.nonEmptyThm
      )

    // Step 5b: Set up inner existential for arbitrary y
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
    val outerPredFOL = have(outerPred * y <=> ∃(x :: ind, y === (succ * x))) subproof:
      val eqAlignInst = have((y =:= (succ * x) === One) <=> (y === (succ * x))) subproof:
        have(((y :: ind, (succ * x) :: ind) |- (y =:= (succ * x) === One) <=> (y === (succ * x)))) by Weakening(eqAlign of (A := ind, x := y, y := succ * x))
        have(Discharge(HOLProofType(y), HOLProofType(succ * x))(lastStep))

      val innerEquiv = have((innerExPred * x) <=> (y === (succ * x))) subproof:
        have((y =:= (succ * x)) <=> (y === (succ * x))) by Tautology.from(
          eqAlignInst,
          boolBivalence of (x := y =:= (succ * x)),
          boolZeroXorOne of (x := y =:= (succ * x)),
          have(HOLProofType(y =:= (succ * x)))
        )
        thenHave(thesis) by Substitute(innerExBeta)

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
      have((x :: ind, ∅ === (succ * x)) |- ()) by Tautology.from(emptyNotSuccApp)
      thenHave((x :: ind) /\ (∅ === (succ * x)) |- ()) by Restate
      thenHave(∃(x :: ind, ∅ === (succ * x)) |- ()) by LeftExists
      have(thesis) by Restate.from(lastStep)

    val emptyInInd = have(∅ ∈ ind) subproof:
      have(thesis) by Weakening(indIsInductive)

    val folNotOnto = have(!(∀(y :: ind, ∃(x :: ind, y === (succ * x))))) subproof:
      have(∀(y :: ind, ∃(x :: ind, y === (succ * x))) |- ∀(y :: ind, ∃(x :: ind, y === (succ * x)))) by Hypothesis
      thenHave(∀(y :: ind, ∃(x :: ind, y === (succ * x))) |- (∅ :: ind) ==> ∃(x :: ind, ∅ === (succ * x))) by InstantiateForall(∅)
      have(∀(y :: ind, ∃(x :: ind, y === (succ * x))) |- ∃(x :: ind, ∅ === (succ * x))) by Tautology.from(lastStep, emptyInInd)
      have(thesis) by Tautology.from(lastStep, emptyNoPreimage)

    // Step 8: Bridge FOL to HOL
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
    SYM(
      TRANS(
        ABS(x)( // fun(x, fun(y, x =:= y)) =:= fun(x, holeq(A) * x)
          ETA(y, holeq(A) * x) // fun(y, holeq(A) * x * y) =:= holeq(A) * x
        ),
        ETA(x, holeq(A)) // fun(x, holeq(A) * x) =:= holeq(A)
      )
    )

}
