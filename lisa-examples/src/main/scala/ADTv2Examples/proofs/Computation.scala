package ADTv2Examples.proofs

import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction

/**
 * The `elim` rules of a recursive function are computation rules: chaining them
 * evaluates a function on a concrete, closed argument.  These theorems check
 * that the library functions compute the values we expect.
 *
 * The per-constructor `elim` rule for a *recursive* constructor (`succ`, `cons`)
 * is an implication guarded by the predecessor's membership, with a free
 * variable for that predecessor.  We instantiate it at a concrete term with
 * `of`; the guard is discharged by the relevant `intro` typing fact.
 */
object Computation extends lisa.Main {

  // Locals named to match the library's internal binders so `of` can target
  // the free variable in each `elim(succ)` / `elim(cons)` statement.
  private val natDoubleN = variable[Ind]
  private val natPredN = variable[Ind]
  private val natAddN = variable[Ind]
  private val natAddRight = variable[Ind]
  private val T = variable[Ind]
  private val e = variable[Ind >>: Ind]
  private val e2 = variable[Ind]
  private val listLengthHead = variable[Ind]
  private val listLengthTail = variable[Ind]
  private val treeLeafValue = variable[Ind]
  private val treeNodeLeft = variable[Ind]
  private val treeNodeRight = variable[Ind]

  // ── Bool: not is fully determined, no instantiation needed ──────────────
  section("not")
  val notTrue = Theorem(not * tru === fals) {
    have(thesis) by Restate.from(not.elim(tru))
  }
  val notFalse = Theorem(not * fals === tru) {
    have(thesis) by Restate.from(not.elim(fals))
  }

  // ── Nat: pred(succ(zero)) = zero ────────────────────────────────────────
  section("pred")
  val predOne = Theorem(pred * (succ * zero) === zero) {
    have(thesis) by Tautology.from(
      pred.elim(succ) of (natPredN := zero),
      zero.intro
    )
  }

  // ── Nat: double(succ(zero)) = succ(succ(zero))  (double 1 = 2) ───────────
  section("double")
  val doubleOne = Theorem(double * (succ * zero) === succ * (succ * zero)) {
    val base = have(double * zero === zero) by Restate.from(double.elim(zero))
    val step = have(double * (succ * zero) === succ * (succ * (double * zero))) by Tautology.from(
      double.elim(succ) of (natDoubleN := zero),
      zero.intro
    )
    have(thesis) by Congruence.from(base, step)
  }

  // ── List: length [zero, zero] = succ(succ(zero))  (length = 2) ───────────
  section("length")
  private val l0 = nil(nat)
  private val l1 = cons(nat) * zero * l0
  private val l2 = cons(nat) * zero * l1
  val lengthTwo = Theorem(length(nat) * l2 === succ * (succ * zero)) {
    // length(nil) = zero
    val lenNil = have(length(nat) * l0 === zero) by Restate.from(length.elim(nat)(nil))
    // length(cons(zero, nil)) = succ(length(nil)),  needs zero::nat and nil::list[nat]
    val lenL1 = have(length(nat) * l1 === succ * (length(nat) * l0)) by Tautology.from(
      length.elim(nat)(cons) of (listLengthHead := zero, listLengthTail := l0),
      zero.intro,
      nil.intro(nat)
    )
    // length(cons(zero, l1)) = succ(length(l1)),  needs zero::nat and l1::list[nat]
    val l1Typing = have(l1 :: list(nat)) by Typecheck.prove
    val lenL2 = have(length(nat) * l2 === succ * (length(nat) * l1)) by Tautology.from(
      length.elim(nat)(cons) of (listLengthHead := zero, listLengthTail := l1),
      zero.intro,
      l1Typing
    )
    have(thesis) by Congruence.from(lenNil, lenL1, lenL2)
  }

  // ── Tree: leafCount(node(star, node(star, leaf, leaf), leaf)) = 3 ───────
  section("leafCount")
  private val t0 = leaf(unit)
  private val t1 = node(unit) * star * t0 * t0
  private val t2 = node(unit) * star * t1 * t0
  private val one = succ * zero
  private val two = succ * one
  private val three = succ * two
  val leafCountThree = Theorem(leafCount(unit) * t2 === three) {

    // Typing facts
    val t1Typing = have(t1 :: tree(unit)) by Typecheck.prove
    val oneTyping = have(one :: nat) by Typecheck.prove

    // Elimination rules
    val countLeaf = have(leafCount(unit) * t0 === one) by Restate.from(leafCount.elim(unit)(leaf))
    val countT1 = have(leafCount(unit) * t1 === add * (leafCount(unit) * t0) * (leafCount(unit) * t0)) by Tautology.from(
      leafCount.elim(unit)(node) of (treeLeafValue := star, treeNodeLeft := t0, treeNodeRight := t0),
      star.intro,
      leaf.intro(unit)
    )
    val countT2 = have(leafCount(unit) * t2 === add * (leafCount(unit) * t1) * (leafCount(unit) * t0)) by Tautology.from(
      leafCount.elim(unit)(node) of (treeLeafValue := star, treeNodeLeft := t1, treeNodeRight := t0),
      star.intro,
      t1Typing,
      leaf.intro(unit)
    )

    // Beta-reductions of add
    val betaAddZeroAtOne = have(abs(nat)(λ(natAddRight, natAddRight)) * one === one) by Tautology.from(
      BetaReduction of (T := nat, e := λ(natAddRight, natAddRight), e2 := one),
      oneTyping
    )
    val betaAddSuccAtOne = have(
      abs(nat)(λ(natAddRight, succ * (add * zero * natAddRight))) * one === succ * (add * zero * one)
    ) by Tautology.from(
      BetaReduction of (T := nat, e := λ(natAddRight, succ * (add * zero * natAddRight)), e2 := one),
      oneTyping
    )
    val betaAddTwoAtOne = have(
      abs(nat)(λ(natAddRight, succ * (add * one * natAddRight))) * one === succ * (add * one * one)
    ) by Tautology.from(
      BetaReduction of (T := nat, e := λ(natAddRight, succ * (add * one * natAddRight)), e2 := one),
      oneTyping
    )
    
    // Elimination rules of add
    val addSuccEq = have(add * one === abs(nat)(λ(natAddRight, succ * (add * zero * natAddRight)))) by Tautology.from(
      add.elim(succ) of (natAddN := zero),
      zero.intro
    )
    val addTwoEq = have(add * two === abs(nat)(λ(natAddRight, succ * (add * one * natAddRight)))) by Tautology.from(
      add.elim(succ) of (natAddN := one),
      oneTyping
    )

    // Addition facts
    val addZeroEq = have(add * zero === abs(nat)(λ(natAddRight, natAddRight))) by Restate.from(add.elim(zero))
    val addOneOne = have(add * one * one === two) by Congruence.from(
      addZeroEq, 
      betaAddZeroAtOne, 
      betaAddSuccAtOne, 
      addSuccEq
    )
    val addTwoOne = have(add * two * one === three) by Congruence.from(
      addZeroEq, 
      betaAddZeroAtOne, 
      betaAddSuccAtOne, 
      betaAddTwoAtOne,
      addSuccEq, 
      addTwoEq
    )


    have(thesis) by Congruence.from(countLeaf, countT1, countT2, addOneOne, addTwoOne)
  }
}
