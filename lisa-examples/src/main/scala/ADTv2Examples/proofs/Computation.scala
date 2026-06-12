package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

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
  private val listLengthHead = variable[Ind]
  private val listLengthTail = variable[Ind]

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
}
