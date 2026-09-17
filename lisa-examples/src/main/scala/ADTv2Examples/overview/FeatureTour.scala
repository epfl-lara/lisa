package ADTv2Examples.overview

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

/**
 * A guided tour of the ADTv2 features, kept deliberately compact.
 *
 * This file is an *overview*: every section touches one capability of the
 * library with the smallest example that still shows the idea.  For the full,
 * exhaustive treatment of each feature, see the dedicated example files:
 *
 *   - builder/      : defining monomorphic / polymorphic ADTs, specialization
 *   - functions/    : non-recursive `fun`, recursive `recFun`, nested patterns
 *   - proofs/       : the `Induction` tactic and `Typecheck` integration
 *   - endtoend/     : a realistic Nat + List development
 *
 * Everything below reuses the predefined library ADTs (Nat, List, Bool,
 * Option, Union) so the tour stays short.
 */
object FeatureTour extends lisa.Main {

  // ── 1. Defining an ADT ──────────────────────────────────────────────────
  // ADTs are values.  A monomorphic one (`nat`, `bool`) has no type variables;
  // a polymorphic one (`list`, `option`, `union`) is parameterized.
  section("1. ADT definitions (monomorphic and polymorphic)")
  // Defining them is enough to obtain their constructors and theorems; the
  // library already did that, here we just point at the results.  The generated
  // `induction` theorem takes one type argument per type variable, so it is
  // called on polymorphic ADTs; monomorphic ones (`nat`, `bool`) use the
  // `Induction` proof tactic instead — see section 7.
  show(list.induction(nat)) // one type argument for the element type
  show(option.induction(bool)) // Option[Bool]
  show(union.induction(nat, bool)) // two type arguments

  // ── 2. Constructors: introduction rules ─────────────────────────────────
  // Each constructor exposes `intro` (membership of a fully applied
  // constructor) and `introApp` (the curried/applied form).
  section("2. Constructor introduction rules")
  show(zero.intro)
  show(succ.intro)
  show(cons.intro(nat)) // polymorphic: pass the element type
  show(some.intro(nat)) // Option — under-shown elsewhere
  show(inl.intro(nat, bool)) // Union — two type arguments

  // ── 3. Disjointness ──────────────────────────────────────────────────────
  // Distinct constructors of the same ADT are provably distinct.
  section("3. Constructor disjointness")
  show(option.disjointness(some, none, nat))
  show(union.disjointness(inl, inr, nat, bool))

  // ── 4. Recursive functions (recFun) ─────────────────────────────────────
  // `pred`, `double`, `length` are recursive functions over an ADT.  Each has
  // an `intro` rule and per-constructor `elim` rules computing its value.
  section("4. Recursive functions")
  show(pred.intro) // Nat predecessor — under-shown elsewhere
  show(pred.elim(zero))
  show(pred.elim(succ))
  show(length.intro(nat))
  show(length.elim(nat)(cons))

  // ── 5. Higher-order recursion ───────────────────────────────────────────
  // A recursive function may return a function (`add : Nat -> (Nat -> Nat)`).
  // `introApp` gives the applied form.
  section("5. Higher-order recursion")
  show(add.introApp)
  show(add.elim(succ))

  // ── 6. Non-recursive functions with (multi-level) nested patterns ───────
  // `fun` defines a non-recursive function; nested patterns let one branch
  // match a constructor argument against a concrete term.  `elimTotal`
  // packages the per-branch elimination rules into a single totality fact.
  section("6. Nested pattern matching")
  val isOne = fun(nat, bool) {
    Case(zero):
      fals
    Case(succ, zero):
      tru
    Case(succ, succ * variable[Ind]):
      fals
  }
  show(isOne.intro)
  show(isOne.elimTotal)

  // ── 8. Induction as a proof tactic ──────────────────────────────────────
  // Beyond the generated `induction` theorem, ADTs integrate with the
  // `Induction` proof tactic for hand-written proofs.
  section("7. The Induction proof tactic")
  val n = variable[Ind]
  val natReflexive = Theorem((n :: nat) |- n === n) {
    have(thesis) by Induction(n, nat) {
      Case(zero) subproof { have(thesis) by RightRefl }
      Case(succ, n) subproof { have(thesis) by RightRefl }
    }
  }
  show(natReflexive)

  // ── 9. Automatic type checking ──────────────────────────────────────────
  // `Typecheck.prove` discharges membership goals for terms built from
  // constructors and functions.
  section("8. Typecheck integration")
  val listValue = cons(nat) * zero * nil(nat)
  val lengthTyping = Theorem(length(nat) * listValue :: nat) {
    have(thesis) by Typecheck.prove
  }
  show(lengthTyping)
}
