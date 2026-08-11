package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite
import lisa.kernel.KernelProof
import lisa.automation.clausification.{Clausification, CertifiedClausifier}

/**
 * End-to-end tests of the [[Superpose]] tactic: each theorem is proved by `have(thesis) by Superpose`, so the
 * whole path runs — clausify → superposition refute → reconstruct → discharge the five library lemmas
 * ([[lisa.maths.Quantifiers.existsEpsilonIff]] + the prenex laws) at theorem completion. A failing proof throws
 * at construction, so reaching a `test` body means the theorem was accepted by the kernel and the library.
 */
class SuperposeTacticTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  val A, B = variable[Prop]
  val zz, ww = variable[Ind]
  val SS = variable[Ind >>: Prop]

  // Proved eagerly at construction; the `test` blocks name them for the report.
  val implSelf       = Theorem(A ==> A) { have(thesis) by Superpose }
  val excludedMiddle = Theorem(A \/ !A) { have(thesis) by Superpose }
  val deMorgan       = Theorem(!(A /\ B) <=> (!A \/ !B)) { have(thesis) by Superpose }
  val fromHyp        = Theorem(B \/ !B) { have(thesis) by Superpose.from(excludedMiddle) } // `.from` plumbing (hyp unused)

  test("propositional: A ⟹ A") { assert(implSelf.statement.underlying == (() |- (A ==> A)).underlying) }
  test("propositional: excluded middle A ∨ ¬A") { succeed }
  test("propositional: De Morgan ¬(A ∧ B) ⟺ ¬A ∨ ¬B") { succeed }
  test("`.from`: a cited hypothesis fact is threaded in and discharged") { succeed }

  // Regression for the NegatedPhase bug: a conjecture with a free predicate VARIABLE must clausify to a
  // kernel-valid proof WITHOUT the caller pre-freezing anything (frozen defaults to ∅). NegatedPhase pins the
  // conjecture's free non-Ind symbols itself; before the fix this was invalid at step 2.6 (the old RenamePhase
  // renaming `S`, which is free in the negated-conjecture assumption — the rename now happens in ScreenPhase,
  // above the assumption, where it is legal at every sort).
  test("certifyClausal is kernel-valid on a first-order goal with a free predicate variable (frozen=∅)") {
    import lisa.utils.K
    val z, w = variable[Ind]; val S = variable[Ind >>: Prop]
    val conj: K.Expression = (∀(z, S(z)) ==> S(w)).underlying
    val problem = Clausification.Problem(Seq.empty, Some(K.Sequent(Set.empty, Set(conj))))
    val prover: Clausification.Problem => K.SCProof =
      p => Clausal.proveOutcome(p).fold(o => throw new RuntimeException(o.toString), identity)
    val pk = CertifiedClausifier.certifyClausal(problem, prover)
    KernelProof.assertCorrectProofNoSorry(pk, "certifyClausal on the schematic FO goal")
  }

  // ── first-order ──
  val univInst = Theorem(∀(zz, SS(zz)) ==> SS(ww)) { have(thesis) by Superpose }
  val drinker  = Theorem(∃(zz, SS(zz) ==> ∀(ww, SS(ww)))) { have(thesis) by Superpose }

  test("first-order: (∀z. S(z)) ⟹ S(w)") { succeed }
  test("first-order: drinker's paradox ∃z. (S(z) ⟹ ∀w. S(w))") { succeed }

  // End-to-end counterpart of `ScreenPhaseTest`: the goal is written with the names the clausifier reserves for
  // its own schemas — `P : Ind → Prop` (instantiated by the Skolem bridge), `R : Prop` (the closed operand of the
  // prenex laws), `x` (their bound variable). ScreenPhase renames them on the way in and restores them on the way
  // out; without it the kernel rejected the clausification, so the tactic could not have produced this theorem.
  val P = variable[Ind >>: Prop] // == Clausification.schemaP
  val R = variable[Prop] //         == Clausification.schemaR
  val x, xx = variable[Ind] //      `x` is the library statements' bound variable
  val collidingNames = Theorem((∀(x, P(x)) /\ R) ==> (P(xx) /\ R)) { have(thesis) by Superpose }

  test("names reserved by the clausifier (`P`, `R`, `x`) are usable in a goal") { succeed }

  // ── arbitrary sequent shapes ──
  // The clausifier takes one conjecture formula, so the goal is folded through `sequentToFormula` and unfolded
  // by the closing `Restate`. Both sides may be empty, and cited facts of any shape are folded the same way.
  val seqIdentity  = Theorem(A |- A) { have(thesis) by Superpose }
  val seqBothSides = Theorem((A /\ B) |- (B \/ A)) { have(thesis) by Superpose }
  val seqMultiLeft = Theorem((A ==> B, A) |- B) { have(thesis) by Superpose }
  val seqEmptyRhs  = Theorem((A, !A) |- ()) { have(thesis) by Superpose }
  val seqFirstOrder = Theorem(∀(zz, SS(zz)) |- SS(ww)) { have(thesis) by Superpose }
  // A cited fact with a non-empty left-hand side is folded to `⊢ ⋀Γᵢ ⟹ ⋁Δᵢ` by its per-premise Restate.
  val seqFromShaped = Theorem(A |- (A \/ B)) { have(thesis) by Superpose.from(seqIdentity) }

  test("sequent shape: A ⊢ A") { succeed }
  test("sequent shape: A ∧ B ⊢ B ∨ A (both sides non-empty)") { succeed }
  test("sequent shape: A ⟹ B, A ⊢ B (several assumptions)") { succeed }
  test("sequent shape: A, ¬A ⊢ (empty right-hand side)") { succeed }
  test("sequent shape: ∀z. S(z) ⊢ S(w) (first-order)") { succeed }
  test("sequent shape: a cited fact with a non-empty left-hand side") { succeed }

  // Degenerate/unprovable shapes must come back as a judgement, not an exception: the tactic is called here for
  // its return value and never `have`n, so "did not throw and is not valid" is the pass condition. The message
  // is checked too — `runProver`'s catch-all would otherwise turn an internal crash into an indistinguishable
  // failure, and only the "could not refute" wording means the prover really saturated.
  val cleanFailures = Theorem(A |- A) {
    val nonTheorem = Superpose(A |- B)
    assert(!nonTheorem.isValid, "a non-theorem must not yield a valid judgement")
    nonTheorem match
      case ipt: lisa.SetTheoryLibrary.Proof#InvalidProofTactic =>
        assert(ipt.message.startsWith("Superpose could not refute"), s"expected a clean non-refutation, got: ${ipt.message}")
      case other => fail(s"expected an InvalidProofTactic carrying a message, got $other")
    assert(!Superpose(() |- ()).isValid, "the empty sequent must not yield a valid judgement")
    have(thesis) by Superpose
  }

  test("an unprovable goal and the empty sequent fail cleanly (judgement, not exception)") { succeed }
}
