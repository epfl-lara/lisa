package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}

/**
 * Tests for [[DistributePhase]]'s leaf discipline — that its per-clause derivations only ever bottom out on real
 * literals, and that anything else is refused loudly.
 *
 * The case worth pinning is the **η-reduced quantifier**. The kernel's `betaNormalForm` η-reduces `λy. p(y)` to
 * `p`, so a `∀y. p(y)` can come back as `∀(p)` = `Application(forall, p)` — which the [[Forall]] extractor, needing
 * an explicit `Lambda`, does not match. `PrenexPhase.hasForall` misses it for the same reason and leaves it in the
 * matrix, and `∀(p)` is `Prop`-sorted, so `isLeaf`'s catch-all used to accept it as an *atom*. The clause then
 * carried an opaque quantified literal whose head `Bridge` interns as an ordinary `forall/1` predicate over a
 * clause variable: nothing anywhere reports it, and the problem simply looks unprovable.
 *
 * So these tests are about a *diagnostic*, not about soundness — the point is that the failure is now visible at
 * the phase that can name it, instead of surfacing as an unexplained non-refutation much later.
 */
class DistributePhaseTest extends AnyFunSuite:

  private val x = Variable(Identifier("x"), Ind)
  private val p = Variable(Identifier("p"), Ind >>: Prop) //   a predicate, so `forall(p)` is well-sorted
  private val a = Variable(Identifier("a"), Prop)
  private val b = Variable(Identifier("b"), Prop)

  /** The clauses of `phi` in the shape the phase emits them: negative literals as their atoms on the left,
    * positive literals on the right. */
  private def clausesOf(phi: Expression): Seq[Sequent] =
    DistributePhase.distributeClauses(phi, scala.collection.mutable.ArrayBuffer.empty)
      .map((negative, positive, _) => Sequent(negative, positive))

  test("an ordinary NNF matrix distributes to its CNF clauses, negative literals on the left") {
    // a ∨ (b ∧ ¬a)  ⇒  the clauses {a, b} and {a, ¬a}, i.e. the sequents `⊢ a, b` and `a ⊢ a`.
    assert(clausesOf(or(a)(and(b)(neg(a)))).toSet == Set(Sequent(Set.empty, Set(a, b)), Sequent(Set(a), Set(a))))
  }

  test("an η-reduced ∀(p) in the matrix is refused, not clausified as an atom") {
    val etaReduced = forall(p) //                         `∀(p)`: Prop-sorted, but NOT matched by `Forall`
    assert(etaReduced.sort == Prop, "the test's premise is that this shape is Prop-sorted and so reaches the leaf case")
    assert(!etaReduced.isInstanceOf[Lambda], "guard: `forall(p)` must not have been normalised into an explicit Lambda")
    etaReduced match
      case Forall(_, _) => fail("`forall(p)` matched the Forall extractor, so this test no longer covers the η-reduced form")
      case _            => ()

    val thrown = intercept[IllegalArgumentException](clausesOf(or(a)(etaReduced)))
    assert(thrown.getMessage.contains("η-reduced"), s"the failure should name the cause, got: ${thrown.getMessage}")
  }

  test("an η-reduced ∃(p) is refused the same way") {
    intercept[IllegalArgumentException](clausesOf(exists(p)))
  }

  test("an explicitly-bound ∀x. p(x) is refused too — the extractor case, for contrast") {
    // Not the η-reduced shape: this one `Forall` does match, and the pre-existing `isLeaf` case already rejected
    // it. Kept so the two paths to the same verdict stay pinned together.
    intercept[IllegalArgumentException](clausesOf(forall(Lambda(x, p(x)))))
  }

  test("a partially-applied connective is excluded by sort, needing no case of its own") {
    // `∧(a)` is `Prop → Prop`, so `isLeaf`'s sort test already rejects it — this is why only the quantifiers,
    // which take one argument and land back at `Prop`, need matching head-on.
    assert(and(a).sort != Prop)
    intercept[IllegalArgumentException](clausesOf(or(a)(and(b))))
  }
