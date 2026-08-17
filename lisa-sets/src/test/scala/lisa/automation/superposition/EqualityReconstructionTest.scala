package lisa.automation.superposition

import scala.collection.mutable

import org.scalatest.funsuite.AnyFunSuite
import it.unimi.dsi.fastutil.ints.IntArrayList

import lisa.utils.K
import lisa.kernel.KernelProof
import Core.*

/**
 * Low-level, kernel-checked reconstruction tests for the individual equality inferences that the full
 * saturation loop rarely selects on tiny problems (it prefers demodulation / resolution): **superposition**
 * (both into-polarities and both from-orientations) and **equality factoring** (with and without a
 * side-reorientation). Each test builds one generating step directly, reconstructs the derived clause into a
 * kernel proof (whose imports are the parents' sequents and whose conclusion is the derived clause's sequent),
 * and asserts the kernel accepts it. Results are kept **ground**, so the conclusion sequent matches exactly.
 */
class EqualityReconstructionTest extends AnyFunSuite:

  class Fix extends TermFixture:

    /** Locate + unify + [[Superposition.superpose]] + restore (mirrors SuperpositionTest's driver). */
    def superposeAt(from: Clause, iFrom: Int, fromSide: Int, into: Clause, iInto: Int, uPos: Array[Int]): Option[Clause] =
      val l = bank.arg(bank.atomOf(from.literals(iFrom)), fromSide)
      val u = Superposition.subtermAt(bank, bank.atomOf(into.literals(iInto)), uPos)
      val saved = trail.save()
      val res = if trail.unify(l, 0, u, 1) then Superposition.superpose(bank, trail, from, iFrom, fromSide, into, iInto, IntArrayList.wrap(uPos)) else None
      trail.restore(saved)
      res

    // --- kernel views of internal clauses, sharing a fixed var-naming scheme (n → `Xn`) -----------

    private def kern(t: Term): K.Expression =
      if bank.isVar(t) then K.Variable(K.Identifier("X" + bank.varNum(t).num), K.Ind)
      else
        val info = sig.info(bank.headSymbol(t))
        val args = (0 until bank.arity(t)).map(i => kern(bank.arg(t, i)))
        val sort: K.Sort = (0 until info.arity).foldRight(if info.isPredicate then K.Prop else K.Ind: K.Sort)((_, acc) => K.Ind -> acc)
        args.foldLeft(K.Constant(K.Identifier(info.name), sort): K.Expression)((acc, a) => K.Application(acc, a))

    def seqOf(c: Clause): K.Sequent =
      K.Sequent(
        c.literals.iterator.filter(l => !bank.isPositive(l)).map(l => kern(bank.atomOf(l))).toSet,
        c.literals.iterator.filter(l => bank.isPositive(l)).map(l => kern(bank.atomOf(l))).toSet
      )

    private def collectVars(t: Term, s: mutable.Set[Int]): Unit =
      if bank.isVar(t) then s += bank.varNum(t).num
      else { var i = 0; while i < bank.arity(t) do { collectVars(bank.arg(t, i), s); i += 1 } }

    def vmOf(c: Clause): Map[Int, K.Variable] =
      val s = mutable.Set.empty[Int]
      c.literals.foreach(l => collectVars(bank.atomOf(l), s))
      s.iterator.map(n => n -> K.Variable(K.Identifier("X" + n), K.Ind)).toMap

    /** Reconstruct `derived` (its parents supplied as imports) and assert the kernel accepts the proof and it
     *  concludes exactly `seqOf(derived)` (well-defined because every `derived` here is ground). */
    def checkReconstructs(derived: Clause, parents: Clause*): Unit =
      val inputs = parents.iterator.map(p => p.id -> (seqOf(p), vmOf(p))).toMap
      val proof = Reconstruction.reconstruct(derived, bank, inputs)
      KernelProof.assertCorrectProofNoSorry(proof, "reconstruction")
      assert(proof.conclusion == seqOf(derived), s"conclusion ${proof.conclusion} != expected ${seqOf(derived)}")
      assert(proof.imports.toSet.subsetOf(parents.iterator.map(seqOf).toSet), "imports are not among the parents")

    /** `seqOf(c)` with the fixture's `X<n>` variables renamed to the `cv<n>` scheme reconstruction builds its
      * sequents in, so a **non-ground** derived clause's conclusion can be compared exactly. This is the
      * invariant every consumer of a reconstructed step depends on: the sequent proved for `c` must name its
      * variables by `c`'s own internal numbers, because the children name theirs by reading `c` directly. */
    def canonSeqOf(c: Clause): K.Sequent =
      val rename: Map[K.Variable, K.Expression] = vmOf(c).map((n, x) =>
        x -> K.Variable(K.Identifier(lisa.automation.clausification.Clausification.GeneratedNames.reconClauseVar, n), K.Ind))
      val s = seqOf(c)
      K.Sequent(s.left.map(K.substituteVariables(_, rename)), s.right.map(K.substituteVariables(_, rename)))

  // --- superposition ------------------------------------------------------------------------------

  test("reconstruct superposition into a positive predicate literal (RightSubstEq)") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val from = clause(pos(mkEq(app(f, a), b))) // f(a) ≈ b
    val into = clause(pos(app(P, app(f, a)))) // P(f(a))
    val r = superposeAt(from, 0, 0, into, 0, Array(0)).get // ⇒ P(b)
    assert(r.literals.toSet == Set(pos(app(P, b))))
    checkReconstructs(r, from, into)
  }

  test("reconstruct superposition when both parents contribute a surviving variable (numbering must match)") {
    // The only test here whose conclusion is non-ground, and so the only one that can observe *which* fresh
    // number each variable got: two must survive, one from each parent. It fails if `superpose` and
    // `Superposition.replayApplier` stop agreeing on the order they hand operands to the `Applier`.
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val Q = pred("Q", 1); val R = pred("R", 1)
    val f = fn("f", 1); val a = const("a"); val b = const("b")
    val y = v(0); val z = v(1); val w = v(0) // `y`/`z` are scope-0 (from), `w` scope-1 (into): numbers may repeat
    val from = clause(pos(mkEq(app(f, y), a)), pos(app(P, z))) //  f(y) ≈ a ∨ P(z)
    val into = clause(pos(app(Q, app(f, b))), pos(app(R, w))) //   Q(f(b)) ∨ R(w)
    val r = superposeAt(from, 0, 0, into, 0, Array(0)).get //      ⇒ Q(a) ∨ R(w) ∨ P(z), w and z renumbered
    assert(r.literals.length == 3)
    assert(vmOf(r).size == 2, s"expected two surviving variables, got ${vmOf(r).keys}")
    val proof = Reconstruction.reconstruct(r, bank, Seq(from, into).map(p => p.id -> (seqOf(p), vmOf(p))).toMap)
    KernelProof.assertCorrectProofNoSorry(proof, "reconstruction")
    assert(proof.conclusion == canonSeqOf(r), s"conclusion ${proof.conclusion} != expected ${canonSeqOf(r)}")
  }

  test("reconstruct superposition into a negative literal (LeftSubstEq)") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val from = clause(pos(mkEq(app(f, a), b))) // f(a) ≈ b
    val into = clause(neg(app(P, app(f, a)))) // ¬P(f(a))
    val r = superposeAt(from, 0, 0, into, 0, Array(0)).get // ⇒ ¬P(b)
    assert(r.literals.toSet == Set(neg(app(P, b))))
    checkReconstructs(r, from, into)
  }

  test("reconstruct superposition from the second (arg1) side of the equation (flip)") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val from = clause(pos(mkEq(b, app(f, a)))) // b ≈ f(a): the rewriting side f(a) is arg1
    val into = clause(pos(app(P, app(f, a)))) // P(f(a))
    val r = superposeAt(from, 0, 1, into, 0, Array(0)).get // ⇒ P(b)
    assert(r.literals.toSet == Set(pos(app(P, b))))
    checkReconstructs(r, from, into)
  }

  test("reconstruct superposition carrying a from-clause side literal") {
    val fx = new Fix; import fx.*
    val P = pred("P", 1); val q = app(pred("Q", 0)); val f = fn("f", 1); val a = const("a"); val b = const("b")
    val from = clause(pos(q), pos(mkEq(app(f, a), b))) // Q ∨ f(a) ≈ b (non-unit)
    val into = clause(neg(app(P, app(f, a)))) // ¬P(f(a))
    val r = superposeAt(from, 1, 0, into, 0, Array(0)).get // ⇒ ¬P(b) ∨ Q
    assert(r.literals.toSet == Set(neg(app(P, b)), pos(q)))
    checkReconstructs(r, from, into)
  }

  // --- equality factoring -------------------------------------------------------------------------

  test("reconstruct equality factoring, matching sides (no reorientation)") {
    val fx = new Fix; import fx.*
    val c0 = const("c"); val a = const("a"); val b = const("b"); val f = fn("f", 1); val x = v(0)
    val cl = clause(pos(mkEq(app(f, x), a)), pos(mkEq(app(f, b), c0))) // f(x)≈a ∨ f(b)≈c
    val factor = Superposition.equalityFactoring(bank, trail, cl, Array(0, 1))
      .find(_.literals.toSet == Set(neg(mkEq(a, c0)), pos(mkEq(app(f, b), c0)))).get // a≉c ∨ f(b)≈c
    factor.justification match
      case Justification.EqualityFactoring(_, d, ds, k, ks) => assert(ds == ks) // same side ⇒ no flip
      case _ => fail("expected EqualityFactoring")
    checkReconstructs(factor, cl)
  }

  test("reconstruct equality factoring, opposite sides (reorientation)") {
    val fx = new Fix; import fx.*
    val c0 = const("c"); val a = const("a"); val b = const("b"); val f = fn("f", 1); val x = v(0)
    val cl = clause(pos(mkEq(app(f, x), a)), pos(mkEq(c0, app(f, b)))) // f(x)≈a ∨ c≈f(b): kept side is arg1
    val factor = Superposition.equalityFactoring(bank, trail, cl, Array(0, 1))
      .find(_.literals.toSet == Set(neg(mkEq(a, c0)), pos(mkEq(c0, app(f, b))))).get // a≉c ∨ c≈f(b)
    factor.justification match
      case Justification.EqualityFactoring(_, d, ds, k, ks) => assert(ds != ks) // opposite sides ⇒ flip path
      case _ => fail("expected EqualityFactoring")
    checkReconstructs(factor, cl)
  }
