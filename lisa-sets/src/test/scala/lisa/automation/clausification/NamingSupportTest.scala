package lisa.automation.clausification

import lisa.kernel.KernelProof
import lisa.utils.K
import lisa.utils.K.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import Clausification.Counter

/**
 * Tests for [[NamingSupport.namingVars]], the single definition of the variables a naming atom abstracts, and
 * for the `frozen` exclusion being threaded to it.
 *
 * `frozen` holds symbols that are uninterpreted constants pinned elsewhere (Skolem functions from
 * [[SkolemPhase]]). A *nullary* one is the only kind that needs excluding by name: it is `Ind`-sorted, so the
 * sort filter alone would abstract it, giving the atom an argument that is the same constant at every occurrence
 * and a definition that quantifies over a symbol not meant to vary.
 *
 * The parameter existed unused for a long time, so these tests exist to make it known to work rather than merely
 * present. Naming currently runs above Skolemization in both pipelines, so no production call passes a non-empty
 * set today; the tests supply one directly.
 */
class NamingSupportTest extends AnyFunSuite:

  private val q = Constant(Identifier("q"), Ind >>: Prop)
  private val sk = Variable(Identifier("sk", 0), Ind) // a nullary Skolem symbol: Ind-sorted, so the sort filter misses it
  private val y = Variable(Identifier("y"), Ind) //     an ordinary clause variable
  private val P = Variable(Identifier("P"), Ind >>: Prop) // higher-sorted: excluded by sort, whatever `frozen` says
  private val a = Constant(Identifier("a"), Ind)
  private val b = Constant(Identifier("b"), Ind)
  private val c = Constant(Identifier("c"), Ind)
  private val d = Constant(Identifier("d"), Ind)

  /**
   * `((q(sk) ∧ q(y)) ∨ (q(a) ∧ q(b))) ∨ (q(c) ∧ q(d))` where the positive `∨` is multiplicative, so the estimate is
   * 2·2·2 = 8, past the default threshold of 4, and `findSite` names the larger child. Its free `Ind` variables
   * are exactly `{sk, y}`.
   */
  private val big: Expression = or(or(and(q(sk))(q(y)))(and(q(a))(q(b))))(and(q(c))(q(d)))

  private def nameOnce(f: Expression, frozen: Set[Variable]): NamingPhase.NamingStep =
    NamingPhase
      .nameOne(f, Counter(), UncertifiedClausifier.DefaultThreshold, Counter(), frozen)
      .getOrElse(fail(s"nothing was named in $f: the test formula no longer trips the threshold"))

  test("namingVars keeps free Ind variables, drops higher-sorted ones and drops frozen ones") {
    val f = and(q(sk))(and(q(y))(P(a)))
    assert(NamingSupport.namingVars(f, Set.empty) == Seq(sk, y), "expected both Ind variables, ordered by identifier")
    assert(NamingSupport.namingVars(f, Set(sk)) == Seq(y), "the frozen symbol was still abstracted")
    assert(!NamingSupport.namingVars(f, Set.empty).contains(P), "a higher-sorted variable must never be abstracted")
  }

  test("a frozen nullary symbol is not abstracted, so the naming atom loses exactly one argument") {
    val loose = nameOnce(big, Set.empty)
    val frozen = nameOnce(big, Set(sk))
    assert(loose.freeVars.contains(sk), "premise: without `frozen`, `sk` is abstracted, being Ind-sorted")
    assert(!frozen.freeVars.contains(sk), "`sk` was abstracted despite being frozen")
    assert(frozen.freeVars.size == loose.freeVars.size - 1, "arity did not drop by exactly one")
    // and the atom's sort follows the list, so the use site really is one argument shorter
    assert(frozen.nm.sort == (Ind >>: Prop) && loose.nm.sort == (Ind >>: Ind >>: Prop), s"atom sorts: frozen=${frozen.nm.sort}  loose=${loose.nm.sort}")
  }

  test("the frozen symbol stays free in the definition rather than being quantified over") {
    val step = nameOnce(big, Set(sk))
    assert(step.quantified.freeVariables.contains(sk), "the definition must leave the frozen symbol free")
    assert(!nameOnce(big, Set.empty).quantified.freeVariables.contains(sk), "premise: unfrozen, it is bound instead")
  }

  test("the naming bridge is kernel-valid either way, so the marker and the atom cannot drift apart") {
    // `findSite` sizes its rewrite marker `p` from `namingVars`, and `freshNamingAtom` sizes `nm` from the same
    // call. `nameOne` substitutes `p -> nm` directly, so if the two lists disagreed the `RightSubstIff` in the
    // bridge would be ill-sorted and the kernel would reject it. Sharing one function is what rules that out;
    // this checks it for both settings of `frozen`.
    for f <- Seq(Set.empty[Variable], Set(sk)) do
      val step = nameOnce(big, f)
      KernelProof.assertCorrectProofNoSorry(step.bridge, s"naming bridge (frozen=$f)")
      assert(step.bridge.conclusion == (big |- step.named), s"bridge concludes ${step.bridge.conclusion}")
  }
