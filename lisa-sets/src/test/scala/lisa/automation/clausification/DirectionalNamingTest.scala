package lisa.automation.clausification

import lisa.automation.Problem
import lisa.automation.ProofSyntax.{_, given}
import lisa.automation.clausification.Clausification.*
import lisa.automation.superposition.SctptpTest
import lisa.kernel.KernelProof
import org.scalatest.funsuite.AnyFunSuite

class DirectionalNamingTest extends AnyFunSuite:
  private val p = Constant(Identifier("p"), Prop)
  private val q = Constant(Identifier("q"), Prop)
  private val r = Constant(Identifier("r"), Prop)
  private val s = Constant(Identifier("s"), Prop)

  // With threshold 2 each formula names its left compound exactly once.
  private def positive(a: Expression, b: Expression) = or(and(a)(b))(and(r)(s))
  private def negative(a: Expression, b: Expression) = neg(and(or(a)(b))(or(r)(s)))

  test("both directions of a quantified naming definition round-trip through SC-TPTP") {
    val x = Variable(Identifier("x"), Ind)
    val y = Variable(Identifier("y"), Ind)
    val z = Variable(Identifier("z"), Ind)
    val pred = Constant(Identifier("pred"), Ind -> (Ind -> Prop))
    for (source, polarity) <- Seq(positive(pred(x)(z), pred(y)(z)) -> 1, negative(pred(x)(z), pred(y)(z)) -> -1) do
      val step = NamingPhase.nameOne(source, Counter(), 2, Counter(), Set(z)).get
      assert(step.pol == polarity && step.freeVars == Seq(x, y))
      val body = if polarity > 0 then implies(step.nmApp)(step.subst) else implies(step.subst)(step.nmApp)
      val proof = step.proveDirectional
      assert(proof.imports == Vector(() |- step.quantified))
      assert(proof.conclusion == (() |- forall(x, forall(y, body))))
      KernelProof.assertCorrectProofNoSorry(proof, "quantified directional naming")
      SctptpTest.checked(proof)
  }

  test("the naming phase selects the configured derivation and reuses neutral definitions") {
    val neutral = iff(and(p)(q))(r)
    for (source, polarity) <- Seq(positive(p, q) -> 1, negative(p, q) -> -1, neutral -> 0); mode <- Distribute.values do
      given ClausifierOptions = ClausifierOptions(threshold = 2, distribute = mode)
      val step = NamingPhase.nameOne(source, Counter(), 2, Counter(), Set.empty).get
      assert(step.pol == polarity)
      val problem = Problem(Seq(() |- source), None)
      val phase = NamingPhase.certifyNaming(problem, (named, _) => {
        assert(named.hypotheses == Seq(() |- step.named, () |- step.directional))
        ClausificationProof(Vector(Hypothesis(p |- p, p)), named.imports ++ libImports)
      })
      val proof = clausificationProofToProofCertificate(phase)
      KernelProof.assertCorrectProofNoSorry(proof, "directional naming")
      val linear = proof.toLinearProof
      val nonstructural = linear.steps.collect { case Weakening(to, ref) =>
        val from = if ref < 0 then linear.imports(-ref - 1) else linear.steps(ref).statement
        (from, to)
      }.filterNot((from, to) => from.left.subsetOf(to.left) && from.right.subsetOf(to.right))
      assert(nonstructural.length == (if polarity != 0 && mode == Distribute.Weakening then 1 else 0))
      val projected = linear.steps.count(_.isInstanceOf[LeftIff])
      assert(projected == (if polarity != 0 && mode == Distribute.Primitive then 1 else 0))
      if mode == Distribute.Primitive then SctptpTest.checked(proof)
  }
