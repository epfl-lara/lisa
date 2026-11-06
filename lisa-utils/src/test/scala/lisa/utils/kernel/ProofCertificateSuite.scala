package lisa.utils.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.Sequent
import org.scalatest.funsuite.AnyFunSuite

class ProofCertificateSuite extends AnyFunSuite:
  private val p = Variable(Identifier("certificate-p"), Prop)
  private val q = Variable(Identifier("certificate-q"), Prop)
  private val identityP = Sequent(Set(p), Set(p))
  private val identityQ = Sequent(Set(q), Set(q))
  private val premiseP = Sequent(Set.empty, Set(p))
  private val premiseQ = Sequent(Set.empty, Set(q))

  test("flatten nested subproofs and remap both local and imported premises"):
    val child = ProofCertificate(IndexedSeq(Restate(identityP, -1), Restate(identityP, 0)), IndexedSeq(identityP))
    val middle = ProofCertificate(IndexedSeq(Hypothesis(identityQ, q), Subproof(child, Seq(-1))), IndexedSeq(identityP))
    val outer = ProofCertificate(IndexedSeq(Hypothesis(identityP, p), Subproof(middle, Seq(0))))
    val flat = outer.toLinearProof
    assert(flat.steps.length == 4)
    assert(flat.steps(2).premises.sameElements(Array(0)))
    assert(flat.steps(3).premises.sameElements(Array(2)))
    assert(flat.check.exists(t => t.statement == identityP && !t.usesSorry && t.assumptions.isEmpty))

  test("restate equivalent but nonidentical subproof imports"):
    val expected = Sequent(Set.empty, Set(and(p)(top)))
    val child = ProofCertificate(IndexedSeq(Restate(expected, -1)), IndexedSeq(expected))
    val outer = ProofCertificate(IndexedSeq(Subproof(child, Seq(-1))), IndexedSeq(premiseP))
    assert(outer.toLinearProof.steps.length == 2)
    assert(outer.check.exists(_.statement == expected))

  test("reject a mismatched import even when the subproof does not use it"):
    val child = ProofCertificate(IndexedSeq(Hypothesis(identityP, p)), IndexedSeq(premiseQ))
    val outer = ProofCertificate(IndexedSeq(Subproof(child, Seq(-1))), IndexedSeq(premiseP))
    assert(outer.check.isLeft)

  test("reject malformed subproof mappings and forward references"):
    val child = ProofCertificate(IndexedSeq(Restate(premiseP, -1)), IndexedSeq(premiseP))
    assert(ProofCertificate(IndexedSeq(Subproof(child, Seq.empty))).check.isLeft)
    assert(ProofCertificate(IndexedSeq(Subproof(child, Seq(0)))).check.isLeft)
    assert(ProofCertificate(IndexedSeq(Subproof(child, Seq(Int.MinValue)))).check.isLeft)
    assert(ProofCertificate(Restate(premiseP, 0)).check.isLeft)
    assert(ProofCertificate(IndexedSeq.empty).check.isLeft)

  test("check unused inference steps instead of pruning their proof cones"):
    val invalid = Hypothesis(Sequent(Set.empty, Set.empty), p)
    val outer = ProofCertificate(IndexedSeq(invalid, Hypothesis(identityP, p)))
    assert(outer.check.isLeft)

  test("retain sorry tracking across subproof flattening"):
    val child = ProofCertificate(Sorry(premiseP))
    val outer = ProofCertificate(IndexedSeq(Subproof(child, Seq.empty)))
    assert(outer.check.exists(_.usesSorry))

  test("remap every reference in binary, variadic and discharge steps"):
    val steps = Seq[ProofStep](
      Cut(identityP, 1, -2, p),
      LeftImplies(identityP, 1, -2, p, q),
      RightIff(identityP, 1, -2, p, q),
      LeftOr(identityP, Array(1, -2), Seq(p, q)),
      RightAnd(identityP, Array(1, -2), Seq(p, q)),
      Discharge(identityP, 1, -2)
    )
    steps.foreach: step =>
      val mapped = ProofStep.mapPremises(step, _ + 10)
      assert(mapped.premises.sameElements(Array(11, 8)))
      assert(mapped.statement == step.statement)
      assert(step.premises.sameElements(Array(1, -2)))
