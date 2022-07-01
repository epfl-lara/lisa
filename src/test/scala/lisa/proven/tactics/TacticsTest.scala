package lisa.proven.tactics

import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.proven.tactics.ProofTactics.*
import lisa.test.ProofCheckerSuite
import lisa.test.TestTheoryLibrary
import lisa.utils.Helpers._
import lisa.utils.Helpers.emptySeq

class TacticsTest extends ProofCheckerSuite {
  export TestTheoryLibrary.*
  /* test theory |- p2(fixed_element) using modus ponens
   *
   *
   *                                                                  -------------------------------------------- hypothesis
   *                                                                   p1_implies_p2 axiom |- p1_implies_p2 axiom
   *  ----------------------------------------- hypothesis        ----------------------------------------------------------------- instantiate forall
   *   p1_for_fixed axiom |- p1(fixed_element)                      p1_implies_p2 axiom |- p1(fixed_element) => p2(fixed_element)
   * ------------------------------------------------------------------------------------------------------------------------------ modus ponens
   *                                     ∀x p1(x) => p2(x), p1(fixed_element) |- p2(fixed_element)
   *
   * */
  test("modus ponens") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(p1_implies_p2)), IndexedSeq(ax"p1_implies_p2")), p1_implies_p2, fixed_element())
    val hypothesis1 = hypothesis(p1_for_fixed)
    val proof = modusPonens(p1(fixed_element()))(hypothesis1, SCSubproof(instantiate0, Seq(-1)))
    checkProof(proof)
  }

  // illustrate by copying the body of modusPonens and making applicable changes that the claim can be proved by using modus ponens
  test("manual modus ponens") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(p1_implies_p2)), IndexedSeq(ax"p1_implies_p2")), p1_implies_p2, fixed_element())
    val hypothesis1 = hypothesis(p1_for_fixed)
    val pa = hypothesis1
    val pb = SCSubproof(instantiate0, Seq(-1))
    val phi = p1(fixed_element())
    val psi = p2(fixed_element())
    val mp2 = hypothesis(psi)
    val mp3 = LeftImplies(emptySeq ++ (pa.bot -> phi) +< (phi ==> psi) +> psi, 0, 2, phi, psi)
    val mp4 = Cut(emptySeq ++ (pa.bot -> phi) ++< pb.bot +> psi ++> (pb.bot -> (phi ==> psi)), 1, 3, phi ==> psi)
    val proof = Proof(IndexedSeq(pa, pb, mp2, mp3, mp4), IndexedSeq(ax"p1_implies_p2", ax"p1_for_fixed"))
    checkProof(proof)
  }

  test("byEquiv") {}
}
