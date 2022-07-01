package lisa.proven.tactics

import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.proven.tactics.ProofTactics.*
import lisa.test.ProofCheckerSuite
import lisa.test.TestTheoryLibrary
import lisa.utils.Helpers._
import lisa.utils.Helpers.emptySeq

class TacticsTest extends ProofCheckerSuite {
  export TestTheoryLibrary.*
  /* A (overcomplicated for the sake of the test) proof that f1(fixedElement) = fixedElement in test theory
   *
   *
   *                                                         -------------------------------------- hypothesis
   *                                                         fixed point axiom |- fixed point axiom
   *                                                  ------------------------------------------------------------------------------------ instantiate forall
   *                                                  fixed point axiom |- f1(fixedElement) = fixedElement <-> fixedElement = fixedElement
   * -------------------------------- RightRefl       ------------------------------------------------------------------------------------ weaken <-> to ->
   *  |- fixedElement = fixedElement                  fixed point axiom |- fixedElement = fixedElement -> f1(fixedElement) = fixedElement
   * ------------------------------------------------------------------------------------------------------------------------------------- modus ponens
   *                                     fixed point axiom |- f1(fixedElement) = fixedElement
   *
   * */
  test("modus ponens") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixedElement())
    val weakenIffToImplies = iffToImplies(
      (f1(fixedElement()) === fixedElement()) <=> (fixedElement() === fixedElement()),
      (fixedElement() === fixedElement()) ==> (f1(fixedElement()) === fixedElement())
    )(
      SCSubproof(instantiate0, IndexedSeq(-1))
    )
    val eq2 = RightRefl(() |- fixedElement() === fixedElement(), fixedElement() === fixedElement())
    val proof = modusPonens(fixedElement() === fixedElement())(eq2, weakenIffToImplies)
    assert(checkSCProof(proof).isValid, "application of modus ponens yields an invalid proof")
  }

  test("explicit modus ponens") {
    val eq0 = RightRefl(() |- fixedElement() === fixedElement(), fixedElement() === fixedElement())
    val instantiate1: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixedElement())
    val weakenIffToImplies1 = iffToImplies(
      (f1(fixedElement()) === fixedElement()) <=> (fixedElement() === fixedElement()),
      (fixedElement() === fixedElement()) ==> (f1(fixedElement()) === fixedElement())
    )(SCSubproof(instantiate1, IndexedSeq(-1)))
    val pa = eq0
    val pb = weakenIffToImplies1
    val phi = fixedElement() === fixedElement()
    val psi = f1(fixedElement()) === fixedElement()
    val p2 = hypothesis(psi)
    val p3 = LeftImplies(emptySeq ++ (pa.bot -> phi) +< (phi ==> psi) +> psi, 0, 2, phi, psi)
    val p4 = Cut(emptySeq ++ (pa.bot -> phi) ++< pb.bot +> psi ++> (pb.bot -> psi), 1, 3, phi ==> psi)
    val proof = Proof(IndexedSeq(eq0, weakenIffToImplies1, p2, p3, p4), IndexedSeq(ax"fixed_point"))
    checkProof(proof)
  }

  test("byEquiv") {}
}
