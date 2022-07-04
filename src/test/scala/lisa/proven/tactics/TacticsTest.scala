package lisa.proven.tactics

import lisa.kernel.fol.FOL.isSame
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.proven.tactics.ProofTactics.*
import lisa.test.ProofCheckerSuite
import lisa.test.TestTheoryLibrary
import lisa.utils.Helpers.emptySeq
import lisa.utils.Helpers.{_, given}

class TacticsTest extends ProofCheckerSuite {
  export TestTheoryLibrary.*
  /* test theory |- p2(fixedElement) using modus ponens
   *
   *
   *                                                                  -------------------------------------------- hypothesis
   *                                                                   p1_implies_p2 axiom |- p1_implies_p2 axiom
   *  ----------------------------------------- hypothesis        ----------------------------------------------------------------- instantiate forall
   *          axiom 2 |- p1(fixedElement)                           p1_implies_p2 axiom |- p1(fixedElement) => p2(fixedElement)
   * ------------------------------------------------------------------------------------------------------------------------------ modus ponens
   *                                     ∀x p1(x) => p2(x), p1(fixedElement) |- p2(fixedElement)
   *
   * */
  test("modus ponens") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(p1_implies_p2)), IndexedSeq(ax"p1_implies_p2")), p1_implies_p2, fixedElement())
    val hypothesis1 = hypothesis(ax2)
    val proof = modusPonens(p1(fixedElement()))(hypothesis1, SCSubproof(instantiate0, Seq(-1)))
    checkProof(proof)
  }

  // illustrate by copying the body of modusPonens and making applicable changes that the claim can be proved by using modus ponens
  test("manual modus ponens") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(p1_implies_p2)), IndexedSeq(ax"p1_implies_p2")), p1_implies_p2, fixedElement())
    val hypothesis1 = hypothesis(ax2)
    val pa = hypothesis1
    val pb = SCSubproof(instantiate0, Seq(-1))
    val phi = p1(fixedElement())
    val psi = p2(fixedElement())
    val mp2 = hypothesis(psi)
    val mp3 = LeftImplies(emptySeq ++ (pa.bot -> phi) +< (phi ==> psi) +> psi, 0, 2, phi, psi)
    val mp4 = Cut(emptySeq ++ (pa.bot -> phi) ++< pb.bot +> psi ++> (pb.bot -> (phi ==> psi)), 1, 3, phi ==> psi)
    val proof = Proof(IndexedSeq(pa, pb, mp2, mp3, mp4), IndexedSeq(ax"p1_implies_p2", ax"A2"))
    checkProof(proof)
  }

  /* test theory |- f1(fixedElement) = fixedElement using byEquiv
   *
   *                                                          -------------------------------------- hypothesis
   *                                                         fixed point axiom |- fixed point axiom
   * -------------------------------- RightRefl       ------------------------------------------------------------------------------------ instantiate forall
   * |- fixedElement = fixedElement                   fixed point axiom |- f1(fixedElement) = fixedElement <=> fixedElement = fixedElement
   * ------------------------------------------------------------------------------------------------------------------------------------- byEquiv
   *                          fixed point axiom |- f1(fixedElement) = fixedElement
   * */
  test("byEquiv") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixedElement())
    val eq1 = RightRefl(() |- fixedElement() === fixedElement(), fixedElement() === fixedElement())
    val proof = byEquiv(instantiate0.conclusion.right.head, eq1.bot.right.head)(SCSubproof(instantiate0, IndexedSeq(-1)), eq1)
    checkProof(proof)
  }

  // illustrate by copying the body of byEquiv and making applicable changes that the claim can be proved by using byEquiv
  test("manual byEquiv") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixedElement())
    val eq1 = RightRefl(() |- fixedElement() === fixedElement(), fixedElement() === fixedElement())
    val f = instantiate0.conclusion.right.head
    val f1 = eq1.bot.right.head
    val pEq = SCSubproof(instantiate0, IndexedSeq(-1))
    val pr1 = eq1
    require(pEq.bot.right.contains(f))
    require(pr1.bot.right.contains(f1))
    val proof = f match {
      case ConnectorFormula(Iff, Seq(fl, fr)) =>
        val f2 = if (isSame(f1, fl)) fr else if (isSame(f1, fr)) fl else throw new Error("not applicable")
        val p2 = hypothesis(f1)
        val p3 = hypothesis(f2)
        val p4 = LeftImplies(Sequent(Set(f1, f1 ==> f2), Set(f2)), 2, 3, f1, f2)
        val p5 = LeftIff(Sequent(Set(f1, f1 <=> f2), Set(f2)), 4, f1, f2)
        val p6 = Cut(pEq.bot -> (f1 <=> f2) +< f1 +> f2, 0, 5, f1 <=> f2)
        val p7 = Cut(p6.bot -< f1 ++ pr1.bot -> f1, 1, 6, f1)
        new SCProof(IndexedSeq(pEq, pr1, p2, p3, p4, p5, p6, p7), IndexedSeq(ax"fixed_point"))
      case _ => throw new Error("not applicable")
    }
    checkProof(proof)
  }

  /* test theory |- f1(another_element) = fixedElement using byEquiv.
   * The proof is intentionally less succinct than possible to illustrate byEquiv usage when subproofs use axioms and have more than one step
   *
   *                                                          -------------------------------------- hypothesis
   *                                                          fixed point axiom |- fixed point axiom
   *  ---------------------------------- RightRefl         ----------------------------------------------------------------------------------------- instantiate forall
   *    |- fixedElement = fixedElement                   fixed point axiom |- f1(fixedElement) = fixedElement <=> fixedElement = fixedElement
   *  ----------------------------------right subst =    -------------------------------------------------------------------------------------------------------- right subst =
   *   same_fixed |- another_element = fixedElement     fixed point, same_fixed axioms |- f1(another_element) = fixedElement <=> another_element = fixedElement
   * --------------------------------------------------------------------------------------------------------------------------------------------------------- byEquiv
   *                          fixed point axiom |- f1(another_element) = fixedElement
   * */

  test("longer byEquiv") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixedElement())
    val substEq1 = RightSubstEq(
      Set(fixed_point, same_fixed) |- (f1(anotherFixed()) === fixedElement()) <=> (anotherFixed() === fixedElement()),
      0,
      (fixedElement(), anotherFixed()) :: Nil,
      LambdaTermFormula(Seq(xl), (f1(xl) === fixedElement()) <=> (xl === fixedElement()))
    )
    val eq2 = RightRefl(() |- fixedElement() === fixedElement(), fixedElement() === fixedElement())
    val substEq3 = RightSubstEq(
      same_fixed |- anotherFixed() === fixedElement(),
      2,
      (fixedElement(), anotherFixed()) :: Nil,
      LambdaTermFormula(Seq(xl), xl === fixedElement())
    )

    val proof = byEquiv(substEq1.bot.right.head, substEq3.bot.right.head)(substEq1, substEq3)
    checkProof(proof)
  }
}
