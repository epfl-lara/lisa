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
    val sp = modusPonens(p1(fixed_element()))(SCSubproof(Proof(IndexedSeq(hypothesis1), IndexedSeq(ax"p1_for_fixed")), Seq(-2)), SCSubproof(instantiate0, Seq(-1)))
    val proof = Proof(IndexedSeq(sp), IndexedSeq(ax"p1_implies_p2", ax"p1_for_fixed"))
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

  /* test theory |- f1(fixed_element) = fixed_element using byEquiv
   *
   *                                                          -------------------------------------- hypothesis
   *                                                         fixed point axiom |- fixed point axiom
   * -------------------------------- RightRefl       ------------------------------------------------------------------------------------ instantiate forall
   * |- fixed_element = fixed_element                   fixed point axiom |- f1(fixed_element) = fixed_element <=> fixed_element = fixed_element
   * ------------------------------------------------------------------------------------------------------------------------------------- byEquiv
   *                          fixed point axiom |- f1(fixed_element) = fixed_element
   * */
  test("byEquiv") {
    val instantiate0proof: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixed_element())
    val instantiate0 = SCSubproof(instantiate0proof, IndexedSeq(-1))
    val eq1 = RightRefl(() |- fixed_element() === fixed_element(), fixed_element() === fixed_element())
    val useEquiv = byEquiv(instantiate0proof.conclusion.right.head, eq1.bot.right.head)(instantiate0, SCSubproof(SCProof(eq1)))
    val proof: SCProof = Proof(IndexedSeq(useEquiv), IndexedSeq(ax"fixed_point"))
    checkProof(proof)
    checkProof(useEquiv.sp)
  }

  // illustrate by copying the body of byEquiv and making applicable changes that the claim can be proved by using byEquiv
  test("manual byEquiv") {
    val instantiate0: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixed_element())
    val eq1 = RightRefl(() |- fixed_element() === fixed_element(), fixed_element() === fixed_element())
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

  /* test theory |- f1(another_element) = fixed_element using byEquiv.
   * The proof is intentionally less succinct than possible to illustrate byEquiv usage when subproofs use axioms and have more than one step
   *
   *                                                          -------------------------------------- hypothesis
   *                                                          fixed point axiom |- fixed point axiom
   *  ---------------------------------- RightRefl         ----------------------------------------------------------------------------------------- instantiate forall
   *    |- fixed_element = fixed_element                   fixed point axiom |- f1(fixed_element) = fixed_element <=> fixed_element = fixed_element
   *  ----------------------------------right subst =    -------------------------------------------------------------------------------------------------------- right subst =
   *   same_fixed |- another_element = fixed_element     fixed point, same_fixed axioms |- f1(another_element) = fixed_element <=> another_element = fixed_element
   * --------------------------------------------------------------------------------------------------------------------------------------------------------- byEquiv
   *                          fixed point axiom |- f1(another_element) = fixed_element
   * */

  test("longer byEquiv") {
    val outerProofAxioms = IndexedSeq(ax"fixed_point", ax"same_fixed")

    val instantiate0 = instantiateForall(SCSubproof(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), IndexedSeq(-2)), fixed_point, fixed_element())
    val substEq1 = RightSubstEq(
      Set(fixed_point, same_fixed) |- (f1(another_fixed()) === fixed_element()) <=> (another_fixed() === fixed_element()),
      0,
      (fixed_element(), another_fixed()) :: Nil,
      LambdaTermFormula(Seq(xl), (f1(xl) === fixed_element()) <=> (xl === fixed_element()))
    )
    val subproofEquiv = SCSubproof(SCProof(IndexedSeq(instantiate0, substEq1), IndexedSeq(ax"same_fixed", ax"fixed_point")), IndexedSeq(-2, -1))
    val eq0 = RightRefl(() |- fixed_element() === fixed_element(), fixed_element() === fixed_element())
    val subst1 = RightSubstEq(
      same_fixed |- another_fixed() === fixed_element(),
      0,
      (fixed_element(), another_fixed()) :: Nil,
      LambdaTermFormula(Seq(xl), xl === fixed_element())
    )
    val subproofSide = SCSubproof(SCProof(IndexedSeq(eq0, subst1), IndexedSeq(ax"same_fixed")), IndexedSeq(-2))
    val useEquiv = byEquiv(substEq1.bot.right.head, subst1.bot.right.head)(
      subproofEquiv,
      subproofSide
    )
    val proof = Proof(IndexedSeq(useEquiv), outerProofAxioms)
    checkProof(proof)
    checkProof(useEquiv.sp)
  }
}
