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
    val sp = modusPonens(p1(fixedElement()))(SCSubproof(Proof(IndexedSeq(hypothesis1), IndexedSeq(ax"A2")), Seq(-2)), SCSubproof(instantiate0, Seq(-1)))
    val proof = Proof(IndexedSeq(sp), IndexedSeq(ax"p1_implies_p2", ax"A2"))
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
    val instantiate0proof: Proof = instantiateForall(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), fixed_point, fixedElement())
    val instantiate0 = SCSubproof(instantiate0proof, IndexedSeq(-1))
    val eq1 = RightRefl(() |- fixedElement() === fixedElement(), fixedElement() === fixedElement())
    val useEquiv = byEquiv(instantiate0proof.conclusion.right.head, eq1.bot.right.head)(instantiate0, SCSubproof(SCProof(eq1)))
    val proof: SCProof = Proof(IndexedSeq(useEquiv), IndexedSeq(ax"fixed_point"))
    checkProof(proof)
    checkProof(useEquiv.sp)
  }

  /* test theory |- f1(anotherFixed) = fixedElement using byEquiv.
   * The proof is intentionally less succinct than possible to illustrate byEquiv usage when subproofs use axioms and have more than one step
   *
   *                                                          -------------------------------------- hypothesis
   *                                                          fixed point axiom |- fixed point axiom
   *  ---------------------------------- RightRefl         ----------------------------------------------------------------------------------------- instantiate forall
   *    |- fixedElement = fixedElement                   fixed point axiom |- f1(fixedElement) = fixedElement <=> fixedElement = fixedElement
   *  ----------------------------------right subst =    -------------------------------------------------------------------------------------------------------- right subst =
   *   same_fixed |- anotherFixed = fixedElement     fixed point, same_fixed axioms |- f1(anotherFixed) = fixedElement <=> anotherFixed = fixedElement
   * --------------------------------------------------------------------------------------------------------------------------------------------------------- byEquiv
   *                          fixed point axiom |- f1(anotherFixed) = fixedElement
   * */

  test("longer byEquiv") {
    val outerProofAxioms = IndexedSeq(ax"fixed_point", ax"same_fixed")

    val instantiate0 = instantiateForall(SCSubproof(Proof(IndexedSeq(hypothesis(fixed_point)), IndexedSeq(ax"fixed_point")), IndexedSeq(-2)), fixed_point, fixedElement())
    val substEq1 = RightSubstEq(
      Set(fixed_point, same_fixed) |- (f1(anotherFixed()) === fixedElement()) <=> (anotherFixed() === fixedElement()),
      0,
      (fixedElement(), anotherFixed()) :: Nil,
      LambdaTermFormula(Seq(xl), (f1(xl) === fixedElement()) <=> (xl === fixedElement()))
    )
    val subproofEquiv = SCSubproof(SCProof(IndexedSeq(instantiate0, substEq1), IndexedSeq(ax"same_fixed", ax"fixed_point")), IndexedSeq(-2, -1))
    val eq0 = RightRefl(() |- fixedElement() === fixedElement(), fixedElement() === fixedElement())
    val subst1 = RightSubstEq(
      same_fixed |- anotherFixed() === fixedElement(),
      0,
      (fixedElement(), anotherFixed()) :: Nil,
      LambdaTermFormula(Seq(xl), xl === fixedElement())
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
