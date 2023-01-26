package lisa.utilities
import lisa.automation.kernel.Destructors.*
import lisa.automation.kernel.ProofTactics.*
import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.test.ProofCheckerSuite
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.Printer

class Transformations extends ProofCheckerSuite {
  // import lisa.settheory.SetTheoryLibrary.*

  test("Trasnsformation initialises well with empty proof and returns an empty proof") {
    val nullSCProof = SCProof()
    val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(nullSCProof)
    assert(transf.transform() == nullSCProof)
  }

  /**
   * Any proof where there are no imports shoud not be modified
   * Dummy proofs of varying size should be tested
   */
  test("A proof with no imports is not modified") {
    val phi = SchematicPredicateLabel("phi", 0)

    val intro = Hypothesis((phi()) |- (phi()), phi())
    val outro = Rewrite((phi()) |- (phi()), 0)

    val noImpProof = SCProof(IndexedSeq(intro, outro), IndexedSeq.empty)
    val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof)

    // assert((transf.transform() == noImpProof))
    checkProof(noImpProof)
  }

  test("A proof with imports is to be modified") {
    val phi = SchematicPredicateLabel("phi", 0)

    val intro = Rewrite(() |- phi(), -1)
    val outro = Weakening(intro.bot.right |- intro.bot.right, 0)

    val noImpProof = SCProof(IndexedSeq(intro, outro), IndexedSeq(intro.bot))
    val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof).transform()

    checkProof(transf)
    assert(transf != noImpProof)
    assert(isSameSequent(transf.steps.last.bot, (sequentToFormula(intro.bot)) |- intro.bot.right))
  }

  test("A proof with imports and a step taking multiple premises should be modified accordingly") {
    val phi = SchematicPredicateLabel("phi", 0)()
    val psi = SchematicPredicateLabel("psi", 0)()

    val into1 = Rewrite(() |- phi, -2)
    val into2 = Rewrite(() |- psi, -1)
    val merge = RightAnd(() |- ConnectorFormula(And, (into1.bot.right ++ into2.bot.right).toSeq), Seq(-2, 0), (into1.bot.right ++ into2.bot.right).toSeq)

    val noImpProof = SCProof(IndexedSeq(into2, merge), IndexedSeq(into2.bot, into1.bot))
    val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof).transform()

    checkProof(transf)
    assert(transf != noImpProof)
    assert(isSameSequent(transf.steps.last.bot, (sequentToFormula(into1.bot), sequentToFormula(into2.bot)) |- merge.bot.right))
  }

  test("A proof with imports and a subproof should be modified accordingly") {
    val phi = SchematicPredicateLabel("phi", 0)()
    val intro = Rewrite(() |- phi, -1)
    val outro = SCSubproof(SCProof(IndexedSeq(Weakening(intro.bot.right |- intro.bot.right, -1)), IndexedSeq(intro.bot)), IndexedSeq(0))
    val noImpProof = SCProof(IndexedSeq(intro, outro), IndexedSeq(intro.bot))
    val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof).transform()

    checkProof(transf)
    assert(transf != noImpProof)
    assert(isSameSequent(transf.steps.last.bot, (outro.bot.left + sequentToFormula(intro.bot)) |- outro.bot.right))

  }

  test("A proof with imports and a complete instantiation should be modified accordingly") {
    val phi = SchematicPredicateLabel("phi", 0)
    val psi = SchematicPredicateLabel("psi", 2)
    val x = VariableLabel("x")
    val y = VariableLabel("y")

    val intro = Rewrite(() |- phi(), -1)
    val outro = InstSchema(() |- psi(x, y), 0, Map.empty, Map((phi, LambdaTermFormula(Seq(), psi(x, y)))), Map.empty)
    val noImpProof = SCProof(IndexedSeq(intro, outro), IndexedSeq(intro.bot))
    val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof).transform()
    checkProof(transf)
    assert(transf != noImpProof)
    assert(isSameSequent(transf.steps.last.bot, (sequentToFormula(outro.bot)) |- outro.bot.right))

  }

  test("A proof with imports and two partial instantiations should be modified accordingly") {
    val phi = SchematicPredicateLabel("phi", 0)
    val psi = SchematicPredicateLabel("psi", 2)
    val lambda = SchematicPredicateLabel("lambda", 2)
    val x = VariableLabel("x")
    val y = VariableLabel("y")

    val intro = Rewrite(() |- phi(), -1)
    val mid = InstSchema(() |- psi(x, y) <=> phi(), 0, Map.empty, Map((phi, LambdaTermFormula(Seq(), psi(x, y) <=> phi()))), Map.empty)
    val outro = InstSchema(() |- psi(x, y) <=> lambda(x, y), 1, Map.empty, Map((phi, LambdaTermFormula(Seq(), lambda(x, y)))), Map.empty)
    val weak = Weakening((psi(x, y)) |- psi(x, y) <=> lambda(x, y), 2)
    val noImpProof = SCProof(IndexedSeq(intro, mid, outro, weak), IndexedSeq(intro.bot))
    val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof).transform()

    checkProof(transf)
    assert(transf != noImpProof)
    assert(isSameSequent(transf.steps.last.bot, ((weak.bot.left + sequentToFormula(outro.bot))) |- weak.bot.right))
  }

  test("A proof with instantiation can be transformed into one with a rewrite and an import") {
    val phi = SchematicPredicateLabel("phi", 0)
    val psi = SchematicPredicateLabel("psi", 2)
    val x = VariableLabel("x")
    val y = VariableLabel("y")

    val intro = Rewrite(() |- phi(), -1)
    val outro = InstSchema(() |- psi(x, y), 0, Map.empty, Map((phi, LambdaTermFormula(Seq(), psi(x, y)))), Map.empty)
    val noImpProof = SCProof(IndexedSeq(intro, outro), IndexedSeq(intro.bot))
    val transf = lisa.utilities.prooftransform.ProofInstantiationRemover(noImpProof).transform()

    checkProof(transf)
    assert(transf != noImpProof)
    assert(isSameSequent(transf.steps.last.bot, () |- outro.bot.right))
  }
}
