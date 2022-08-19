package lisa.front.theory

import lisa.kernel.proof.RunningTheory
import lisa.settheory.AxiomaticSetTheory
import lisa.front.fol.FOL.*

/**
 * The set theory package. See [[lisa.settheory.AxiomaticSetTheory]].
 */
object SetTheory {

  // The purpose of this file is simply to lift the definitions from the kernel to the front

  /**
   * A safe type representing a formula that is considered as an axiom in this theory.
   */
  opaque type AxiomaticFormula <: Formula = Formula


  val membership: ConstantPredicateLabel[2] = fromKernel(AxiomaticSetTheory.in).asInstanceOf[ConstantPredicateLabel[2]]
  val subset: ConstantPredicateLabel[2] = fromKernel(AxiomaticSetTheory.subset).asInstanceOf[ConstantPredicateLabel[2]]
  val sameCardinality: ConstantPredicateLabel[2] = fromKernel(AxiomaticSetTheory.in).asInstanceOf[ConstantPredicateLabel[2]]

  val emptySet: ConstantFunctionLabel[0] = fromKernel(AxiomaticSetTheory.emptySet).asInstanceOf[ConstantFunctionLabel[0]]
  val unorderedPairSet: ConstantFunctionLabel[2] = fromKernel(AxiomaticSetTheory.pair).asInstanceOf[ConstantFunctionLabel[2]]
  val singletonSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.singleton).asInstanceOf[ConstantFunctionLabel[1]]
  val powerSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.powerSet).asInstanceOf[ConstantFunctionLabel[1]]
  val unionSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.union).asInstanceOf[ConstantFunctionLabel[1]]
  val universeSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.universe).asInstanceOf[ConstantFunctionLabel[1]]

  val axiomEmpty: AxiomaticFormula = fromKernel(AxiomaticSetTheory.emptySetAxiom)
  val axiomExtensionality: AxiomaticFormula = fromKernel(AxiomaticSetTheory.extensionalityAxiom)
  val axiomPair: AxiomaticFormula = fromKernel(AxiomaticSetTheory.pairAxiom)
  val axiomUnion: AxiomaticFormula = fromKernel(AxiomaticSetTheory.unionAxiom)
  val axiomPower: AxiomaticFormula = fromKernel(AxiomaticSetTheory.powerAxiom)
  val axiomFoundation: AxiomaticFormula = fromKernel(AxiomaticSetTheory.foundationAxiom)

  val axiomSchemaReplacement: AxiomaticFormula = fromKernel(AxiomaticSetTheory.replacementSchema)

  val axiomTarski: AxiomaticFormula = fromKernel(AxiomaticSetTheory.tarskiAxiom)

  val definitionSubset: AxiomaticFormula = {
    val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))
    forall(x, forall(y, subset(x, y) <=> forall(z, (z in x) ==> (z in y))))
  }

  extension (term: Term) {
    infix def in(other: Term): Formula = membership(term, other)
    def subsetOf(other: Term): Formula = subset(term, other)
    infix def ~(other: Term): Formula = sameCardinality(term, other)
  }



}
