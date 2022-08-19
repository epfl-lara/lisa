package lisa.front.proof.sequent

import lisa.front.fol.FOL.*

trait SequentDefinitions {

  protected def pretty(sequent: Sequent): String
  protected def pretty(sequent: PartialSequent): String

  /**
   * The base sequent object; used to represent both the concrete sequent and its partial counterpart.
   */
  sealed abstract class SequentBase {
    val left: IndexedSeq[Formula]
    val right: IndexedSeq[Formula]

    def formulas: IndexedSeq[Formula] = left ++ right
  }

  /**
   * A sequent is a pair of indexable collections of formulas.
   * @param left the left hand side of this sequent
   * @param right the right hand side of this sequent
   */
  final case class Sequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula]) extends SequentBase {
    override def toString: String = pretty(this)
  }

  /**
   * A partial sequent is a representation of a sequent where only a part of the formulas are known.
   * @param left the left hand side of this partial sequent
   * @param right the right hand side of this partial sequent
   * @param partialLeft whether the left hand side is partial
   * @param partialRight whether the right hand side is partial
   */
  final case class PartialSequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula], partialLeft: Boolean = true, partialRight: Boolean = true) extends SequentBase {
    override def toString: String = pretty(this)
  }

  def functionsOfSequent(sequent: SequentBase): Set[TermLabel[?]] = sequent.formulas.flatMap(termLabelsOf).toSet

  def predicatesOfSequent(sequent: SequentBase): Set[PredicateLabel[?]] = sequent.formulas.flatMap(predicatesOf).toSet

  def schematicFunctionsOfSequent(sequent: SequentBase): Set[SchematicTermLabel[?]] =
    functionsOfSequent(sequent).collect { case l: SchematicTermLabel[?] => l }

  def schematicPredicatesOfSequent(sequent: SequentBase): Set[SchematicPredicateLabel[?]] =
    predicatesOfSequent(sequent).collect { case l: SchematicPredicateLabel[?] => l }

  def schematicConnectorsOfSequent(sequent: SequentBase): Set[SchematicConnectorLabel[?]] =
    sequent.formulas.flatMap(schematicConnectorsOf).toSet

  def freeVariablesOfSequent(sequent: SequentBase): Set[VariableLabel] = sequent.formulas.flatMap(freeVariablesOf).toSet

  def declaredBoundVariablesOfSequent(sequent: SequentBase): Set[VariableLabel] =
    sequent.formulas.flatMap(declaredBoundVariablesOf).toSet

  def isSequentWellFormed(sequent: SequentBase): Boolean =
    sequent.formulas.forall(isWellFormed)

  // Only full sequents should be converted to the kernel
  def sequentToKernel(sequent: Sequent): lisa.kernel.proof.SequentCalculus.Sequent =
    lisa.kernel.proof.SequentCalculus.Sequent(
      sequent.left.map(toKernel).toSet,
      sequent.right.map(toKernel).toSet
    )

  given Conversion[Sequent, lisa.kernel.proof.SequentCalculus.Sequent] = sequentToKernel

  def isSameSequent(s1: Sequent, s2: Sequent): Boolean =
    lisa.kernel.proof.SequentCalculus.isSameSequent(s1, s2)

  def instantiateSequentSchemas(
    sequent: Sequent,
    functions: Seq[AssignedFunction] = Seq.empty,
    predicates: Seq[AssignedPredicate] = Seq.empty,
    connectors: Seq[AssignedConnector] = Seq.empty,
  ): Sequent = {
    def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
      formulas.map(instantiateFormulaSchemas(_, functions, predicates, connectors))
    Sequent(instantiate(sequent.left), instantiate(sequent.right))
  }

}
