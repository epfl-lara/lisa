package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}

/**
 * Axioms for the Zermelo-Fraenkel theory (ZF)
 */
private[settheory] trait SetTheoryZFAxioms extends SetTheoryZAxioms {
  private val (x, y, a, b) =
    (VariableLabel("x"), VariableLabel("y"), VariableLabel("A"), VariableLabel("B"))
  private final val sPsi = SchematicPredicateLabel("P", 3)

  /**
   * Replacement Schema
   *
   * If a predicate \psi is 'functional' over a, i.e., given x \in a, there is a unique y such that \psi(a, x, y), then the 'image' of a in \psi exists and is a set. It contains exactly the y's that satisfy \psi for each x \in a.
   */
  final val replacementSchema: Formula = forall(x, (in(x, a)) ==> existsOne(y, sPsi(a, x, y))) ==>
    exists(b, forall(x, in(x, a) ==> exists(y, in(y, b) /\ sPsi(a, x, y))))

  runningSetTheory.addAxiom("replacementSchema", replacementSchema)

  override def axioms: Set[(String, Formula)] = super.axioms + (("replacementSchema", replacementSchema))

}
