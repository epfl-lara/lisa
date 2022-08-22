package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.utils.Helpers.{*, given}

/**
 * Axioms for the Zermelo-Fraenkel theory (ZF)
 */
private[settheory] trait SetTheoryZFAxioms extends SetTheoryZAxioms {
  private val (x, y, a, b) =
    (VariableLabel("x"), VariableLabel("y"), VariableLabel("A"), VariableLabel("B"))
  private final val sPsi = SchematicPredicateLabel("P", 3)

  final val replacementSchema: Formula = forall(
    a,
    forall(x, (in(x, a)) ==> existsOne(y, sPsi(a, x, y))) ==>
      exists(b, forall(x, in(x, a) ==> exists(y, in(y, b) /\ sPsi(a, x, y))))
  )
  runningSetTheory.addAxiom("replacementSchema", replacementSchema)

  override def axioms: Set[(String, Formula)] = super.axioms + (("replacementSchema", replacementSchema))

}
