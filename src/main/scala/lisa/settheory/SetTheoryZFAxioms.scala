package lisa.settheory

import lisa.kernel.fol.FOL._
import utilities.Helpers.{_, given}

/**
 * Axioms for the Zermelo-Fraenkel theory (ZF)
 */
private[settheory] trait SetTheoryZFAxioms extends SetTheoryZAxioms {

  final val replacementSchema: Axiom = forall(
    a,
    forall(x, (in(x, a)) ==> existsOne(y, sPsi(a, x, y))) ==>
      exists(b, forall(x, in(x, a) ==> exists(y, in(y, b) /\ sPsi(a, x, y))))
  )
  runningSetTheory.addAxiom("replacementSchema", replacementSchema)

  override def axioms: Set[(String, Axiom)] = super.axioms + (("replacementSchema", replacementSchema))

}
