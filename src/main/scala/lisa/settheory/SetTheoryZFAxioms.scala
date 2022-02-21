package lisa.settheory

import lisa.KernelHelpers.{_, given}
import lisa.kernel.fol.FOL._

/**
 * Axioms for the Zermelo-Fraenkel theory (ZF)
 */
private[settheory] trait SetTheoryZFAxioms extends SetTheoryZAxioms {

  final val replacementSchema: Axiom = forall(
    a,
    forall(x, (in(x, a)) ==> existsOne(y, sPsi(a, x, y))) ==>
      exists(b, forall(x, in(x, a) ==> exists(y, in(y, b) /\ sPsi(a, x, y))))
  )

}
