package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.utils.Helpers.{*, given}

/**
 * Axioms for the Tarski-Grothendieck theory (TG)
 */
private[settheory] trait SetTheoryTGAxioms extends SetTheoryZFAxioms {
  private val (x, y, z) =
    (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

  final val tarskiAxiom: Formula = forall(
    x,
    in(x, universe(x)) /\
      forall(
        y,
        in(y, universe(x)) ==> (in(powerSet(y), universe(x)) /\ subset(powerSet(y), universe(x))) /\
          forall(z, subset(z, universe(x)) ==> (sim(y, universe(x)) /\ in(y, universe(x))))
      )
  )

  runningSetTheory.addAxiom("TarskiAxiom", tarskiAxiom)

  override def axioms: Set[(String, Formula)] = super.axioms + (("TarskiAxiom", tarskiAxiom))

}
