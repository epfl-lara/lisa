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
   * Replacement Schema --- If a predicate `Ψ` is 'functional' over `x`, i.e.,
   * given `a ∈ x`, there is a unique `b` such that `Ψ(x, a, b)`, then the
   * 'image' of `x` in Ψ exists and is a set. It contains exactly the `b`'s that
   * satisfy `Ψ` for each `a ∈ x`.
   */
  final val replacementSchema: runningSetTheory.Axiom = runningSetTheory.makeAxiom(
    forall(a, in(a, x) ==> existsOne(b, sPsi(x, a, b))) ==>
      exists(y, forall(b, in(b, y) <=> exists(a, in(a, x) /\ sPsi(x, a, b))))
  )

  override def axioms: Set[(String, runningSetTheory.Axiom)] = super.axioms + (("replacementSchema", replacementSchema))

}
