package lisa.settheory

import lisa.fol.FOL.{_, given}
import lisa.utils.K
import lisa.utils.K.makeAxiom

/**
 * Axioms for the Zermelo-Fraenkel theory (ZF)
 */
private[settheory] trait SetTheoryZFAxioms extends SetTheoryZAxioms {
  private val x = variable
  private val y = variable
  private val A = variable
  private val B = variable
  private val P = predicate[3]
  // private final val sPsi = SchematicPredicateLabel("P", 3)

  /**
   * Replacement Schema --- If a predicate `P` is 'functional' over `x`, i.e.,
   * given `a ∈ x`, there is a unique `b` such that `P(x, a, b)`, then the
   * 'image' of `x` in P exists and is a set. It contains exactly the `b`'s that
   * satisfy `P` for each `a ∈ x`.
   */
  final val replacementSchema: AXIOM = Axiom(
    "replacementSchema",
    forall(A, in(A, x) ==> existsOne(B, P(x, A, B))) ==>
      exists(y, forall(B, in(B, y) <=> exists(A, in(A, x) /\ P(x, A, B))))
  )

  override def axioms: Set[(String, AXIOM)] = super.axioms + (("replacementSchema", replacementSchema))

}
