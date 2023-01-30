package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.utils.KernelHelpers.{_, given}

/**
 * Axioms for the Zermelo theory (Z)
 */
private[settheory] trait SetTheoryZAxioms extends SetTheoryDefinitions {

  private val (x, y, z) =
    (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))
  final val sPhi = SchematicPredicateLabel("P", 2)

  final val emptySetAxiom: Formula = !in(x, emptySet())
  final val extensionalityAxiom: Formula = forall(z, in(z, x) <=> in(z, y)) <=> (x === y)
  final val subsetAxiom: Formula = subset(x, y) <=> forall(z, in(z, x) ==> in(z, y))
  final val pairAxiom: Formula = in(z, unorderedPair(x, y)) <=> (x === z) \/ (y === z)
  final val unionAxiom: Formula = in(x, union(z)) <=> exists(y, in(x, y) /\ in(y, z))
  final val powerAxiom: Formula = in(x, powerSet(y)) <=> subset(x, y)
  final val foundationAxiom: Formula = !(x === emptySet()) ==> exists(y, in(y, x) /\ forall(z, in(z, x) ==> !in(z, y)))
  final val infinityAxiom: Formula = exists(x, in(emptySet(), x) /\ forall(y, in(y, x) ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)))

  final val comprehensionSchema: Formula = exists(y, forall(x, in(x, y) <=> (in(x, z) /\ sPhi(x, z))))

  private val zAxioms: Set[(String, Formula)] = Set(
    ("EmptySet", emptySetAxiom),
    ("extensionalityAxiom", extensionalityAxiom),
    ("pairAxiom", pairAxiom),
    ("unionAxiom", unionAxiom),
    ("subsetAxiom", subsetAxiom),
    ("powerAxiom", powerAxiom),
    ("foundationAxiom", foundationAxiom),
    ("infinityAxiom", infinityAxiom),
    ("comprehensionSchema", comprehensionSchema)
  )

  zAxioms.foreach(a => runningSetTheory.addAxiom(a._1, a._2))

  override def axioms: Set[(String, Formula)] = super.axioms ++ zAxioms

}
