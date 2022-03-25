package lisa.settheory

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.KernelHelpers.{given, _}
/**
 * Axioms for the Zermelo theory (Z)
 */
private[settheory] trait SetTheoryZAxioms extends SetTheoryDefinitions {

  final val emptySetAxiom: Axiom = forall(x, !in(x, emptySet()))
  final val extensionalityAxiom: Axiom = forall(x, forall(y, forall(z, in(z, x) <=> in(z, y)) <=> (x === y)))
  final val pairAxiom: Axiom = forall(x, forall(y, forall(z, in(z, pair(x, y)) <=> (x === z) \/ (y === z))))
  final val unionAxiom: Axiom = forall(x, forall(z, in(x, union(z)) <=> exists(y, in(x, y) /\ in(y, z))))
  final val powerAxiom: Axiom = forall(x, forall(y, in(x, powerSet(y)) <=> subset(x, y)))
  final val foundationAxiom: Axiom = forall(x, !(x === emptySet()) ==> exists(y, in(y, x) /\ forall(z, in(z, x) ==> !in(z, y))))


  final val comprehensionSchema: Axiom = forall(z, exists(y, forall(x, in(x,y) <=> (in(x,z) /\ sPhi(x,z)))))

  private val zAxioms: Set[Axiom] = Set(emptySetAxiom, extensionalityAxiom, pairAxiom, unionAxiom, powerAxiom, foundationAxiom, comprehensionSchema)


  
  zAxioms.foreach(a => runningSetTheory.addAxiom(a))
    
  override def axioms: Set[Axiom] = super.axioms ++ zAxioms

}