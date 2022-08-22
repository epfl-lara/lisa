package lisa.automation.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.*

import scala.collection.mutable.Set as mSet

/**
 * A simple but complete solver for propositional logic. Will not terminate for large problems
 */
object SimplePropositionalSolver {
  class OrganisedFormulaSet {
    val negs: mSet[ConnectorFormula] = mSet()
    val impliess: mSet[ConnectorFormula] = mSet()
    val iffs: mSet[ConnectorFormula] = mSet()
    val ands: mSet[ConnectorFormula] = mSet()
    val ors: mSet[ConnectorFormula] = mSet()
    val others: mSet[Formula] = mSet()

    def updateFormula(phi: Formula, add: Boolean): Unit = (phi match {
      case phi@ConnectorFormula(label, args) =>
        label match {
          case Neg => if (add) negs.add(phi) else negs.remove(phi)
          case Implies => if (add) impliess.add(phi) else impliess.remove(phi)
          case Iff => if (add) iffs.add(phi) else iffs.remove(phi)
          case And => if (add) ands.add(phi) else ands.remove(phi)
          case Or => if (add) ors.add(phi) else ors.remove(phi)
          case _ => if (add) others.add(phi) else others.remove(phi)
        }
      case _ => if (add) others.add(phi) else others.remove(phi)
    })

    def copy(): OrganisedFormulaSet = {
      val r = new OrganisedFormulaSet
      r.negs.addAll(negs)
      r.impliess.addAll(impliess)
      r.iffs.addAll(iffs)
      r.ands.addAll(ands)
      r.ors.addAll(ors)
      r.others.addAll(others)
      r
    }
  }

  def solveOrganisedSequent(left: OrganisedFormulaSet, right: OrganisedFormulaSet, s: Sequent, offset: Int): List[SCProofStep] = {
    if (left.negs.nonEmpty) {
      val f = left.negs.head
      val phi = f.args.head
      left.updateFormula(f, false)
      right.updateFormula(f.args.head, true)
      val proof = solveOrganisedSequent(left, right, s -< f +> phi, offset)
      LeftNot(s, proof.length - 1 + offset, phi) :: proof
    } else if (left.impliess.nonEmpty) {
      val f = left.impliess.head
      val phi = f.args(0)
      val psi = f.args(1)

      left.updateFormula(f, false) // gamma
      val rl = left.copy() // sigma
      val rr = right.copy() // pi
      right.updateFormula(phi, true) // delta
      rl.updateFormula(psi, true)
      val proof1 = solveOrganisedSequent(left, right, s -< f +> phi, offset)
      val proof2 = solveOrganisedSequent(rl, rr, s -< f +< psi, offset + proof1.size)
      LeftImplies(s, proof1.size + offset - 1, proof1.size + proof2.size + offset - 1, phi, psi) :: (proof2 ++ proof1)
    } else if (left.iffs.nonEmpty) {
      val f = left.iffs.head
      val phi = f.args(0)
      val psi = f.args(1)
      left.updateFormula(f, false)
      left.updateFormula(phi ==> psi, true)
      left.updateFormula(psi ==> phi, true)
      val proof = solveOrganisedSequent(left, right, s -< f +< (phi ==> psi) +< (psi ==> phi), offset)
      LeftIff(s, proof.length - 1 + offset, phi, psi) :: proof
    } else if (left.ands.nonEmpty) {
      val f = left.ands.head
      val phi = f.args(0)
      val psi = f.args(1)
      left.updateFormula(f, false)
      left.updateFormula(phi, true)
      left.updateFormula(psi, true)
      val proof = solveOrganisedSequent(left, right, s -< f +< phi +< psi, offset)
      LeftAnd(s, proof.length - 1 + offset, phi, psi) :: proof

    } else if (left.ors.nonEmpty) {
      val f = left.ors.head
      val phi = f.args(0)
      val psi = f.args(1)

      left.updateFormula(f, false) // gamma
      val rl = left.copy() // sigma
      val rr = right.copy() // pi
      left.updateFormula(phi, true) // delta
      rl.updateFormula(psi, true)
      val proof1 = solveOrganisedSequent(left, right, s -< f +< phi, offset)
      val proof2 = solveOrganisedSequent(rl, rr, s -< f +< psi, offset + proof1.size)
      LeftOr(s, Seq(proof1.size + offset - 1, proof1.size + proof2.size + offset - 1), Seq(phi, psi)) :: (proof2 ++ proof1)
    } else if (right.negs.nonEmpty) {
      val f = right.negs.head
      val phi = f.args.head
      right.updateFormula(f, false)
      left.updateFormula(phi, true)
      val proof = solveOrganisedSequent(left, right, s -> f +< phi, offset)
      RightNot(s, proof.length - 1 + offset, phi) :: proof
    } else if (right.impliess.nonEmpty) {
      val f = right.impliess.head
      val phi = f.args(0)
      val psi = f.args(1)
      left.updateFormula(phi, true)
      right.updateFormula(f, false)
      right.updateFormula(psi, true)
      val proof = solveOrganisedSequent(left, right, s -> f +< phi +> psi, offset)
      RightImplies(s, proof.length - 1 + offset, phi, psi) :: proof
    } else if (right.iffs.nonEmpty) {
      val f = right.iffs.head
      val phi = f.args(0)
      val psi = f.args(1)
      right.updateFormula(f, false) // gamma
      val rl = left.copy() // sigma
      val rr = right.copy() // pi
      right.updateFormula(phi ==> psi, true) // delta
      rr.updateFormula(psi ==> phi, true)
      val proof1 = solveOrganisedSequent(left, right, s -> f +> (phi ==> psi), offset)
      val proof2 = solveOrganisedSequent(rl, rr, s -> f +> (psi ==> phi), offset + proof1.size)
      RightIff(s, proof1.size + offset - 1, proof1.size + proof2.size + offset - 1, phi, psi) :: (proof2 ++ proof1)
    } else if (right.ands.nonEmpty) {
      val f = right.ands.head
      val phi = f.args(0)
      val psi = f.args(1)

      right.updateFormula(f, false) // gamma
      val rl = left.copy() // sigma
      val rr = right.copy() // pi
      right.updateFormula(phi, true) // delta
      rr.updateFormula(psi, true)
      val proof1 = solveOrganisedSequent(left, right, s -> f +> phi, offset)
      val proof2 = solveOrganisedSequent(rl, rr, s -> f +> psi, offset + proof1.size)
      RightAnd(s, Seq(proof1.size + offset - 1, proof1.size + proof2.size + offset - 1), Seq(phi, psi)) :: (proof2 ++ proof1)
    } else if (right.ors.nonEmpty) {
      val f = right.ors.head
      val phi = f.args(0)
      val psi = f.args(1)
      right.updateFormula(f, false)
      right.updateFormula(phi, true)
      right.updateFormula(psi, true)
      val proof = solveOrganisedSequent(left, right, s -> f +> phi +> psi, offset)
      RightOr(s, proof.length - 1 + offset, phi, psi) :: proof

    } else {
      val f = s.left.find(f => s.right.contains(f))
      List(Hypothesis(s, if (f.nonEmpty) f.get else PredicateFormula(VariableFormulaLabel("P"), Seq())))
    }
  }

  def solveSequent(s: Sequent): SCProof = {
    val l = new OrganisedFormulaSet
    s.left.foreach(f => l.updateFormula(f, true))
    val r = new OrganisedFormulaSet
    s.right.foreach(f => r.updateFormula(f, true))
    val r2 = solveOrganisedSequent(l, r, s, 0)
    val r3 = r2.reverse.toVector
    val r4 = SCProof(r3)
    r4
  }

}
