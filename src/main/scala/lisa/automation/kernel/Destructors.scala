package lisa.automation.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.automation.kernel.ProofTactics.hypothesis
import lisa.utils.Helpers.*

object Destructors {
  def destructRightOr(p: SCProof, a: Formula, b: Formula): SCProof = {
    val mat = p.conclusion.right.find(f => isSame(f, a \/ b))
    require(mat.nonEmpty)
    val p0 = hypothesis(a)
    val p1 = hypothesis(b)
    val p2 = LeftOr(emptySeq +< (a \/ b) +> a +> b, Seq(p.length, p.length + 1), Seq(a, b))
    val p3 = Cut(p.conclusion -> mat.get +> a +> b, p.length - 1, p.length + 2, a \/ b)
    p withNewSteps IndexedSeq(p0, p1, p2, p3)
  }

  def destructRightAnd(p: SCProof, f: Formula, g: Formula): SCProof = {
    val p0 = hypothesis(f) // n
    val p1 = LeftAnd(emptySeq +< (f /\ g) +> f, p.length, f, g) // n+1
    val p2 = Cut(p.conclusion -> (f /\ g) -> (g /\ f) +> f, p.length - 1, p.length + 1, f /\ g)
    p withNewSteps IndexedSeq(p0, p1, p2)
  }

  def destructRightImplies(p: SCProof, f: Formula, g: Formula): SCProof = { //   |- f=>g
    val p0 = hypothesis(f) //   f |- f
    val p1 = hypothesis(g) //   g |- g
    val p2 = LeftImplies(emptySeq +< f +< (f ==> g) +> g, p.length, p.length + 1, f, g) //  f, f=>g |- g
    val p3 = Cut(p.conclusion -> (f ==> g) +< f +> g, p.length - 1, p.length + 2, f ==> g) //  f|- g
    p withNewSteps IndexedSeq(p0, p1, p2, p3)
  }
}
