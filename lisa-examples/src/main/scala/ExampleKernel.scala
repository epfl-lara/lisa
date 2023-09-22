import lisa.utils.K

import K.*

/**
 * Discover some of the elements of the logical kernel of LISA.
 */
object ExampleKernel {

  import lisa.kernel.proof.SequentCalculus.*

  def main(args: Array[String]): Unit = {
    val phi = formulaVariable()
    val psi = formulaVariable()
    val PierceLaw = SCProof(
      Hypothesis(phi |- phi, phi),
      Weakening(phi |- (phi, psi), 0),
      RightImplies(() |- (phi, phi ==> psi), 1, phi, psi),
      LeftImplies((phi ==> psi) ==> phi |- phi, 2, 0, (phi ==> psi), phi),
      RightImplies(() |- ((phi ==> psi) ==> phi) ==> phi, 3, (phi ==> psi) ==> phi, phi)
    )
    val PierceLaw2 = SCProof(
      RestateTrue(() |- ((phi ==> psi) ==> phi) ==> phi)
    )

    checkProof(PierceLaw, println)
    checkProof(PierceLaw2, println)

    val theory = new RunningTheory
    val pierceThm: theory.Theorem = theory.makeTheorem("Pierce's Law", () |- ((phi ==> psi) ==> phi) ==> phi, PierceLaw, Seq.empty).get
  }

}
