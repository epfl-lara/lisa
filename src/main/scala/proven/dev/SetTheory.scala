package proven.dev

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory
import lisa.settheory.AxiomaticSetTheory.*
import proven.DSetTheory.Part1.{russelParadox, theory}
import utilities.KernelHelpers.{*, given}
import lisa.kernel.proof.RunningTheory

trait SetTheory extends MainLibrary{
  /*
  private val x = SchematicFunctionLabel("x", 0)
  private val y = SchematicFunctionLabel("y", 0)
  private val z = SchematicFunctionLabel("z", 0)
  private val x1 = VariableLabel("x")
  private val y1 = VariableLabel("y")
  private val z1 = VariableLabel("z")
  private val f = SchematicFunctionLabel("f", 0)
  private val g = SchematicFunctionLabel("g", 0)
  private val h = SchematicPredicateLabel("h", 0)
  */

  private val `s?` = "sd"

  given Conversion[SchematicFunctionLabel, Term] with
    def apply(s: SchematicFunctionLabel): Term = s.apply()



  val russelParadox: SCProof = {
    val contra = (in(?y, ?y)) <=> !(in(?y, ?y))
    val s0 = Hypothesis(contra |- contra, contra)
    val s1 = LeftForall(forall(x, in(x, ?y) <=> !in(x, x)) |- contra, 0, in(x, ?y) <=> !in(x, x), x, ?y)
    val s2 = Rewrite(forall(x, in(x, ?y) <=> !in(x, x)) |- (), 1)
    SCProof(s0, s1, s2)
  }
  theorem("russelParadox", "∀x. (x ∈ ?y) ↔ ¬(x ∈ x) ⊢", russelParadox, Nil).get

}
