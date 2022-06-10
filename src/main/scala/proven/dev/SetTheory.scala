package proven.dev

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory
import lisa.settheory.AxiomaticSetTheory.*
import proven.DSetTheory.Part1.{russelParadox, theory}
import utilities.KernelHelpers.{*, given}
import utilities.TheoriesHelpers.{*, given}

trait SetTheory extends MainLibrary{
  private val x = SchematicFunctionLabel("x", 0)
  private val y = SchematicFunctionLabel("y", 0)
  private val z = SchematicFunctionLabel("z", 0)
  private val x1 = VariableLabel("x")
  private val y1 = VariableLabel("y")
  private val z1 = VariableLabel("z")
  private val f = SchematicFunctionLabel("f", 0)
  private val g = SchematicFunctionLabel("g", 0)
  private val h = SchematicPredicateLabel("h", 0)

  given Conversion[SchematicFunctionLabel, Term] with
    def apply(s: SchematicFunctionLabel): Term = s()

  /**
   */
  val russelParadox: SCProof = {
    val contra = (in(y, y)) <=> !(in(y, y))
    val s0 = Hypothesis(contra |- contra, contra)
    val s1 = LeftForall(forall(x1, in(x1, y) <=> !in(x1, x1)) |- contra, 0, in(x1, y) <=> !in(x1, x1), x1, y)
    val s2 = Rewrite(forall(x1, in(x1, y) <=> !in(x1, x1)) |- (), 1)
    SCProof(s0, s1, s2)
  }
  import AxiomaticSetTheory.runningSetTheory.*
  theorem(AxiomaticSetTheory.runningSetTheory)("russelParadox", "∀x. (x ∈ ?y) ↔ ¬(x ∈ x) ⊢", russelParadox, Nil).get
}
