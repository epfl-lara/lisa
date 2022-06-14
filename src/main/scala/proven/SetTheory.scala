package proven

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory
import lisa.settheory.AxiomaticSetTheory.*
import utilities.Helpers.{_, given}

trait SetTheory extends MainLibrary {
  private val x = SchematicFunctionLabel("x", 0)
  private val y = SchematicFunctionLabel("y", 0)
  private val z = SchematicFunctionLabel("z", 0)
  private val x_ = VariableLabel("x")
  private val y_ = VariableLabel("y")
  private val z_ = VariableLabel("z")

  THEOREM("russelParadox") of ("∀x. (x ∈ ?y) ↔ ¬(x ∈ x) ⊢") PROOF {
    val contra = in(y, y) <=> !in(y, y)
    val s0 = Hypothesis(contra |- contra, contra)
    val s1 = LeftForall(forall(x_, in(x_, y) <=> !in(x_, x_)) |- contra, 0, in(x_, y) <=> !in(x_, x_), x_, y)
    val s2 = Rewrite(forall(x_, in(x_, y) <=> !in(x_, x_)) |- (), 1)
    SCProof(s0, s1, s2)
  } using ()

  thm"russelParadox".show()
}

object SetTheory extends SetTheory {}
