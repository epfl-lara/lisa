package lisa.constructions

import lisa.SetTheoryLibrary.*
import lisa.fol.FOL.{*, given}
import lisa.utils.KernelHelpers.{apply, -<<, +<<, ++<<}
import lisa.SetTheoryLibrary
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.utils.{_, given}


object Fraenkels {
  private val x = variable 
  private val y = variable 
  private val z = variable
  private val φ = predicate[1]

  private def innerComp(c: Variable, filter: (Term**1) |-> Formula, t: Term): Formula = //forall(x, in(x, y) <=> (in(x, t) /\ φ(x)))
    comprehensionSchema.asInstanceOf[BinderFormula].body.substitute(φ := filter, z := t, y := c)

  //Axiom(exists(y, forall(x, in(x, y) <=> (in(x, z) /\ φ(x)))))

  class Comprehension(_proof: Proof, val t: Term, val filter: (Term**1) |-> Formula, id:Identifier) extends LocalyDefinedVariable(_proof, c => comprehensionSchema)(id) {
    
    override val definingFormula: Formula = in(x, this) <=> (in(x, t) /\ filter(x))
    override val definition: proof.Fact = {
      val a = assume(using proof)(innerComp(this, filter, t))

      InstantiateForall(using SetTheoryLibrary, proof)(definingFormula, x)(a)(forall(x, definingFormula) |- definingFormula).validate(summon[sourcecode.Line], summon[sourcecode.File])
    }

    override def toString: String = s"$id{$x ∈ $t | ${filter(x)}}"
  }


  extension (t:Term) {
    def comprehension(using _proof: Proof)(filter: (Term**1) |-> Formula): LocalyDefinedVariable = {

      val id = freshId((filter.allSchematicLabels ++ t.allSchematicLabels ++ _proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id), "Zc")

      val c = Comprehension(_proof, t, filter, id)

      val defin = c.definingFormula
      val definU = defin.underlying
      val exDefinU = K.Exists(c.underlyingLabel, definU)

      _proof.addElimination(defin, (i, sequent) => 
        val (compS, compI) = _proof.sequentAndIntOfFact(comprehensionSchema)
        val resSequent = (sequent.underlying -<< definU)
        List(
          SC.LeftExists(resSequent +<< exDefinU, i, definU, c.underlyingLabel),
          SC.Cut(resSequent, compI, i+1, exDefinU)
      ))

      c.asInstanceOf[Comprehension {val proof: _proof.type}]
    }
  }


}
