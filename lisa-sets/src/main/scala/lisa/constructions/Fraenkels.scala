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

  private def innerComp(c: Variable, filter: (Term**1) |-> Formula, t: Term): BinderFormula = //forall(x, in(x, y) <=> (in(x, t) /\ φ(x)))
    comprehensionSchema.axiom.asInstanceOf[BinderFormula].body.substitute(φ := filter, z := t, y := c).asInstanceOf[BinderFormula]

  //Axiom(exists(y, forall(x, in(x, y) <=> (in(x, z) /\ φ(x)))))

  class Comprehension(_proof: Proof, val t: Term, val filter: (Term**1) |-> Formula, id:Identifier) extends LocalyDefinedVariable(_proof, c => comprehensionSchema)(id) {

    val fullFormula = innerComp(this, filter, t)
    val xb = fullFormula.bound
    
    override lazy val definingFormula: Formula = fullFormula.body //in(xb, this) <=> (in(xb, t) /\ filter(x))
    override val definition: proof.Fact = {
      val a = assume(using proof)(fullFormula)

      InstantiateForall(using SetTheoryLibrary, proof)(xb)(a)(forall(xb, definingFormula) |- definingFormula).validate(summon[sourcecode.Line], summon[sourcecode.File])
    }

    override def toString: String = s"$id{$xb ∈ $t | ${filter(x)}}"
  }


  extension (t:Term) {
    def comprehension(using _proof: Proof, name: sourcecode.Name)(filter: (Term**1) |-> Formula): Comprehension {val proof: _proof.type} = {

      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then
        throw new Exception(s"Name $name is already used in the proof")

      val id = name.value
      val c = Comprehension(_proof, t, filter, id)
      val (compS, compI) = _proof.sequentAndIntOfFact(comprehensionSchema of (φ := filter, z := t, y := c))

      val defin = c.fullFormula
      val definU = defin.underlying
      val exDefinU = K.Exists(c.underlyingLabel, definU)

      _proof.addElimination(defin, (i, sequent) => 
        
        val resSequent = (sequent.underlying -<< definU)
        List(
          SC.LeftExists(resSequent +<< exDefinU, i, definU, c.underlyingLabel),
          SC.Cut(resSequent, compI, i+1, exDefinU)
      ))

      c.asInstanceOf[Comprehension {val proof: _proof.type}]
    }
  }


}
