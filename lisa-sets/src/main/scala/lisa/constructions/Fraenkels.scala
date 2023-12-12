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

  class Comprehension(_proof: Proof, val t: Term, val filter: (Term**1) |-> Formula, id:Identifier) extends LocalyDefinedVariable(_proof, id) {
    given proof.type = proof

    /**
      * forall(x, in(x, y) <=> (in(x, t) /\ φ(x)))
      */
    override val definition: proof.Fact = assume(using proof)(innerComp(this, filter, t))

    val xb = definingFormula.asInstanceOf[BinderFormula].bound

    private val instDef: proof.Fact = {
      InstantiateForall(using SetTheoryLibrary, proof)(xb)(definition)(definingFormula |- definingFormula.asInstanceOf[BinderFormula].body).validate(summon[sourcecode.Line], summon[sourcecode.File])
    }

    /**
      * in(elem, y) <=> (in(elem, t) /\ φ(elem))
      */
    def elim(elem: Term): proof.Fact = instDef of (xb := elem)

    override def toString: String = s"$id{$xb ∈ $t | ${filter(x)}}"
  }


  extension (t:Term) {
    def comprehension(using _proof: Proof, name: sourcecode.Name)(filter: (Term**1) |-> Formula): Comprehension {val proof: _proof.type} = {

      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then
        throw new Exception(s"Name $name is already used in the proof")

      val id = name.value
      val c = Comprehension(_proof, t, filter, id)
      val (compS, compI) = _proof.sequentAndIntOfFact(comprehensionSchema of (φ := filter, z := t, y := c))

      val defin = c.definingFormula
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
