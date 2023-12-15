package lisa.settheory

import lisa.SetTheoryLibrary.*
import lisa.utils.KernelHelpers.{apply, -<<, +<<, ++<<}
import lisa.SetTheoryLibrary
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.utils.{_, given}
import lisa.prooflib.BasicStepTactic.TacticSubproof
import lisa.prooflib.BasicStepTactic.RightForall
import lisa.maths.settheory.SetTheory.functional

// Need to objects until https://github.com/lampepfl/dotty/pull/18647 is fixed. 
// See also https://github.com/lampepfl/dotty/issues/18569


object FraenkelsThm extends lisa.Main {

  private val x = variable
  private val y = variable
  private val z = variable
  private val A = variable
  private val B = variable
  private val C = variable
  private val P = predicate[2]
  private val Filter = predicate[1]
  private val Map = function[1]

  val primReplacement = Theorem(
    ∀(x, in(x, A) ==> ∀(y, ∀(z, (P(x, y) /\ P(x, z)) ==> (y === z)))) |-
    ∃(B, forall(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y))))
  ){
    have(thesis) by Restate.from(replacementSchema of (A := A, x := x, P := P))
  }



  val manyForall = Lemma (
    ∀(x, in(x, A) ==> ∀(y, ∀(z, (P(x, y) /\ P(x, z)) ==> (y === z)))).substitute(P := lambda((A, B), P(A, B) /\ ∀(C, P(A, C) ==> (B === C)) )) <=> top
  ) {
    have(thesis) by Tableau
  }

  val functionalIsFunctional = Lemma (
    ∀(x, in(x, A) ==> ∀(y, ∀(z, (P(x, y) /\ P(x, z)) ==> (y === z)))).substitute(P := lambda((A, B), Filter(A) /\ (B === Map(A)) )) <=> top
  ){

    have(y === Map(x) |- (y === Map(x))) by Restate
    thenHave((y === Map(x), z === Map(x)) |- y === z) by Substitution.ApplyRules(Map(x) === z)
    thenHave(in(x, A) |- ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z))) by Weakening
    thenHave(in(x, A) |- ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z)))) by RightForall
    thenHave(in(x, A) |- ∀(y, ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z))))) by RightForall
    thenHave(in(x, A) ==> ∀(y, ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z))))) by Restate
    thenHave(∀(x, in(x, A) ==> ∀(y, ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z)))))) by RightForall
    thenHave(thesis) by Restate

  }

  /**
    * Theorem --- the refined replacement axiom. Easier to use as a rule than primReplacement.
    */
  val replacement = Theorem(
    ∃(B, ∀(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y) /\ ∀(z, P(x, z) ==> (z === y)))))
  ) {
    have(thesis) by Tautology.from(manyForall, primReplacement of (P := lambda((A, B), P(A, B) /\ ∀(C, P(A, C) ==> (B === C)) )))
  }

}

object Fraenkels {
  import lisa.fol.FOL.{*, given}
  import FraenkelsThm.{primReplacement, replacement, functionalIsFunctional}
  import lisa.automation.Tautology 
  private val x = variable 
  private val y = variable 
  private val z = variable
  private val A = variable
  private val B = variable
  private val C = variable
  private val P = predicate[2]
  private val Filter = predicate[1]
  private val Map = function[1]

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary


  //Comprehension

  class Comprehension(_proof: Proof, val t: Term, val filter: (Term**1) |-> Formula, val map: (Term**1) |-> Term, id:Identifier) extends LocalyDefinedVariable(_proof, id) {
    given proof.type = proof

    protected lazy val replacer: (Term**2) |-> Formula = lambda((A, B), filter(A) /\ (B === map(A)))

    
    private val mainFact = have(
      ∃(B, ∀(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y)))).substitute(P := replacer)
    ) subproof {
      have(thesis) by Tautology.from(primReplacement of (P := replacer), functionalIsFunctional of (Filter := filter, Map := map))
    }
    

    /**
      * forall(y, in(y, B) <=> ∃(x, in(x, A) /\ filter(x) /\ (y === map(x))
      */
    override val definition: proof.Fact = assume(using proof)(forall(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y))).substitute(P := replacer, A := t, B := this))

    val elem_bound = definingFormula.asInstanceOf[BinderFormula].bound

    
    private val instDef: proof.Fact = {
      InstantiateForall(using SetTheoryLibrary, proof)(elem_bound)(definition)(
        definingFormula |- definingFormula.asInstanceOf[BinderFormula].body).validate(summon[sourcecode.Line], summon[sourcecode.File])
    }

    def elim(elem: Term) = instDef of (elem_bound := elem)

    //Add elimination to proof
    {
      val (compS, compI) = proof.sequentAndIntOfFact(mainFact of (A := t))

      val definU = definingFormula.underlying
      val exDefinU = K.BinderFormula(K.Exists, underlyingLabel, definU)


      println(compS)
      println(lisa.utils.parsing.FOLPrinter.prettyFormula(exDefinU))

      _proof.addElimination(definingFormula, (i, sequent) => 
        
        val resSequent = (sequent.underlying -<< definU)
        List(
          SC.LeftExists(resSequent +<< exDefinU, i, definU, underlyingLabel),
          SC.Cut(resSequent, compI, i+1, exDefinU)
      ))
    }
  }



  // Replacement and Set Builders

  private def innerRepl(c: Variable, replacer: (Term**2) |-> Formula, t: Term): BinderFormula = //forall(x, in(x, y) <=> (in(x, t) /\ φ(x)))
    ∀(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y) /\ ∀(z, P(x, z) ==> (z === y)))).substitute(P := replacer, A := t, y := c)

  //Axiom(exists(y, forall(x, in(x, y) <=> (in(x, z) /\ φ(x)))))

  class Replacement(_proof: Proof, val t: Term, val replacer: (Term**2) |-> Formula, id:Identifier) extends LocalyDefinedVariable(_proof, id) {
    given proof.type = proof

    /**
      * forall(x, in(x, y) <=> (in(x, t) /\ φ(x)))
      */
    override val definition: proof.Fact = assume(using proof)(innerRepl(this, replacer, t))

    val elem_bound = definingFormula.asInstanceOf[BinderFormula].bound

    private val instDef: proof.Fact = {
      InstantiateForall(using SetTheoryLibrary, proof)(elem_bound)(definition)(definingFormula |- definingFormula.asInstanceOf[BinderFormula].body).validate(summon[sourcecode.Line], summon[sourcecode.File])
    }


    //Add elimination to proof
    {
      val (compS, compI) = proof.sequentAndIntOfFact(replacement of (P := replacer, z := t, y := this))

      val definU = definingFormula.underlying
      val exDefinU = K.BinderFormula(K.Exists, underlyingLabel, definU)

      _proof.addElimination(definingFormula, (i, sequent) => 
        
        val resSequent = (sequent.underlying -<< definU)
        List(
          SC.LeftExists(resSequent +<< exDefinU, i, definU, underlyingLabel),
          SC.Cut(resSequent, compI, i+1, exDefinU)
      ))
    }


    /**
      * in(elem, y) <=> (in(elem, t) /\ φ(elem))
      */
    def elim(elem: Term): proof.Fact = instDef of (elem_bound := elem)

    override def toString: String = s"$id{$elem_bound | ${ definition.asInstanceOf[BinderFormula].body.asInstanceOf[AppliedConnector].args(1) }]}"
  }




  extension (t:Term) {
    def replace(using _proof: Proof, name: sourcecode.Name)(replacer: (Term**2) |-> Formula): Replacement {val proof: _proof.type} = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then
        throw new Exception(s"Name $name is already used in the proof")
      val id = name.value
      val c = Replacement(_proof, t, replacer, id)
      c.asInstanceOf[Replacement {val proof: _proof.type}]
    }

    def collect(using _proof: Proof, name: sourcecode.Name)(filter: (Term**1) |-> Formula, map: (Term**1) |-> Term): Comprehension {val proof: _proof.type} = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then
        throw new Exception(s"Name $name is already used in the proof")
      val id = name.value
      val c = new Comprehension(_proof, t, filter, map, id) 
      c.asInstanceOf[Comprehension {val proof: _proof.type}]
    }

    def map(using _proof: Proof, name: sourcecode.Name)(map: (Term**1) |-> Term): Comprehension {val proof: _proof.type} = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then
        throw new Exception(s"Name $name is already used in the proof")
      val id = name.value
      inline def _map = map
      val c = new Comprehension(_proof, t, lambda(x, top), map, id) {
        override lazy val replacer: (Term**2) |-> Formula = lambda((A, B), B === _map(A))
      }
      c.asInstanceOf[Comprehension {val proof: _proof.type}]
    }

  }




}
