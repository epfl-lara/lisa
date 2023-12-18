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
  import lisa.maths.settheory.SetTheory.*
  import Fraenkels.*


  private val s = variable
  private val x = variable
  private val x_1 = variable
  private val y = variable
  private val z = variable
  private val f = function[1]
  private val t = variable
  private val A = variable
  private val B = variable
  private val C = variable
  private val P = predicate[2]
  private val Q = predicate[1]
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

  val onePointRule = Theorem(
    ∃(x, (x===y) /\ Q(x)) <=> Q(y)
  ) {
    val s1 = have(∃(x, (x===y) /\ Q(x)) ==> Q(y)) subproof {
      assume(∃(x, (x===y) /\ Q(x)))
      val ex = pick(lastStep)
      val s1 = have(Q(ex)) by Tautology.from(ex.definition)
      val s2 = have(ex === y) by Tautology.from(ex.definition)
      have(Q(y)) by Substitution.ApplyRules(s2)(s1)
    }
    val s2 = have(Q(y) ==> ∃(x, (x===y) /\ Q(x))) subproof{
      assume(Q(y))
      thenHave((y === y) /\ Q(y)) by Restate
      thenHave(∃(x, (x===y) /\ Q(x))) by RightExists
      thenHave(thesis) by Restate.from
    }
    have(thesis) by Tautology.from(s1, s2)
  }


  val singletonMap = Lemma(
    ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1))) <=> (x === f(∅))
  ) {
    val s1 = have(∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1))) ==> (x === f(∅))) subproof {
      have(x === f(∅) |- x === f(∅)) by Restate
      thenHave((x_1 === ∅, x === f(x_1)) |- x === f(∅)) by Substitution.ApplyRules(x_1 === ∅)
      thenHave((x_1 === ∅) /\ (x === f(x_1)) |- x === f(∅)) by Restate
      thenHave((in(x_1, singleton(∅))) /\ ((x === f(x_1))) |- x === f(∅)) by Substitution.ApplyRules(singletonHasNoExtraElements of (y := x_1, x := ∅))
      thenHave(∃(x_1, in(x_1, singleton(∅)) /\ ((x === f(x_1)))) |- x === f(∅)) by LeftExists

    } 

    val s2 = have( (x === f(∅)) ==> ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1)))) subproof {
      have(x === f(∅) |- (∅ === ∅) /\ (x === f(∅))) by Restate
      thenHave(x === f(∅) |- in(∅, singleton(∅)) /\ (x === f(∅))) by Substitution.ApplyRules(singletonHasNoExtraElements of (y := x_1, x := ∅))
      thenHave(x === f(∅) |- ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1)))) by RightExists
      thenHave(thesis) by Restate.from

    }

    have(thesis) by Tautology.from(s1, s2)
  }


  val testCollector = Theorem(
    ∃(s, ∀(x, in(x, s) <=> (x === f(∅))))
  ) {
    val r = singleton(∅).collect(lambda(x, top), f)

    have(in(x, r) <=> (x === f(∅))) by Substitution.ApplyRules(singletonMap)(r.elim(x))
    thenHave(∀(x, in(x, r) <=> (x === f(∅)))) by RightForall
    thenHave(thesis) by RightExists
  }


  val testMap = Theorem(
    ∃(s, ∀(x, in(x, s) <=> (x === f(∅))))
  ) {
    val r = singleton(∅).map(f)
    have(in(x, r) <=> (x === f(∅))) by Substitution.ApplyRules(singletonMap)(r.elim(x))
    thenHave(∀(x, in(x, r) <=> (x === f(∅)))) by RightForall
    thenHave(thesis) by RightExists
  }

  val testFilter = Theorem(
    ∃(x, Q(x)) |- ∃(z, ∀(t, in(t, z) <=> ∀(y, Q(y) ==> in(t, y))))
  ) {
    val s1 = assume(∃(x_1, Q(x_1)))
    val x = pick(s1)
    val z = x.filter(lambda(t, ∀(y, Q(y) ==> in(t, y))))
    have(∀(y, Q(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, Q(y) ==> in(t, y)))) by Tableau
    have( in(t, z) <=> ∀(y, Q(y) ==> in(t, y)) ) by Substitution.ApplyRules(lastStep)(z.elim(t))
    thenHave( ∀(t, in(t, z) <=> ∀(y, Q(y) ==> in(t, y))) ) by RightForall
    thenHave(thesis) by RightExists

    /*
    have(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ φ(t))))) by InstFunSchema(Map(z -> x))(comprehensionSchema)
    val conjunction = thenHave(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) by InstPredSchema(Map(φ -> lambda(t, ∀(y, P(y) ==> in(t, y)))))

    have(∀(y, P(y) ==> in(t, y)) |- ∀(y, P(y) ==> in(t, y))) by Hypothesis
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- ∀(y, P(y) ==> in(t, y))) by Weakening
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- P(x) ==> in(t, x)) by InstantiateForall(x)
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- in(t, x) /\ ∀(y, P(y) ==> in(t, y))) by Tautology
    val fwd = thenHave(P(x) |- ∀(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Restate

    have((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) |- (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Hypothesis
    val bwd = thenHave((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) ==> (∀(y, P(y) ==> in(t, y)))) by Restate

    val lhs = have(P(x) |- ∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by RightIff(fwd, bwd)

    val form = formulaVariable
    have((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) |- in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Hypothesis
    val rhs = thenHave(
      Set((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))), (∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- (in(t, z) <=> (∀(y, P(y) ==> in(t, y))))
    ) by RightSubstIff(List((∀(y, P(y) ==> in(t, y)), (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))

    have((P(x), (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by Cut(lhs, rhs)
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by LeftForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y))))) by RightForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by RightExists
    val cutRhs = thenHave((P(x), ∃(z, ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists

    have(P(x) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by Cut(conjunction, cutRhs)
    thenHave(∃(x, P(x)) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists
    */

  }


  //Cantor's Theorem with filter

}

object Fraenkels {
  import lisa.fol.FOL.{*, given}
  import FraenkelsThm.{primReplacement, replacement, functionalIsFunctional, onePointRule}
  import lisa.automation.Tautology 
  import lisa.automation.Substitution
  private val x = variable 
  private val y = variable 
  private val z = variable
  private val A = variable
  private val B = variable
  private val C = variable
  private val P = predicate[2]
  private val Q = predicate[1]
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
      val s = have(thesis) by Tautology.from(primReplacement of (P := replacer), functionalIsFunctional of (Filter := filter, Map := map))
    }

    /**
      * forall(y, in(y, B) <=> ∃(x, in(x, A) /\ filter(x) /\ (y === map(x))
      */
    override val definition: proof.Fact = assume(using proof)(forall(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y))).substitute(P := replacer, A := t, B := this))

    val elem_bound = definingFormula.asInstanceOf[BinderFormula].bound

    
    protected val instDef: proof.Fact = {
      have(definingFormula |- definingFormula.asInstanceOf[BinderFormula].body) by InstantiateForall(using SetTheoryLibrary, proof)(elem_bound)(definition)
    }

    def elim(elem: Term) = instDef of (elem_bound := elem)

    //Add elimination to proof
    {
      val (compS, compI) = proof.sequentAndIntOfFact(mainFact of (A := t))
      val definU = definingFormula.underlying
      val exDefinU = K.BinderFormula(K.Exists, underlyingLabel, definU)
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

    protected val instDef: proof.Fact = {
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
      inline def _t = t
      val c = new Comprehension(_proof, t, lambda(x, top), map, id) {

        override val instDef: proof.Fact = {
          val elim_formula = (forall(elem_bound, in(elem_bound, B) <=> ∃(x, in(x, A) /\ P(x, elem_bound))).substitute(P := lambda((A, B), B === _map(A)), A := _t, B := this)).body

          have(TacticSubproof(using proof) { 
            val s = have(definingFormula |- definingFormula.asInstanceOf[BinderFormula].body) by InstantiateForall(elem_bound)(definition)
            thenHave(definingFormula |- elim_formula) by Restate.from
          })
          
            
        }
      }
      c.asInstanceOf[Comprehension {val proof: _proof.type}]
    }

    def filter(using _proof: Proof, name: sourcecode.Name)(filter: (Term**1) |-> Formula): Comprehension {val proof: _proof.type} = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then
        throw new Exception(s"Name $name is already used in the proof")
      val id = name.value
      inline def _filter = filter
      inline def _t = t
      val c = new Comprehension(_proof, t, filter, lambda(x, x), id) {

        override val instDef: proof.Fact = {
          have(TacticSubproof(using proof) {
            val ex = new Variable(freshId(definingFormula.allSchematicLabels.map(_.id), "x"))
            have(definingFormula |- definingFormula.asInstanceOf[BinderFormula].body) by InstantiateForall(elem_bound)(definition)
            have(in(elem_bound, this) <=> ∃(ex, (ex === elem_bound) /\ in(ex, _t) /\ _filter(ex))) by Tautology.from(lastStep)
            thenHave(in(elem_bound, this) <=> (in(elem_bound, _t) /\ _filter(elem_bound))) by Substitution.ApplyRules(onePointRule of (y := elem_bound, Q := lambda(ex, in(ex, _t) /\ _filter(ex))))
          })
        }

      }
      c.asInstanceOf[Comprehension {val proof: _proof.type}]
    }


  }




}
