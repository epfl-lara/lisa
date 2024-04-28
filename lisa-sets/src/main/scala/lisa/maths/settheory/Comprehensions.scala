package lisa.maths.settheory

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.*
import lisa.maths.settheory.functions.functional
import lisa.prooflib.BasicStepTactic.RightForall
import lisa.prooflib.BasicStepTactic.TacticSubproof
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.utils.KernelHelpers.++<<
import lisa.utils.KernelHelpers.+<<
import lisa.utils.KernelHelpers.-<<
import lisa.utils.KernelHelpers.apply
import lisa.utils.{_, given}

// Need to objects until https://github.com/lampepfl/dotty/pull/18647 is fixed.
// See also https://github.com/lampepfl/dotty/issues/18569

object Comprehensions {
  import lisa.fol.FOL.{*, given}
  import lisa.maths.settheory.SetTheory2.{primReplacement, replacement, functionalIsFunctional, onePointRule}
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

  // Comprehension

  /**
   * A Comprehension is a local definition of a set from a base set, a filter and a map. In Set builder notation, it denotes
   * {map(x) | x in A /\ filter(x)}.
   * It is represented by a variable usable locally in the proof. The assumptions corresponding to the definition of that variable are automatically eliminated.
   * To obtain the defining property of the comprehension, use the [[elim]] fact.
   *
   * @param _proof the [[Proof]] in which the comprehension is valid
   * @param t The base set
   * @param filter A filter on elements of the base set
   * @param map A map from elements of the base set to elements of the comprehension
   * @param id The identifier of the variable encoding the comprehension.
   */
  class Comprehension(_proof: Proof, val t: Term, val filter: (Term ** 1) |-> Formula, val map: (Term ** 1) |-> Term, id: Identifier) extends LocalyDefinedVariable(_proof, id) {
    given proof.type = proof

    protected lazy val replacer: (Term ** 2) |-> Formula = lambda((A, B), filter(A) /\ (B === map(A)))

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

    /**
     * `in(elem, B) <=> ∃(x, in(x, A) /\ filter(x) /\ (elem === map(x))`
     * if built with term.map, `in(elem, B) <=> ∃(x, in(x, A) /\ (elem === map(x))`
     * if built with term.filter, `in(elem, B) <=> (in(elem, t) /\ filter(elem))`
     */
    def elim(elem: Term) = instDef of (elem_bound := elem)

    // Add elimination to proof
    {
      val (compS, compI) = proof.sequentAndIntOfFact(mainFact of (A := t))
      val definU = definingFormula.underlying
      val exDefinU = K.BinderFormula(K.Exists, underlyingLabel, definU)
      _proof.addElimination(
        definingFormula,
        (i, sequent) =>
          val resSequent = (sequent.underlying -<< definU)
          List(
            SC.LeftExists(resSequent +<< exDefinU, i, definU, underlyingLabel),
            SC.Cut(resSequent, compI, i + 1, exDefinU)
          )
      )
    }

    def toStringFull: String = s"$id{${map(elem_bound)} | ${elem_bound} ∈ $t /\\ ${filter(elem_bound)}]}"
  }

  // Replacement and Set Builders

  private def innerRepl(c: Variable, replacer: (Term ** 2) |-> Formula, t: Term): BinderFormula = // forall(x, in(x, y) <=> (in(x, t) /\ φ(x)))
    ∀(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y) /\ ∀(z, P(x, z) ==> (z === y)))).substitute(P := replacer, A := t, y := c)

  // Axiom(exists(y, forall(x, in(x, y) <=> (in(x, z) /\ φ(x)))))

  class Replacement(_proof: Proof, val t: Term, val replacer: (Term ** 2) |-> Formula, id: Identifier) extends LocalyDefinedVariable(_proof, id) {
    given proof.type = proof

    override val definition: proof.Fact = assume(using proof)(innerRepl(this, replacer, t))

    val elem_bound = definingFormula.asInstanceOf[BinderFormula].bound

    protected val instDef: proof.Fact = {
      InstantiateForall(using SetTheoryLibrary, proof)(elem_bound)(definition)(definingFormula |- definingFormula.asInstanceOf[BinderFormula].body)
        .validate(summon[sourcecode.Line], summon[sourcecode.File])
    }

    // Add elimination to proof
    {
      val (compS, compI) = proof.sequentAndIntOfFact(replacement of (P := replacer, z := t, y := this))

      val definU = definingFormula.underlying
      val exDefinU = K.BinderFormula(K.Exists, underlyingLabel, definU)

      _proof.addElimination(
        definingFormula,
        (i, sequent) =>

          val resSequent = (sequent.underlying -<< definU)
          List(
            SC.LeftExists(resSequent +<< exDefinU, i, definU, underlyingLabel),
            SC.Cut(resSequent, compI, i + 1, exDefinU)
          )
      )
    }

    /**
     * in(elem, y) <=> ∃(x, in(x, t) /\ replacer(x, y) /\ ∀(z, P(x, z) ==> (z === y))
     */
    def elim(elem: Term): proof.Fact = instDef of (elem_bound := elem)

    def toStringFull: String = s"$id{$elem_bound | ${definition.asInstanceOf[BinderFormula].body.asInstanceOf[AppliedConnector].args(1)}]}"
  }

  extension (t: Term) {
    def replace(using _proof: Proof, name: sourcecode.Name)(replacer: (Term ** 2) |-> Formula): Replacement { val proof: _proof.type } = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then throw new Exception(s"Name $name is already used in the proof")
      val id = name.value
      val c = Replacement(_proof, t, replacer, id)
      c.asInstanceOf[Replacement { val proof: _proof.type }]
    }

    def collect(using _proof: Proof, name: sourcecode.Name)(filter: (Term ** 1) |-> Formula, map: (Term ** 1) |-> Term): Comprehension { val proof: _proof.type } = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then throw new Exception(s"Name $name is already used in the proof")
      val id = name.value
      val c = new Comprehension(_proof, t, filter, map, id)
      c.asInstanceOf[Comprehension { val proof: _proof.type }]
    }

    def map(using _proof: Proof, name: sourcecode.Name)(map: (Term ** 1) |-> Term): Comprehension { val proof: _proof.type } = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then throw new Exception(s"Name $name is already used in the proof")
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
      c.asInstanceOf[Comprehension { val proof: _proof.type }]
    }

    def filter(using _proof: Proof, name: sourcecode.Name)(filter: (Term ** 1) |-> Formula): Comprehension { val proof: _proof.type } = {
      if (_proof.lockedSymbols ++ _proof.possibleGoal.toSet.flatMap(_.allSchematicLabels)).map(_.id.name).contains(name.value) then throw new Exception(s"Name $name is already used in the proof")
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
      c.asInstanceOf[Comprehension { val proof: _proof.type }]
    }

  }

}
