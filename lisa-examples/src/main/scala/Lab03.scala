import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*


object Lab03 extends lisa.Main{

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  private val z = VariableLabel("z")
  private val f = SchematicFunctionLabel("f", 1)
  private val P = VariableFormulaLabel("P")
  private val Q = SchematicPredicateLabel("Q", 1)
  private val H = SchematicPredicateLabel("R", 2)

  ///////////////////////
  // First Order Logic //
  ///////////////////////


  // you may need to use the following proof tactics:
  // have("_____ |- _____") by Restate
  // have("_____ |- _____") by Trivial
  // have("_____ |- _____") by Weakening     (Restate and Weakening can replace all single-premise Sequent Calculus proof steps. Try them before Trivial.)
  // have("_____ |- _____") by LeftForall(term)(premise)
  // have("_____ |- _____") by RightForall(premise)
  // have("_____ |- _____") by LeftExists(premise)
  // have("_____ |- _____") by RightExists(term)
  // have("_____ |- _____") by InstantiateForall(term*)(premise)
  // have("_____ |- _____") by LeftOr(premise1, premise2)
  // have("_____ |- _____") by LeftImplies(premise1, premise2)
  // have("_____ |- _____") by RightIff(premise1, premise2)
  // have("_____ |- _____") by RightAnd(premise1, premise2)
  //
  // andThen("_____ |- _____") by Tactic    may be use instead of "have" and (premise). In that case, the premise is replaced by the previously proven step.

  //Details about Sequent Calculus in LISA can be found here: https://github.com/epfl-lara/lisa/blob/main/Reference%20Manual/lisa.pdf

  THEOREM("Ex_All_implies_All_Ex") of "∃'x. ∀'y. 'R('x, 'y) ⊢ ∀'x. ∃'y. 'R('x, 'y)" PROOF {
    //TODO
  }

  THEOREM("Unique_Exist_Variant") of "∃'y. ∀'x. ('P('x) ⇔ 'x='y) ⊢ ∃'y. 'P('y) ∧ (∀'x. 'P(x) ⇒ 'x='y)" PROOF {
    //TODO
  }




  ////////////////
  // Set Theory //
  ////////////////

  THEOREM("Subset_Reflexivity") of " ⊢ subset_of('x, 'x)" PROOF {
    val subs = have(subsetAxiom) //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x = 'y
    showCurrentProof() //shows the current sequent calculus proof
    val r1 = andThen(() |- forall(z, in(z, x) ==> in(z, x)) <=> subset(x, x)) by InstantiateForall(x, x)    //InstantiateForall will instantiate a universally bound formula on the right of a sequent with the given terms.
    have(() |- in(z, x) ==> in(z, x)) by Restate                                                            //Restate solves automatically a class of easy proposition, including reflexivity of equality, alpha-equivalence of formulas, and some propositional logic properties
    andThen(() |- forall(z, in(z, x) ==> in(z, x))) by RightForall
    andThen(applySubst(forall(z, in(z, x) ==> in(z, x)) <=> subset(x, x)))                                  //applySubst will replace  occurences of the left-hand-side of the equivalence given in argument by the right-hand-side in the current sequent.
    Discharge(r1)                                                                                           //Discharge removes the formula proven on the right of sequent r1 from the left-hand-side of the current sequent
  }

  THEOREM("Subset_Transitivity") of "subset_of('x, 'y); subset_of('y, 'z) ⊢ subset_of('x, 'z)" PROOF {
    val subs = have(subsetAxiom)           //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x = 'y
    //TODO
  }

  THEOREM("Subset_Antisymmetry") of "subset_of('x, 'y); subset_of('y, 'x)  ⊢ x=y " PROOF {
    val ext = have(extensionalityAxiom)    //  ⊢ ∀'x. ∀'y. 'x ⊆ 'y ⇔ (∀'z. 'z ∊ 'x ⇒ 'z ∊ 'y)
    val subs = have(subsetAxiom)           //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x = 'y
    //TODO
  }


}
