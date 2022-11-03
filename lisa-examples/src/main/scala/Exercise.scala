import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Printer

object Exercise extends lisa.Main {

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  private val z = VariableLabel("z")
  private val f = SchematicFunctionLabel("f", 1)
  private val P = SchematicPredicateLabel("P", 1)
  private val Q = SchematicPredicateLabel("Q", 2)
  private val H = VariableFormulaLabel("H")

  /////////////////////////
  // Propositional Logic //
  /////////////////////////

  THEOREM("double_negation_elim") of "|- 'a ⇔ ¬¬'a" PROOF {
    val hyp = have("'a |- 'a") by Hypothesis

    andThen("|- !'a; 'a") by RightNot
    andThen("!!'a |- 'a") by LeftNot
    val direction1 = andThen("|- !!'a ==> 'a") by RightImplies

    have("'a; !'a |- ") by LeftNot(hyp)
    andThen(("'a |- !!'a")) by RightNot
    val direction2 = andThen("|- !!'a ==> 'a") by RightImplies

    have("|- !!'a <=> 'a") by RightIff(direction1, direction2)
    showCurrentProof()
  }
  show

  /*
  THEOREM("pierce-law") of "|- ((('A ==> 'B) ==> 'A) ==> 'A)" PROOF {
    ???
  }
  show
   */

  ///////////////////////
  // First Order Logic //
  ///////////////////////

  /*
  THEOREM("russel_Paradox") of "∀'x. 'Q('y, 'x) ↔ ¬'Q('x, 'x) ⊢" PROOF {
    have("'Q('y, 'y) <=> !'Q('y, 'y) |- ") by Restate
    andThen("∀'x. 'Q('y, 'x) <=> !'Q('x, 'x) |- ") by LeftForall(y)
  }
  show

  THEOREM("all-comm") of "|- (∀'x. ∀'y. 'Q('x, 'y)) ⇔ (∀'y. ∀'x. 'Q('x, 'y))" PROOF {
    val base = have("'Q('x, 'y) |- 'Q('x, 'y)") by Hypothesis

    andThen ("∀'y. 'Q('x, 'y) |- 'Q('x, 'y)") by LeftForall(y)
    andThen ("∀'x. ∀'y. 'Q('x, 'y) |- 'Q('x, 'y)") by LeftForall(x)
    andThen ("∀'x. ∀'y. 'Q('x, 'y) |- ∀'x. 'Q('x, 'y)") by RightForall()
    andThen ("∀'x. ∀'y. 'Q('x, 'y) |- ∀'y. ∀'x. 'Q('x, 'y)") by RightForall()
    val direction1 = andThen ("|- (∀'x. ∀'y. 'Q('x, 'y)) ==> (∀'y. ∀'x. 'Q('x, 'y))") by Restate

    have ("∀'x. 'Q('x, 'y) |- 'Q('x, 'y)") by LeftForall(x)(base)
    andThen ("∀'y. ∀'x. 'Q('x, 'y) |- 'Q('x, 'y)") by LeftForall(y)
    andThen ("∀'y. ∀'x. 'Q('x, 'y) |- ∀'y. 'Q('x, 'y)") by RightForall()
    andThen ("∀'y. ∀'x. 'Q('x, 'y) |- ∀'x. ∀'y. 'Q('x, 'y)") by RightForall()
    val direction2 = andThen ("|- (∀'y. ∀'x. 'Q('x, 'y)) ==> (∀'x. ∀'y. 'Q('x, 'y))") by Restate
    have ("|- (∀'x. ∀'y. 'Q('x, 'y)) <=> (∀'y. ∀'x. 'Q('x, 'y))") by RightIff(direction1, direction2)
  }
  show
   */

  /*
  THEOREM("fixed_Point_Double_Application") of "∀'x. 'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('f('x)))" PROOF {
    ???
  }
  show
   */

}
