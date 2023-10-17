

object Lab04  extends lisa.Main {

    /*
    You may use the following tactics: 
        - Restate              | "Trivially" true Sequent. Deals with alpha equivalence and most propositional rules but not distributivity
        - Weakening            | "Trivially" weaker sequent (than the previous one).
        - Tautology.from       | Anything that can be solved by propositional reasoning alone

        - LeftForall           | To introduce a ∀ quantifier in an assumption
        - LeftExists           | To introduce a ∃ quantifier in an assumption (the variable must not be free somewhere else)
        - RightForall          | To introduce a ∀ quantifier in the conclusion (the variable must not be free somewhere else)
        - RightExists          | To introduce a ∃ quantifier in the conclusion
        - InstantiateForall    | To obtain a formula of the form P(t) from a quantified assumption ∀(x, P(x))



        thm1 and thm2 illustrate how those tactics can be used, as well as the usage of "assume", "have", "thenHave", "by", "thesis", "of" and "subproof".
    */

    val x = variable
    val y = variable
    val z = variable
    val f = function[1]
    val P = formulaVariable
    val Q = predicate[1]
    val R = predicate[1]
    val S = predicate[2]





    //A standard theorem about reordering quantifiers. Does the converse hold?
    val thm1 = Theorem( ∃(x, ∀(y, S(x, y))) |-  ∀(y, ∃(x, S(x, y))) ) {
        have(S(x, y) |- S(x, y)) by Restate
        thenHave(∀(y, S(x, y)) |-  S(x, y)) by LeftForall
        thenHave(∀(y, S(x, y)) |-  ∃(x, S(x, y))) by RightExists
        thenHave(∃(x, ∀(y, S(x, y))) |-  ∃(x, S(x, y))) by LeftExists
        thenHave(∃(x, ∀(y, S(x, y))) |-  ∀(y, ∃(x, S(x, y)))) by RightForall
    }

    //A standard and important property of ∀: It distributes over conjunction. This is useful to justify prenex normal form.
    val thm2 = Theorem ( (∀(x,  Q(x)) /\ ∀ (x, R(x))) <=> ∀(x, Q(x) /\ R(x)) ) {

        //Here we prove the two directions of <=> separately and then combine them.
        val forward = have((∀(x,  Q(x)), ∀ (x, R(x))) |- ∀(x, Q(x) /\ R(x))) subproof {
            have((Q(x), R(x)) |- Q(x) /\ R(x)) by Restate
            thenHave((∀(x,  Q(x)), R(x)) |- Q(x) /\ R(x)) by LeftForall
            thenHave((∀(x,  Q(x)), ∀ (x, R(x))) |- Q(x) /\ R(x)) by LeftForall
            thenHave(thesis) by RightForall
        }

        //The second direction
        val backward = have( ∀(x, Q(x) /\ R(x)) |- ∀(x,  Q(x)) /\ ∀ (x, R(x))) subproof {
            assume(∀(x, Q(x) /\ R(x)))
            val assump = have(Q(x) /\ R(x)) by InstantiateForall
            have(Q(x)) by Weakening(assump)
            val conj1 = thenHave(∀(x, Q(x))) by RightForall
            have(R(x)) by Weakening(assump)
            val conj2 = thenHave(∀(x, R(x))) by RightForall
            have(thesis) by Tautology.from(conj1, conj2)
        }

        have(thesis) by Tautology.from(forward, backward)
    }

    // This theorem requires instantiating the assumption twice, once with x and once with f(x), and then combine the two. 
    // Since x is free is the sequent step1, then step 1 is true with anything substituted for x.
    // We can do such substitution with the "of" keyword.
    // Specifically, `step1 of (x := f(x))` proves the formula P(f(x)) ==> P(f(f(x)))
    val thm3 = Theorem(∀(x, Q(x) ==> Q(f(x))) |- Q(x) ==> Q(f(f(x)))) {
      assume(∀(x, Q(x) ==> Q(f(x))))
      val step1 = have(Q(x) ==> Q(f(x))) by InstantiateForall
      have(thesis) by Tautology.from(step1, step1 of (x := f(x)))
    } 


    //////////////////////////////////
    // Prove the following theorems //
    //////////////////////////////////


    // This Theorem should be straightforward: You simply need to apply the ∀ and the ∃ quantifiers in the good order.
    val thm4 = Theorem( (∀(x, Q(x) ==> P), ∃(x, Q(x))) |- P ) {
        ???
    }

    // This theorem is also short. 
    val thm5 = Theorem( ! ∀(x, Q(x)) |- ∃(x, !Q(x)) ) {
        ???
    }

    // Quantifiers are not very nice to use.
    // The following theorem, called Russel's Paradox in Set theory, is equivalent to |- !∃(x, ∀(y, (y ∈ x) <=> !(y ∈ y)))
    // If we can, we prefer to avoid using the top level quantifier! Here x is a free parameter: The sequent is true for any term substituted for x.
    val thm6 = Theorem( ∀(y, (y ∈ x) <=> !(y ∈ y)) |- () ) {
        ???
    }

    //Again, free variables in a sequent are implicitly universaly quantified: The statement hold with any term substituted for x.
    val thm7 = Theorem( (Q(x), R(x)) |- ∃(y, Q(y)) /\ ∃(y, R(y)) )  {
        ???
    }

    // This theorem is a bit more involved
    val thm8 = Theorem( ∃(y, ∀(x, Q(y) ==> Q(x) )) ) {
        ???
    }




    // This theorem is more complex. it says that "If all poor person have a rich father, then there is a rich person with a rich grandfather".
    // If you're stuck, make sure to first prove the statement with pen and paper.
    val father = function[1]
    val rich = predicate[1]

    val richGrandfather = Theorem(∀(x, !rich(x) ==> rich(father(x))) |- ∃(x, rich(x) /\ rich(father(father(x)))) ) {
        ???
    }




}