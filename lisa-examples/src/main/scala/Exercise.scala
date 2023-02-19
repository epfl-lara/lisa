import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Printer

object Exercise extends lisa.Main {

  val x = variable
  val P = predicate(1)
  val f = function(1)
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))){
    assume (∀(x, P(x) ==> P(f(x))))
    assume (P(x))
    val step1 = have(P(x) ==> P(f(x))) by InstantiateForall
    val step2 = have(P(f(x)) ==> P(f(f(x)))) by InstantiateForall
    have (P(x) ==> P(f(f(x)))) by Tautology.from(step1, step2)
  }



  /*
  val x = variable
  val y = variable
  val z = variable
  val P = predicate(1)
  val f = function(1)


  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    assume(∀(x, P(x) ==> P(f(x))))
    val base = have((P(x) ==> P(f(x)), P(f(x)) ==> P(f(f(x)))) |- P(x) ==> P(f(f(x)))) by Tautology
    have(P(x) ==> P(f(f(x)))) subproof {
      assume(∀(x, P(x) ==> P(f(x))))
      have(P(f(x)) ==> P(f(f(x))) |- P(x) ==> P(f(f(x)))) by LeftForall(base)
      thenHave(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) by LeftForall
    }
    showCurrentProof()
  }
  show

  val nonEmptySetExists = Lemma(() |- ∃!(x, !(x === ∅) /\ (x === unorderedPair(∅, ∅)))) {
    val subst = have(() |- bot <=> in(∅, ∅)) by Rewrite(emptySetAxiom of (x -> ∅))
    have(in(∅, unorderedPair(∅, ∅)) <=> False |- ()) by Rewrite(pairAxiom of (x -> ∅, y -> ∅, z -> ∅))
    andThen(applySubst(subst))
    thenHave(∀(z, in(z, unorderedPair(∅, ∅)) <=> in(z, ∅)) |- ()) by LeftForall
    andThen(applySubst(extensionalityAxiom of (x -> unorderedPair(∅, ∅), y -> ∅)))
    andThen(applySubst(x === unorderedPair(∅(), ∅())))
    thenHave(() |- !(x === ∅) /\ (x === unorderedPair(∅, ∅)) <=> (x === unorderedPair(∅, ∅))) by Tautology
    thenHave(() |- ∀(x, (x === unorderedPair(∅, ∅)) <=> (!(x === ∅) /\ (x === unorderedPair(∅, ∅))))) by RightForall
    thenHave(() |- ∃(y, ∀(x, (x === y) <=> (!(x === ∅) /\ (x === unorderedPair(∅, ∅)))))) by RightExists
  }
  show

  val nonEmpty = DEF() --> The(x, !(x === ∅()))(nonEmptySetExists)
  show
*/
}
