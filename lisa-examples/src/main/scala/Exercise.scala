import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Printer

object Exercise extends lisa.Main {

  val x = variable
  val y = variable
  val z = variable
  val P = predicate(1)
  val f = function(1)

  val testThm = makeTHM("'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('x))") {
    val i1 = have(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by Restate;
  }
  show

  val fixedPointDoubleApplication = makeTHM(seq"∀'x. 'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('f('x)))") {
    assume("∀'x. 'P('x) ⇒ 'P('f('x))")
    val base = have("'P('x) ⇒ 'P('f('x)); 'P('f('x)) ==> 'P('f('f('x))) |- 'P('x) ==> 'P('f('f('x)))") by Tautology
    have("'P('x) ==> 'P('f('f('x)))") subproof {
      assume("∀'x. 'P('x) ⇒ 'P('f('x))")
      have("'P('f('x)) ==> 'P('f('f('x))) |- 'P('x) ==> 'P('f('f('x)))") by LeftForall(x)(base)
      thenHave("∀'x. 'P('x) ⇒ 'P('f('x))|- 'P('x) ==> 'P('f('f('x)))") by LeftForall(f(x))
    }
    showCurrentProof()
  }
  show

  val defineNonEmptySet = makeTHM(" |- ∃!'x. !('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet)") {
    val subst = have("|- False <=> elem(emptySet, emptySet)") by Rewrite(emptySetAxiom of (x -> emptySet()))
    have(" elem(emptySet, unorderedPair(emptySet, emptySet))<=>False |- ") by Rewrite(pairAxiom of (x -> emptySet(), y -> emptySet(), z -> emptySet()))
    andThen(applySubst(subst))
    thenHave(" ∀'z. elem('z, unorderedPair(emptySet, emptySet)) ⇔ elem('z, emptySet) |- ") by LeftForall(emptySet())
    andThen(applySubst(extensionalityAxiom of (x -> unorderedPair(emptySet(), emptySet()), y -> emptySet())))
    andThen(applySubst(x === unorderedPair(emptySet(), emptySet())))
    thenHave(" |- (!('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet)) <=> ('x=unorderedPair(emptySet, emptySet))") by Tautology
    thenHave(" |- ∀'x. ('x=unorderedPair(emptySet, emptySet)) <=> (!('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet))") by RightForall
    thenHave(" |- ∃'y. ∀'x. ('x='y) <=> (!('x=emptySet) ∧ 'x=unorderedPair(emptySet, emptySet))") by RightExists(unorderedPair(emptySet(), emptySet()))
  }
  show

  val nonEmpty = DEF() --> The(x, !(x === emptySet()))(defineNonEmptySet)
  show

}
