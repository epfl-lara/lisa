import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Printer

object Exercise extends lisa.Main {



  val x = variable
  val P = SchematicPredicateLabel("P", 1)
  val f = SchematicFunctionLabel("f", 1)

  val testThm = makeTHM("'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('x))") {
    val i1 = have(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by Hypothesis()
    have(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by LeftAnd(i1)
    andThen(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by LeftAnd
  }
  show



  /*
  val fixedPointDoubleApplication = makeTHM("∀'x. 'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('f('x)))") {
    assume(forall(x, P(x) ==> P(f(x))))
    val base = have((P(x) ==> P(f(x)), P(f(x)) ==> P(f(f(x)))) |- P(x) ==> P(f(f(x)))) by Trivial
    have(() |- P(x) ==> P(f(f(x)))) bySP {
      have(P(f(x)) ==> P(f(f(x))) |- P(x) ==> P(f(f(x)))) by LeftForall(x)(base)
      andThen(() |- P(x) ==> P(f(f(x)))) by LeftForall(f(x))
    }
    showCurrentProof()
  }
  show
*/


}
