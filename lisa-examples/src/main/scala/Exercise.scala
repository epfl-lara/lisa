import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.{Library, Printer}

object Exercise extends lisa.Main {




  val x = variable
  val P = predicate(1)
  val f = function(1)

  val testThm = makeTHM("'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('x))") {
    val i1 = have(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by Restate;
    have(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by Restate(i1)
    //andThen(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by Restate
  }
  show

  val fixedPointDoubleApplication = makeTHM("∀'x. 'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('f('x)))") {
    assume(forall(x, P(x) ==> P(f(x))))
    val base = have((P(x) ==> P(f(x)), P(f(x)) ==> P(f(f(x)))) |- P(x) ==> P(f(f(x)))) by Trivial

    val fo = forall(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))
    have(fo) subproof {

      have((forall(x, P(x) ==> P(f(x))), P(f(x)) ==> P(f(f(x)))) |- P(x) ==> P(f(f(x)))) by LeftForall(x)(base)
      andThen((forall(x, P(x) ==> P(f(x)))) |- P(x) ==> P(f(f(x)))) by (LeftForall(f(x)))

    }
    //showCurrentProof()
  }
  show


}
