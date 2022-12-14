import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Library
import lisa.utils.KernelHelpers.*
import lisa.utils.Printer

object Exercise extends lisa.Main {

  val x = variable
  val P = predicate(1)
  val f = function(1)


  val testThm = makeTHM("'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('x))") {
    val i1 = have(P(x) ==> P(f(x)) |- P(x) ==> P(f(x))) by Restate;
  }
  show

  val fixedPointDoubleApplication = makeTHM(seq"∀'x. 'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('f('x)))") {
    assume("∀'x. 'P('x) ⇒ 'P('f('x))")
    val base = have("'P('x) ⇒ 'P('f('x)); 'P('f('x)) ==> 'P('f('f('x))) |- 'P('x) ==> 'P('f('f('x)))") by Trivial
    have("'P('x) ==> 'P('f('f('x)))") subproof {
      assume("∀'x. 'P('x) ⇒ 'P('f('x))")
      have("'P('f('x)) ==> 'P('f('f('x))) |- 'P('x) ==> 'P('f('f('x)))") by LeftForall(x)(base)
      andThen("∀'x. 'P('x) ⇒ 'P('f('x))|- 'P('x) ==> 'P('f('f('x)))") by LeftForall(f(x))
    }
    showCurrentProof()
  }
  show

}
