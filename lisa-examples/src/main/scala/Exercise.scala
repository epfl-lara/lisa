import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Printer

object Exercise extends lisa.Main {



  val x = variable
  val P = SchematicPredicateLabel("P", 1)
  val f = SchematicFunctionLabel("f", 1)



  val fixedPointDoubleApplication = makeTHM("∀'x. 'P('x) ⇒ 'P('f('x)) ⊢ 'P('x) ⇒ 'P('f('f('x)))") {
    assume(forall(x, P(x) ==> P(f(x))))
    val base = have((P(x) ==> P(f(x)), P(f(x)) ==> P(f(f(x)))) |- P(x) ==> P(f(f(x)))) by Trivial
    have(() |- P(x) ==> P(f(f(x)))) bySP {
      have(P(f(x)) ==> P(f(f(x))) |- P(x) ==> P(f(f(x)))) by LeftForall(x)(base)
      andThen(() |- P(x) ==> P(f(f(x)))) by LeftForall(f(x))
      ()
    }
  }
  show

  /*
        object fixedpointdoubleapplication extends THM("'P(x); 'P('x) ⇒ 'P('f('x)) ⊢ 'P('f('x))")({
          have("'P(x); 'P('x) ⇒ 'P('f('x)) ⊢ 'P('f('x))") by Trivial
        })

   */

  /*
  trait Simplification(s:String){
    thm: THM =>
  }

  object Thm1 extends THM("'P('f('x)) ⊢ 'P('f('x))")({
    have("'P('f('x)) ⊢ 'P('f('x))") by Hypothesis
  }) with Simplification("thing")

  val th2 = makeTHM("'P('f('x)) ⊢ 'P('f('x))"){
    have("'P('f('x)) ⊢ 'P('f('x))") by Hypothesis
  } //with simp    a function




  val thm3 = new THM("'P('f('x)) ⊢ 'P('f('x))")({
    have("'P('f('x)) ⊢ 'P('f('x))") by Hypothesis
  }) with Simplification("thing")

  show
  println(thm)
*/


}
