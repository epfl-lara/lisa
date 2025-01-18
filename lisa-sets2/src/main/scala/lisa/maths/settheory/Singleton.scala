package lisa.maths.settheory

import lisa.maths.settheory.UnorderedPair.*
import lisa.automation.Substitution

object Singleton extends lisa.Main:

  private val s = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Ind >>: Prop]

  val singleton = DEF(lambda(x, x <> x))

  extension (t: Expr[Ind])
    /**
     * Prefix notation for singleton set
     */
    def unary_~ = singleton(x)


  println(singleton.definition.statement)

  val membership = Theorem(x ∈ ~x):
    have(x ∈ (x <> x)) by Restate.from(UnorderedPair.firstMember of (y := x))
    thenHave(thesis) by Substitution.Apply(singleton.definition)

end Singleton
