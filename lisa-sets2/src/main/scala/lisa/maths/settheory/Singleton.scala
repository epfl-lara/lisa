package lisa.maths.settheory

import lisa.maths.settheory.UnorderedPair.*
import lisa.automation.Substitution

object Singleton extends lisa.Main:

  private val s = variable[Term]
  private val x = variable[Term]
  private val y = variable[Term]
  private val z = variable[Term]
  private val P = variable[Term >>: Formula]
  private val Q = variable[Term >>: Term >>: Formula]

  val singleton = DEF ( lambda(x, x <> x) )

  extension (t: Term)
    /**
      * Prefix notation for singleton set
      */
    def unary_~ = singleton(x)

  val membership = Theorem( x ∈ ~x ):
    have(x ∈ (x <> x)) by Restate.from(UnorderedPair.firstMember of (y := x)) 
    thenHave(thesis) by Substitution.Apply(singleton.definition)


end Singleton