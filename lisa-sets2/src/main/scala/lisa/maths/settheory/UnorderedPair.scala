package lisa.maths.settheory

object UnorderedPair extends lisa.Main:

  private val s = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Ind >>: Prop]

  /**
   * Unordered pair of sets
   */
  val upair = unorderedPair

  /**
   * Unordered pair of sets
   */
  val <> = upair

  extension (t: Expr[Ind])
    /**
     * Infix notation for an unordered pair.
     */
    infix def <>(s: Expr[Ind]) = upair(t)(s)

  val firstMember = Theorem(x ∈ (x <> y)):
    have(thesis) by Tautology.from(<>.definition of (z := x))

  val secondMember = Theorem(y ∈ (x <> y)):
    have(thesis) by Tautology.from(<>.definition of (z := y))

  // val symmetry = Theorem( (x <> y) === (y <> x) ):
  //   val fwd = have(z ∈ (x <> y) <=> ((z === x) \/ (z === y))) by Restate.from(<>.definition)
  //   val bwd = have(z ∈ (y <> x) <=> ((z === y) \/ (z === x))) by Restate.from(<>.definition of (x := y, y := x))

  //   have(z ∈ (x <> y) <=> z ∈ (y <> x)) by Tautology.from(fwd, bwd)
  //   thenHave(thesis) by Extensionality.tactic

end UnorderedPair
