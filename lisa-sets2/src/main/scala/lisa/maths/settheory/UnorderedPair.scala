package lisa.maths.settheory

object UnorderedPair extends lisa.Main:

  private val s = variable[Term]
  private val x = variable[Term]
  private val y = variable[Term]
  private val z = variable[Term]
  private val P = variable[Term >>: Formula]
  private val Q = variable[Term >>: Term >>: Formula]

  /** Unordered pair of sets */
  val upair = unorderedPair
  /** Unordered pair of sets */
  val <> = upair

  extension (t: Expr[Term])
    /**
      * Infix notation for an unordered pair.
      */
    infix def <> (s: Expr[Term]) = upair(t)(s)

  val firstMember = Theorem( x ∈ (x <> y) ):
    have(thesis) by Tautology.from(<>.definition of (z := x))
  
  val secondMember = Theorem( y ∈ (x <> y) ):
    have(thesis) by Tautology.from(<>.definition of (z := y))

  // val symmetry = Theorem( (x <> y) === (y <> x) ):
  //   val fwd = have(z ∈ (x <> y) <=> ((z === x) \/ (z === y))) by Restate.from(<>.definition)
  //   val bwd = have(z ∈ (y <> x) <=> ((z === y) \/ (z === x))) by Restate.from(<>.definition of (x := y, y := x))

  //   have(z ∈ (x <> y) <=> z ∈ (y <> x)) by Tautology.from(fwd, bwd)
  //   thenHave(thesis) by Extensionality.tactic

end UnorderedPair