import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau
import lisa.automation.atp.Egg
import lisa.automation.atp.Goeland

object Example extends lisa.Main:
  draft()


  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val Q = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val e1 = P(x) ==> P(f(y))
  val e2 = forall(x, P(x) /\ P(f(y)))

  println(e1.rewrite(P(x), Q(x)))
  println(e1.rewrite(P(x), Q(y)))
  println(e2.rewrite(P(f(y)), Q(x)))


/*
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val thing : set = x
  extension (x: set) {
    inline infix def subset(y: set): Expr[Prop] = App(App(⊆, x), y)
  }
  // Simple proof with LISA's DSL
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    val a1 = assume(∀(x, P(x) ==> P(f(x))))
    have(thesis) by Tautology.from(a1 of x, a1 of f(x))
  }

  // Example of set theoretic development
  val union = Theorem(
    //App(App(⊆, x), y)
    //⊆.#@(x).#@(y)
    (thing) subset (thing)
  ) {
    sorry
  }
  
  /**
 * Theorem --- The empty set is a subset of every set.
 *
   *    `|- ∅ ⊆ x`
 */
  val leftEmpty = Theorem(
    P(x) //∅ ⊆ x
  ) {
    //have((y ∈ ∅) ==> (y ∈ x)) by Weakening(emptySetAxiom of (x := y))
    //val rhs = thenHave(∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    //have(thesis) by Tautology.from(subsetAxiom of (x := ∅, y := x), rhs)
  }

  /**
 * Theorem --- If a set has an element, then it is not the empty set.
 *
   *    `y ∈ x ⊢ ! x = ∅`
 */
  val setWithElementNonEmpty = Theorem(
    (y ∈ x) |- x =/= ∅
  ) {
    have((x === ∅) |- !(y ∈ x)) by Substitute(x === ∅)(emptySetAxiom of (x := y))
  }

  /**
 * Theorem --- A power set is never empty.
 *
   *   `|- !powerAxiom(x) = ∅`
 */
  val powerSetNonEmpty = Theorem(
    𝒫(x) =/= ∅
  ) {
    have(thesis) by Tautology.from(
      setWithElementNonEmpty of (y := ∅, x := 𝒫(x)),
      powerSetAxiom of (x := ∅, y := x),
      leftEmpty
    )
  }

  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Tableau
  }


/**
 * Example showing discharge of proofs using the Goeland theorem prover. Will
 * fail if Goeland is not available on PATH.
 */
object ATPExample extends lisa.Main:
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]

  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))):
    have(thesis) by Goeland

  val rule8 = Axiom(forall(x, x === f(f(f(f(f(f(f(f(x))))))))))
  val rule5 = Axiom(forall(x, x === f(f(f(f(f(x)))))))

  val saturation = Theorem(∅ === f(∅)):
    have(thesis) by Egg.from(rule8, rule5)
 */
