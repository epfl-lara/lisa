package lisa.maths.SetTheory.Base

import Class.*

import scala.annotation.targetName

/**
 * The replacement axiom schema states that for any class-function `f : V -> V`
 * and any set `S`, one can define the set `R = {f(x) | x ∈ S}`.
 */
object Replacement extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val A = variable[Ind]
  private val R, S = variable[Ind]
  private val f = variable[ClassFunction]
  private val P = variable[Ind >>: Ind >>: Prop]

  /**
   * Definition --- For any class-function `f : V -> V` and any set `S`, defines the set
   *
   *   `R = {f(x) | x ∈ S}`
   */
  private val replacement = DEF(λ(f, λ(S, ε(R, ∀(y, y ∈ R <=> ∃(x, x ∈ S /\ (f(x) === y))))))).printAs(args => {
    val λ(x, t) = (args(0).asInstanceOf[Expr[Ind >>: Ind]]: @unchecked) // always of this form when using the notation
    val S = args(1)
    s"{$t | $x ∈ $S}"
  })

  extension (body: Expr[Ind]) {

    /**
     * Notation `{f(x) | x ∈ S}`.
     *
     * Note: the [[scala.annotation.targetName]] annotation is required to avoid clashing
     * with sets built by comprehension.
     */
    @targetName("replacement_|")
    def |(e: Expr[Prop]): set = {
      e match {
        case (x: Variable[Ind]) ∈ s => replacement(λ(x, body))(s)
        case _ => throw new IllegalArgumentException("Invalid replacement.")
      }
    }
  }

  /**
   * Existence --- For any class-function `f : V -> V` and set `S`, the set `{f(x) | x ∈ S}` exists.
   *
   * Follows from the [[replacementSchema]].
   */
  val existence = Theorem(
    ∃(R, ∀(y, y ∈ R <=> ∃(x, x ∈ S /\ (f(x) === y))))
  ) {
    have((f(x) === y, f(x) === z) |- y === z) by Congruence
    thenHave((f(x) === y) /\ (f(x) === z) ==> (y === z)) by Restate
    thenHave(∀(y, ∀(z, (f(x) === y) /\ (f(x) === z) ==> (y === z)))) by Generalize
    thenHave(x ∈ S ==> ∀(y, ∀(z, (f(x) === y) /\ (f(x) === z) ==> (y === z)))) by Tautology
    thenHave(∀(x, x ∈ S ==> ∀(y, ∀(z, (f(x) === y) /\ (f(x) === z) ==> (y === z))))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(replacementSchema of (A := S, P := λ(x, λ(y, f(x) === y))))
  }

  /**
   * Membership --- `y ∈ {f(x) | x ∈ S}` if and only if there exists `x ∈ S` such that `f(x) = y`.
   */
  val membership = Theorem(
    y ∈ { f(x) | x ∈ S } <=> ∃(x, x ∈ S /\ (f(x) === y))
  ) {
    def P(z: Expr[Ind]) = ∀(y, y ∈ z <=> ∃(x, x ∈ S /\ (f(x) === y)))

    have(P(R) |- P(R)) by Hypothesis
    thenHave(P(R) |- P(ε(R, P(R)))) by RightEpsilon
    thenHave(P(R) |- ∀(y, y ∈ { f(x) | x ∈ S } <=> ∃(x, x ∈ S /\ (f(x) === y)))) by Substitute(replacement.definition)
    thenHave(∃(R, P(R)) |- ∀(y, y ∈ { f(x) | x ∈ S } <=> ∃(x, x ∈ S /\ (f(x) === y)))) by LeftExists
    thenHave(∃(R, P(R)) |- y ∈ { f(x) | x ∈ S } <=> ∃(x, x ∈ S /\ (f(x) === y))) by InstantiateForall(y)

    have(thesis) by Cut(existence, lastStep)
  }

  /**
   * Tactic that proves `y ∈ { f(x) | x ∈ S } <=> ∃(x, x ∈ S /\ (f(x) === y))` by finding suitable `S` and `f`
   * from the conclusion.
   *
   * Essentially a thin wrapper around applying [[membership]] but without specifying the arguments.
   *
   * TODO: In the future, this tactic could be removed by Congruence with unification
   */
  def apply(using proof: lisa.SetTheoryLibrary.Proof)(conclusion: Sequent): proof.ProofTacticJudgement = {
    if conclusion.right.size != 1 then proof.InvalidProofTactic("Don't know which formula to prove by replacement.")
    else
      conclusion.right.head match {
        case v ∈ App(App(`replacement`, g), s) <=> _ =>
          // Use Tautology instead of Restate to handle trivial rewrites/weakening
          unwrapTactic(Tautology.from(membership of (y := v, S := s, f := g))(conclusion))("Could not prove membership by replacement.")

        case _ => proof.InvalidProofTactic("Could not prove membership by replacement.")
      }
  }

  /**
   * Theorem --- If `x ∈ S` then `f(x) ∈ {f(x) | x ∈ S}`.
   *
   *   `x ∈ s |- f(x) ∈ {f(x) | x ∈ S}`
   */
  val map = Theorem(
    x ∈ S |- f(x) ∈ { f(x) | x ∈ S }
  ) {
    assume(x ∈ S)
    thenHave(x ∈ S /\ (f(x) === f(x))) by Tautology
    thenHave(∃(z, z ∈ S /\ (f(z) === f(x)))) by RightExists
    thenHave(thesis) by Tautology.fromLastStep(membership of (y := f(x)))
  }

}
