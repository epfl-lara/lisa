package lisa.maths.SetTheory.Base

import Class.*

import scala.annotation.targetName

/**
 * The replacement axiom schema states that for any class-function `F : V -> V`
 * and any set `S`, one can define the set `R = {F(x) | x ∈ S}`.
 */
object Replacement extends lisa.Main {
  import Symbols.{P as _, *}

  private val P = variable[Ind >>: Ind >>: Prop]

  /**
   * Definition --- For any class-function `F : V -> V` and any set `A`, defines the set
   *
   *   `B = {F(x) | x ∈ S}`
   */
  private val replacement = DEF(λ(F, λ(A, ε(B, ∀(y, y ∈ B <=> ∃(x, x ∈ A /\ (F(x) === y))))))).printAs(args => {
    val A = args(1)
    args(0).asInstanceOf[Expr[Ind >>: Ind]] match {
      case λ(x, e) => s"{$e | $x ∈ $A}"
      case _ => s"replacement(${args(0)})(${args(1)})"
    }
  })

  extension (body: Expr[Ind]) {

    /**
     * Notation `{F(x) | x ∈ S}`.
     *
     * Note: the [[scala.annotation.targetName]] annotation is required to avoid clashing
     * with sets built by comprehension.
     */
    @targetName("replacement_|")
    def |(e: Expr[Prop]): Expr[Ind] = {
      e match {
        case (x: Variable[Ind]) ∈ s => replacement(λ(x, body))(s)
        case _ => throw new IllegalArgumentException("Invalid replacement.")
      }
    }
  }

  /**
   * Existence --- For any class-function `F : V -> V` and set `S`, the set `{F(x) | x ∈ S}` exists.
   *
   * Follows from the [[replacementSchema]].
   */
  val existence = Theorem(
    ∃(B, ∀(y, y ∈ B <=> ∃(x, x ∈ A /\ (F(x) === y))))
  ) {
    have((F(x) === y, F(x) === z) |- y === z) by Congruence
    thenHave((F(x) === y) /\ (F(x) === z) ==> (y === z)) by Restate
    thenHave(∀(y, ∀(z, (F(x) === y) /\ (F(x) === z) ==> (y === z)))) by Generalize
    thenHave(x ∈ A ==> ∀(y, ∀(z, (F(x) === y) /\ (F(x) === z) ==> (y === z)))) by Tautology
    thenHave(∀(x ∈ A, ∀(y, ∀(z, (F(x) === y) /\ (F(x) === z) ==> (y === z))))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(replacementSchema of (A := A, P := λ(x, λ(y, F(x) === y))))
  }

  /**
   * Membership --- `y ∈ {F(x) | x ∈ S}` if and only if there exists `x ∈ S` such that `F(x) = y`.
   */
  val membership = Theorem(
    y ∈ { F(x) | x ∈ A } <=> ∃(x ∈ A, F(x) === y)
  ) {
    def P(z: Expr[Ind]) = ∀(y, y ∈ z <=> ∃(x ∈ A, F(x) === y))

    have(P(B) |- P(B)) by Hypothesis
    thenHave(P(B) |- P(ε(B, P(B)))) by RightEpsilon
    thenHave(P(B) |- ∀(y, y ∈ { F(x) | x ∈ A } <=> ∃(x ∈ A, F(x) === y))) by Substitute(replacement.definition)
    thenHave(∃(B, P(B)) |- ∀(y, y ∈ { F(x) | x ∈ A } <=> ∃(x ∈ A, F(x) === y))) by LeftExists
    thenHave(∃(B, P(B)) |- y ∈ { F(x) | x ∈ A } <=> ∃(x ∈ A, F(x) === y)) by InstantiateForall(y)

    have(thesis) by Cut(existence, lastStep)
  }

  /**
   * Tactic that proves `y ∈ { F(x) | x ∈ S } <=> ∃(x, x ∈ S /\ (F(x) === y))` by finding suitable `S` and `F`
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
          unwrapTactic(Tautology.from(membership of (y := v, A := s, F := g))(conclusion))("Could not prove membership by replacement.")

        case _ => proof.InvalidProofTactic("Could not prove membership by replacement.")
      }
  }

  /**
   * Theorem --- If `x ∈ S` then `F(x) ∈ {F(x) | x ∈ S}`.
   *
   *   `x ∈ s |- F(x) ∈ {F(x) | x ∈ S}`
   */
  val map = Theorem(
    x ∈ A |- F(x) ∈ { F(x) | x ∈ A }
  ) {
    assume(x ∈ A)
    thenHave(x ∈ A /\ (F(x) === F(x))) by Tautology
    thenHave(∃(z, z ∈ A /\ (F(z) === F(x)))) by RightExists
    thenHave(thesis) by Tautology.fromLastStep(membership of (y := F(x)))
  }

}
