package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function.{app}
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Relation.relationBetween

/**
 * Identity function (set-coded).
 *
 * `id(A)` is the graph `{ (x, x) | x ∈ A }`.
 */
object Identity extends lisa.Main {

  private val A = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val y0 = variable[Ind]
  private val z = variable[Ind]

  val id = DEF(λ(A, { (x, x) | x ∈ A }))

  val typing = Theorem(
    id(A) :: A -> A
  ) {
    // relationBetween: id(A) ⊆ A × A
    have(id(A) ⊆ (A × A)) subproof {
      val phi = z ∈ id(A)
      val psi = z ∈ (A × A)

      have(phi ==> psi) subproof {
        assume(phi)
        thenHave(z ∈ { (x, x) | x ∈ A }) by Substitute(id.definition)
        thenHave(∃(x, x ∈ A /\ ((x, x) === z))) by Tautology.fromLastStep(
          Replacement.membership of (A := A, y := z, F := λ(x, (x, x)))
        )
        val ex = lastStep
        val body = x ∈ A /\ ((x, x) === z)

        val zInAAFromBody = have(body |- z ∈ (A × A)) subproof {
          val hx = assume(body)

          val xInA = have(x ∈ A) by Tautology.from(hx)
          have((x, x) ∈ (A × A)) by Tautology.from(
            CartesianProduct.membershipSufficientCondition of (A := A, B := A, x := x, y := x),
            xInA,
            xInA
          )
          val pairInAA = lastStep

          val pairEq = have((x, x) === z) by Tautology.from(hx)
          val transport = have(((x, x) ∈ (A × A), (x, x) === z) |- z ∈ (A × A)) by Congruence
          have(z ∈ (A × A)) by Tautology.from(transport, pairInAA, pairEq)
        }

        val goalSeq = (zInAAFromBody.statement.left - body) + ∃(x, body) |- zInAAFromBody.statement.right
        have(goalSeq) by LeftExists(zInAAFromBody)
        have(psi) by Cut(ex, lastStep)

        thenHave(thesis) by RightImplies.withParameters(phi, psi)
      }

      thenHave(∀(z, phi ==> psi)) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := id(A), y := (A × A)))
    }
    val subset = lastStep

    have(relationBetween(id(A))(A)(A)) by Substitute(relationBetween.definition of (R := id(A), X := A, Y := A))(subset)
    val relBetween = lastStep

    // ∀x∈A, ∃!y. (x,y)∈id(A)
    have(∀(x ∈ A, Quantifiers.∃!(y, (x, y) ∈ id(A)))) subproof {
      have(x ∈ A ==> Quantifiers.∃!(y, (x, y) ∈ id(A))) subproof {
        val xInA = assume(x ∈ A)

        have((x, x) ∈ id(A)) subproof {
          have(x ∈ A /\ ((x, x) === (x, x))) by Tautology.from(xInA)
          thenHave(∃(y, y ∈ A /\ ((y, y) === (x, x)))) by RightExists
          thenHave((x, x) ∈ { (x, x) | x ∈ A }) by Tautology.fromLastStep(
            Replacement.membership of (A := A, y := (x, x), F := λ(x, (x, x)))
          )
          thenHave((x, x) ∈ id(A)) by Substitute(id.definition)
        }
        val existsPair = lastStep
        val existsY = have(∃(y, (x, y) ∈ id(A))) by RightExists(existsPair)

        have(∀(y, ∀(y0, ((x, y) ∈ id(A) /\ (x, y0) ∈ id(A)) ==> (y === y0)))) subproof {
          val conj = (x, y) ∈ id(A) /\ (x, y0) ∈ id(A)

          have(conj ==> (y === y0)) subproof {
            val both = assume(conj)
            val hy = have((x, y) ∈ id(A)) by Tautology.from(both)
            val hy0 = have((x, y0) ∈ id(A)) by Tautology.from(both)

            val yEqXFromMem = have((x, y) ∈ id(A) |- y === x) subproof {
              assume((x, y) ∈ id(A))
              thenHave((x, y) ∈ { (x, x) | x ∈ A }) by Substitute(id.definition)
              thenHave(∃(z, z ∈ A /\ ((z, z) === (x, y)))) by Tautology.fromLastStep(
                Replacement.membership of (A := A, y := (x, y), F := λ(x, (x, x)))
              )
              val ex = lastStep
              val body = z ∈ A /\ ((z, z) === (x, y))

              val yEqXFromBody = have(body |- y === x) subproof {
                val hz = assume(body)

                val zEqX = have(z === x) by Tautology.from(hz, Pair.extensionality of (a := z, b := z, c := x, d := y))
                val zEqY = have(z === y) by Tautology.from(hz, Pair.extensionality of (a := z, b := z, c := x, d := y))
                have(y === x) by Congruence.from(zEqX, zEqY)
              }

              val goalSeq = (yEqXFromBody.statement.left - body) + ∃(z, body) |- yEqXFromBody.statement.right
              have(goalSeq) by LeftExists(yEqXFromBody)
              have(y === x) by Cut(ex, lastStep)
            }

            val y0EqXFromMem = have((x, y0) ∈ id(A) |- y0 === x) subproof {
              assume((x, y0) ∈ id(A))
              thenHave((x, y0) ∈ { (x, x) | x ∈ A }) by Substitute(id.definition)
              thenHave(∃(z, z ∈ A /\ ((z, z) === (x, y0)))) by Tautology.fromLastStep(
                Replacement.membership of (A := A, y := (x, y0), F := λ(x, (x, x)))
              )
              val ex = lastStep
              val body = z ∈ A /\ ((z, z) === (x, y0))

              val y0EqXFromBody = have(body |- y0 === x) subproof {
                val hz = assume(body)

                val zEqX = have(z === x) by Tautology.from(hz, Pair.extensionality of (a := z, b := z, c := x, d := y0))
                val zEqY0 = have(z === y0) by Tautology.from(hz, Pair.extensionality of (a := z, b := z, c := x, d := y0))
                have(y0 === x) by Congruence.from(zEqX, zEqY0)
              }

              val goalSeq = (y0EqXFromBody.statement.left - body) + ∃(z, body) |- y0EqXFromBody.statement.right
              have(goalSeq) by LeftExists(y0EqXFromBody)
              have(y0 === x) by Cut(ex, lastStep)
            }

            val yEqX = have(y === x) by Cut(hy, yEqXFromMem)
            val y0EqX = have(y0 === x) by Cut(hy0, y0EqXFromMem)
            have(y === y0) by Congruence.from(yEqX, y0EqX)

            thenHave(thesis) by RightImplies.withParameters(conj, y === y0)
          }

          thenHave(∀(y0, conj ==> (y === y0))) by RightForall
          thenHave(thesis) by RightForall
        }
        val unique = lastStep

        have(Quantifiers.∃!(y, (x, y) ∈ id(A))) by Tautology.from(
          Quantifiers.existsOneAlternativeDefinition of (P := λ(y, (x, y) ∈ id(A))),
          existsY,
          unique
        )

        thenHave(thesis) by RightImplies.withParameters(x ∈ A, Quantifiers.∃!(y, (x, y) ∈ id(A)))
      }

      thenHave(∀(x, x ∈ A ==> Quantifiers.∃!(y, (x, y) ∈ id(A)))) by RightForall
      thenHave(thesis) by Restate
    }
    val exuniq = lastStep

    have(relationBetween(id(A))(A)(A) /\ ∀(x ∈ A, Quantifiers.∃!(y, (x, y) ∈ id(A)))) by Tautology.from(relBetween, exuniq)
    thenHave(thesis) by Substitute(Function.functionBetween.definition of (f := id(A), A := A, B := A))
  }

  val app_id = Theorem(
    (id(A) :: A -> A, x ∈ A) |- app(id(A))(x) === x
  ) {
    val idTy = assume(id(A) :: A -> A)
    val xInA = assume(x ∈ A)

    have(dom(id(A)) === A) by Tautology.from(BasicTheorems.functionBetweenDomain of (f := id(A), A := A, B := A), idTy)
    have(x ∈ dom(id(A))) by Congruence.from(lastStep, xInA)
    val xInDom = lastStep

    have((x, x) ∈ id(A)) subproof {
      have(x ∈ A /\ ((x, x) === (x, x))) by Tautology.from(xInA)
      thenHave(∃(y, y ∈ A /\ ((y, y) === (x, x)))) by RightExists
      thenHave((x, x) ∈ { (x, x) | x ∈ A }) by Tautology.fromLastStep(
        Replacement.membership of (A := A, y := (x, x), F := λ(x, (x, x)))
      )
      thenHave((x, x) ∈ id(A)) by Substitute(id.definition)
    }
    val pairIn = lastStep

    have((app(id(A))(x) === x) <=> (x, x) ∈ id(A)) by Tautology.from(
      BasicTheorems.appDefinition of (f := id(A), x := x, y := x),
      BasicTheorems.functionBetweenIsFunction of (f := id(A), A := A, B := A),
      idTy,
      xInDom
    )
    thenHave(thesis) by Tautology.fromLastStep(pairIn)
  }
}
