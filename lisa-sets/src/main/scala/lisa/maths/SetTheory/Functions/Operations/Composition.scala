package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function.{app, dom, functionBetween}
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Function composition (set-coded).
 *
 * The composition `f ∘ g` is the graph `{ (x, f(g(x))) | x ∈ dom(g) }`.
 *
 * This file provides:
 * - the definition and notation `∘`
 * - a typing theorem: if `f : A → B` and `g : C → A` then `f ∘ g : C → B`
 * - the expected application lemma under the same typing hypotheses
 */
object Composition extends lisa.Main {

  private val f = variable[Ind]
  private val g = variable[Ind]

  private val A = variable[Ind]
  private val B = variable[Ind]
  private val C = variable[Ind]

  private val x = variable[Ind]
  private val y = variable[Ind]
  private val y0 = variable[Ind]
  private val z = variable[Ind]
  private val D0 = variable[Ind]

  val ∘ = DEF(λ(f, λ(g, { (x, app(f)(app(g)(x))) | x ∈ dom(g) }))).printInfix()
  val comp = ∘

  extension (f: Expr[Ind]) {
    inline infix def ∘(g: Expr[Ind]): Expr[Ind] = comp(f)(g)
  }

  val typing = Theorem(
    (f :: A -> B, g :: C -> A) |- ((f ∘ g) :: C -> B)
  ) {
    val fTy = assume(f :: A -> B)
    val gTy = assume(g :: C -> A)

    val domG = have(dom(g) === C) by Tautology.from(BasicTheorems.functionBetweenDomain of (f := g, A := C, B := A), gTy)

    val subset = have((f ∘ g) ⊆ (C × B)) subproof {
      val phi = z ∈ (f ∘ g)
      val psi = z ∈ (C × B)

      have(phi ==> psi) subproof {
        assume(phi)
        thenHave(z ∈ { (x, app(f)(app(g)(x))) | x ∈ dom(g) }) by Substitute(comp.definition)
        thenHave(∃(x, x ∈ dom(g) /\ ((x, app(f)(app(g)(x))) === z))) by Tautology.fromLastStep(
          Replacement.membership of (A := dom(g), y := z, F := λ(x, (x, app(f)(app(g)(x)))))
        )
        val ex = lastStep
        val body = x ∈ dom(g) /\ ((x, app(f)(app(g)(x))) === z)

        val zInProdFromBody = have(body |- z ∈ (C × B)) subproof {
          val hx = assume(body)

          val xInDom = have(x ∈ dom(g)) by Tautology.from(hx)
          val xInC = have(x ∈ C) by Congruence.from(domG, xInDom)
          val gxInA = have(app(g)(x) ∈ A) by Tautology.from(gTy, xInC, BasicTheorems.appTyping of (f := g, A := C, B := A, x := x))
          val fgxInB = have(app(f)(app(g)(x)) ∈ B) by Tautology.from(
            fTy,
            gxInA,
            BasicTheorems.appTyping of (f := f, A := A, B := B, x := app(g)(x))
          )

          have((x, app(f)(app(g)(x))) ∈ (C × B)) by Tautology.from(
            CartesianProduct.membershipSufficientCondition of (A := C, B := B, x := x, y := app(f)(app(g)(x))),
            xInC,
            fgxInB
          )
          val pairInProd = lastStep
          val pairEq = have((x, app(f)(app(g)(x))) === z) by Tautology.from(hx)
          val transport = have(((x, app(f)(app(g)(x))) ∈ (C × B), (x, app(f)(app(g)(x))) === z) |- z ∈ (C × B)) by Congruence
          have(z ∈ (C × B)) by Tautology.from(transport, pairInProd, pairEq)
        }

        val goalSeq = (zInProdFromBody.statement.left - body) + ∃(x, body) |- zInProdFromBody.statement.right
        have(goalSeq) by LeftExists(zInProdFromBody)

        have(z ∈ (C × B)) by Cut(ex, lastStep)
        thenHave(thesis) by RightImplies.withParameters(phi, psi)
      }

      thenHave(∀(z, z ∈ (f ∘ g) ==> z ∈ (C × B))) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := (f ∘ g), y := (C × B)))
    }

    have((f ∘ g) ⊆ (C × B)) by Restate.from(subset)
    thenHave(relationBetween(f ∘ g)(C)(B)) by Substitute(relationBetween.definition of (R := (f ∘ g), X := C, Y := B))
    val relBetween = lastStep

    val exuniq = have(∀(x ∈ C, Quantifiers.∃!(y, (x, y) ∈ (f ∘ g)))) subproof {
      have(x ∈ C ==> Quantifiers.∃!(y, (x, y) ∈ (f ∘ g))) subproof {
        val xInC = assume(x ∈ C)
        val xInDomG = have(x ∈ dom(g)) by Congruence.from(domG, xInC)

        have(Quantifiers.∃!(y, (x, y) ∈ (f ∘ g))) subproof {
          // existence: witness `y = f(g(x))`
          have(x ∈ dom(g) /\ ((x, app(f)(app(g)(x))) === (x, app(f)(app(g)(x))))) by Tautology.from(xInDomG)
          thenHave(∃(z, z ∈ dom(g) /\ ((z, app(f)(app(g)(z))) === (x, app(f)(app(g)(x)))))) by RightExists
          thenHave((x, app(f)(app(g)(x))) ∈ { (x, app(f)(app(g)(x))) | x ∈ dom(g) }) by Tautology.fromLastStep(
            Replacement.membership of (A := dom(g), y := (x, app(f)(app(g)(x))), F := λ(z, (z, app(f)(app(g)(z)))))
          )
          thenHave((x, app(f)(app(g)(x))) ∈ (f ∘ g)) by Substitute(comp.definition)
          val existsY = have(∃(y, (x, y) ∈ (f ∘ g))) by RightExists(lastStep)

          // uniqueness: any `y` in the fiber equals `f(g(x))`
          have(∀(y, ∀(y0, ((x, y) ∈ (f ∘ g) /\ (x, y0) ∈ (f ∘ g)) ==> (y === y0)))) subproof {
            val conj = (x, y) ∈ (f ∘ g) /\ (x, y0) ∈ (f ∘ g)

            have(conj ==> (y === y0)) subproof {
              val both = assume(conj)
              val hy = have((x, y) ∈ (f ∘ g)) by Tautology.from(both)
              val hy0 = have((x, y0) ∈ (f ∘ g)) by Tautology.from(both)

              have((x, y) ∈ (f ∘ g) |- y === app(f)(app(g)(x))) subproof {
                assume((x, y) ∈ (f ∘ g))
                thenHave((x, y) ∈ { (x, app(f)(app(g)(x))) | x ∈ dom(g) }) by Substitute(comp.definition)
                thenHave(∃(z, z ∈ dom(g) /\ ((z, app(f)(app(g)(z))) === (x, y)))) by Tautology.fromLastStep(
                  Replacement.membership of (A := dom(g), y := (x, y), F := λ(z, (z, app(f)(app(g)(z)))))
                )
                val ex = lastStep
                val body = z ∈ dom(g) /\ ((z, app(f)(app(g)(z))) === (x, y))

                val yEqFromBody = have(body |- y === app(f)(app(g)(x))) subproof {
                  val hz = assume(body)

                  val zEqX = have(z === x) by Tautology.from(hz, Pair.extensionality of (a := z, b := app(f)(app(g)(z)), c := x, d := y))
                  val fgzEqY = have(app(f)(app(g)(z)) === y) by Tautology.from(hz, Pair.extensionality of (a := z, b := app(f)(app(g)(z)), c := x, d := y))
                  have(y === app(f)(app(g)(x))) by Congruence.from(zEqX, fgzEqY)
                }

                val goalSeq = (yEqFromBody.statement.left - body) + ∃(z, body) |- yEqFromBody.statement.right
                have(goalSeq) by LeftExists(yEqFromBody)

                val yEq = have(y === app(f)(app(g)(x))) by Cut(ex, lastStep)
                have(thesis) by Restate.from(yEq)
              }

              val yEq = have(y === app(f)(app(g)(x))) by Tautology.from(lastStep, hy)
              val y0Eq = have(y0 === app(f)(app(g)(x))) by Tautology.from(lastStep of (y := y0), hy0)
              have(y === y0) by Congruence.from(yEq, y0Eq)

              thenHave(thesis) by RightImplies.withParameters(conj, y === y0)
            }

            thenHave(∀(y0, conj ==> (y === y0))) by RightForall
            thenHave(thesis) by RightForall
          }
          val unique = lastStep

          have(thesis) by Tautology.from(
            Quantifiers.existsOneAlternativeDefinition of (P := λ(y, (x, y) ∈ (f ∘ g))),
            existsY,
            unique
          )
        }

        thenHave(thesis) by RightImplies.withParameters(x ∈ C, Quantifiers.∃!(y, (x, y) ∈ (f ∘ g)))
      }

      thenHave(∀(x, x ∈ C ==> Quantifiers.∃!(y, (x, y) ∈ (f ∘ g)))) by RightForall
      thenHave(thesis) by Restate
    }

    have(thesis) subproof {
      have(relationBetween(f ∘ g)(C)(B) /\ ∀(x ∈ C, Quantifiers.∃!(y, (x, y) ∈ (f ∘ g)))) by Tautology.from(relBetween, exuniq)
      thenHave(thesis) by Substitute(functionBetween.definition of (f := (f ∘ g), A := C, B := B))
    }
  }

  val app_comp = Theorem(
    (f :: A -> B, g :: C -> A, x ∈ C) |- app(f ∘ g)(x) === app(f)(app(g)(x))
  ) {
    val fTy = assume(f :: A -> B)
    val gTy = assume(g :: C -> A)
    val xInC = assume(x ∈ C)

    have((f ∘ g) :: C -> B) by Tautology.from(typing, fTy, gTy)
    val compTy = lastStep

    have(Function.function(f ∘ g)) by Tautology.from(
      BasicTheorems.functionBetweenIsFunction of (f := (f ∘ g), A := C, B := B),
      compTy
    )
    val compFun = lastStep

    have(dom(f ∘ g) === C) by Tautology.from(BasicTheorems.functionBetweenDomain of (f := (f ∘ g), A := C, B := B), compTy)
    have(x ∈ dom(f ∘ g)) by Congruence.from(lastStep, xInC)
    val xInDomComp = lastStep

    // show `(x, f(g(x))) ∈ f ∘ g`
    have(x ∈ dom(g)) by Congruence.from(BasicTheorems.functionBetweenDomain of (f := g, A := C, B := A), gTy, xInC)
    thenHave(x ∈ dom(g) /\ ((x, app(f)(app(g)(x))) === (x, app(f)(app(g)(x))))) by Tautology
    thenHave(∃(z, z ∈ dom(g) /\ ((z, app(f)(app(g)(z))) === (x, app(f)(app(g)(x)))))) by RightExists
    thenHave((x, app(f)(app(g)(x))) ∈ { (x, app(f)(app(g)(x))) | x ∈ dom(g) }) by Tautology.fromLastStep(
      Replacement.membership of (A := dom(g), y := (x, app(f)(app(g)(x))), F := λ(z, (z, app(f)(app(g)(z)))))
    )
    thenHave((x, app(f)(app(g)(x))) ∈ (f ∘ g)) by Substitute(comp.definition)
    val pairInComp = lastStep

    have((app(f ∘ g)(x) === app(f)(app(g)(x))) <=> ((x, app(f)(app(g)(x))) ∈ (f ∘ g))) by Tautology.from(
      BasicTheorems.appDefinition of (f := (f ∘ g), x := x, y := app(f)(app(g)(x))),
      compFun,
      xInDomComp
    )
    thenHave(thesis) by Tautology.fromLastStep(pairInComp)
  }

  val associativity = Theorem(
    (f :: A -> B, g :: C -> A, h :: D0 -> C) |- ((f ∘ g) ∘ h) === (f ∘ (g ∘ h))
  ) {
    val fTy = assume(f :: A -> B)
    val gTy = assume(g :: C -> A)
    val hTy = assume(h :: D0 -> C)

    // Both sides are functions on `D0`.
    have(((f ∘ g) ∘ h) :: D0 -> B) by Tautology.from(
      typing of (f := (f ∘ g), g := h, A := C, B := B, C := D0),
      typing of (f := f, g := g, A := A, B := B, C := C),
      fTy,
      gTy,
      hTy
    )
    val leftTy = lastStep

    have((f ∘ (g ∘ h)) :: D0 -> B) by Tautology.from(
      typing of (f := f, g := (g ∘ h), A := A, B := B, C := D0),
      typing of (f := g, g := h, A := C, B := A, C := D0),
      fTy,
      gTy,
      hTy
    )
    val rightTy = lastStep

    have(functionOn(((f ∘ g) ∘ h))(D0)) by Tautology.from(
      BasicTheorems.functionBetweenIsFunctionOn of (f := ((f ∘ g) ∘ h), A := D0, B := B),
      leftTy
    )
    val leftOn = lastStep

    have(functionOn((f ∘ (g ∘ h)))(D0)) by Tautology.from(
      BasicTheorems.functionBetweenIsFunctionOn of (f := (f ∘ (g ∘ h)), A := D0, B := B),
      rightTy
    )
    val rightOn = lastStep

    have(∀(x ∈ D0, app(((f ∘ g) ∘ h))(x) === app((f ∘ (g ∘ h)))(x))) subproof {
      have(x ∈ D0 ==> (app(((f ∘ g) ∘ h))(x) === app((f ∘ (g ∘ h)))(x))) subproof {
        val xInD = assume(x ∈ D0)

        val leftApp1 = have(app(((f ∘ g) ∘ h))(x) === app((f ∘ g))(app(h)(x))) by Tautology.from(
          app_comp of (f := (f ∘ g), g := h, A := C, B := B, C := D0, x := x),
          typing of (f := f, g := g, A := A, B := B, C := C),
          fTy,
          gTy,
          hTy,
          xInD
        )

        val rightApp1 = have(app((f ∘ (g ∘ h)))(x) === app(f)(app((g ∘ h))(x))) by Tautology.from(
          app_comp of (f := f, g := (g ∘ h), A := A, B := B, C := D0, x := x),
          fTy,
          typing of (f := g, g := h, A := C, B := A, C := D0),
          gTy,
          hTy,
          xInD
        )

        val ghApp = have(app((g ∘ h))(x) === app(g)(app(h)(x))) by Tautology.from(
          app_comp of (f := g, g := h, A := C, B := A, C := D0, x := x),
          gTy,
          hTy,
          xInD
        )

        val fgApp = have(app((f ∘ g))(app(h)(x)) === app(f)(app(g)(app(h)(x)))) by Tautology.from(
          app_comp of (f := f, g := g, A := A, B := B, C := C, x := app(h)(x)),
          fTy,
          gTy,
          BasicTheorems.appTyping of (f := h, A := D0, B := C, x := x),
          hTy,
          xInD
        )

        val rhs2 = have(app(f)(app((g ∘ h))(x)) === app(f)(app(g)(app(h)(x)))) by Congruence.from(ghApp)

        have(app(((f ∘ g) ∘ h))(x) === app((f ∘ (g ∘ h)))(x)) by Congruence.from(leftApp1, fgApp, rhs2, rightApp1)
        thenHave(thesis) by RightImplies.withParameters(
          x ∈ D0,
          app(((f ∘ g) ∘ h))(x) === app((f ∘ (g ∘ h)))(x)
        )
      }

      thenHave(∀(x, x ∈ D0 ==> (app(((f ∘ g) ∘ h))(x) === app((f ∘ (g ∘ h)))(x)))) by RightForall
      thenHave(thesis) by Restate
    }

    have(((f ∘ g) ∘ h) === (f ∘ (g ∘ h))) by Tautology.from(
      BasicTheorems.extensionality of (f := ((f ∘ g) ∘ h), g := (f ∘ (g ∘ h)), A := D0),
      leftOn,
      rightOn,
      lastStep
    )
    thenHave(thesis) by Restate
  }

  val rightIdentity = Theorem(
    f :: A -> B |- (f ∘ Identity.id(A)) === f
  ) {
    val fTy = assume(f :: A -> B)
    have((Identity.id(A)) :: A -> A) by Tautology.from(Identity.typing of (A := A))
    val idTy = lastStep

    have((f ∘ Identity.id(A)) :: A -> B) by Tautology.from(typing of (f := f, g := Identity.id(A), A := A, B := B, C := A), fTy, idTy)
    val compTy = lastStep

    have(functionOn(f)(A)) by Tautology.from(BasicTheorems.functionBetweenIsFunctionOn of (f := f, A := A, B := B), fTy)
    val fOn = lastStep
    have(functionOn(f ∘ Identity.id(A))(A)) by Tautology.from(BasicTheorems.functionBetweenIsFunctionOn of (f := (f ∘ Identity.id(A)), A := A, B := B), compTy)
    val compOn = lastStep

    have(∀(x ∈ A, app(f ∘ Identity.id(A))(x) === app(f)(x))) subproof {
      have(x ∈ A ==> (app(f ∘ Identity.id(A))(x) === app(f)(x))) subproof {
        val xInA = assume(x ∈ A)
        val compApp = have(app(f ∘ Identity.id(A))(x) === app(f)(app(Identity.id(A))(x))) by Tautology.from(
          app_comp of (f := f, g := Identity.id(A), A := A, B := B, C := A, x := x),
          fTy,
          idTy,
          xInA
        )
        val idApp = have(app(Identity.id(A))(x) === x) by Tautology.from(Identity.app_id of (A := A, x := x), idTy, xInA)
        have(app(f ∘ Identity.id(A))(x) === app(f)(x)) by Congruence.from(compApp, idApp)
        thenHave(thesis) by RightImplies.withParameters(x ∈ A, app(f ∘ Identity.id(A))(x) === app(f)(x))
      }

      thenHave(∀(x, x ∈ A ==> (app(f ∘ Identity.id(A))(x) === app(f)(x)))) by RightForall
      thenHave(thesis) by Restate
    }

    have((f ∘ Identity.id(A)) === f) by Tautology.from(
      BasicTheorems.extensionality of (f := (f ∘ Identity.id(A)), g := f, A := A),
      compOn,
      fOn,
      lastStep
    )
    thenHave(thesis) by Restate
  }

  val leftIdentity = Theorem(
    f :: A -> B |- (Identity.id(B) ∘ f) === f
  ) {
    val fTy = assume(f :: A -> B)

    have((Identity.id(B)) :: B -> B) by Tautology.from(Identity.typing of (A := B))
    val idTy = lastStep

    have((Identity.id(B) ∘ f) :: A -> B) by Tautology.from(typing of (f := Identity.id(B), g := f, A := B, B := B, C := A), idTy, fTy)
    val compTy = lastStep

    have(functionOn(f)(A)) by Tautology.from(BasicTheorems.functionBetweenIsFunctionOn of (f := f, A := A, B := B), fTy)
    val fOn = lastStep
    have(functionOn(Identity.id(B) ∘ f)(A)) by Tautology.from(BasicTheorems.functionBetweenIsFunctionOn of (f := (Identity.id(B) ∘ f), A := A, B := B), compTy)
    val compOn = lastStep

    have(∀(x ∈ A, app(Identity.id(B) ∘ f)(x) === app(f)(x))) subproof {
      have(x ∈ A ==> (app(Identity.id(B) ∘ f)(x) === app(f)(x))) subproof {
        val xInA = assume(x ∈ A)
        val fxInB = have(app(f)(x) ∈ B) by Tautology.from(BasicTheorems.appTyping of (f := f, A := A, B := B, x := x), fTy, xInA)

        val compApp = have(app(Identity.id(B) ∘ f)(x) === app(Identity.id(B))(app(f)(x))) by Tautology.from(
          app_comp of (f := Identity.id(B), g := f, A := B, B := B, C := A, x := x),
          idTy,
          fTy,
          xInA
        )
        val idApp = have(app(Identity.id(B))(app(f)(x)) === app(f)(x)) by Tautology.from(
          Identity.app_id of (A := B, x := app(f)(x)),
          idTy,
          fxInB
        )
        have(app(Identity.id(B) ∘ f)(x) === app(f)(x)) by Congruence.from(compApp, idApp)
        thenHave(thesis) by RightImplies.withParameters(x ∈ A, app(Identity.id(B) ∘ f)(x) === app(f)(x))
      }

      thenHave(∀(x, x ∈ A ==> (app(Identity.id(B) ∘ f)(x) === app(f)(x)))) by RightForall
      thenHave(thesis) by Restate
    }

    have((Identity.id(B) ∘ f) === f) by Tautology.from(
      BasicTheorems.extensionality of (f := (Identity.id(B) ∘ f), g := f, A := A),
      compOn,
      fOn,
      lastStep
    )
    thenHave(thesis) by Restate
  }
}
