package lisa.maths.MathlibPort.Algebra.Group

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Group/Hom`.
 *
 * A minimal set-based notion of monoid/group homomorphisms.
 */
object Hom extends lisa.Main {

  val G = variable[Ind]
  val H = variable[Ind]
  val K0 = variable[Ind]

  val mulG = variable[Ind]
  val oneG = variable[Ind]
  val invG = variable[Ind]

  val mulH = variable[Ind]
  val oneH = variable[Ind]
  val invH = variable[Ind]

  val mulK0 = variable[Ind]
  val oneK0 = variable[Ind]
  val invK0 = variable[Ind]

  val f = variable[Ind]
  val g = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]

  private def mulApp(mul: Expr[Ind], a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  private def invApp(inv: Expr[Ind], a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(inv)(a)

  private def app(h: Expr[Ind], a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(h)(a)

  val monoidHom = DEF(λ(G, λ(mulG, λ(oneG, λ(H, λ(mulH, λ(oneH, λ(f,
    (f :: G -> H) /\
      forall(x, x ∈ G ==> forall(y, y ∈ G ==> (app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y))))) /\
      (app(f, oneG) === oneH)
  ))))))))

  val groupHom = DEF(λ(G, λ(mulG, λ(oneG, λ(invG, λ(H, λ(mulH, λ(oneH, λ(invH, λ(f,
    monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) /\
      forall(x, x ∈ G ==> (app(f, invApp(invG, x)) === invApp(invH, app(f, x))))
  ))))))))))

  val monoidHom_map_mul = Theorem(
    monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) |- forall(x, x ∈ G ==> forall(y, y ∈ G ==> (app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y)))))
  ) {
    have(thesis) by Tautology.from(monoidHom.definition)
  }

  val monoidHom_map_one = Theorem(
    monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) |- app(f, oneG) === oneH
  ) {
    have(thesis) by Tautology.from(monoidHom.definition)
  }

  val monoidHom_isFunction = Theorem(
    monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) |- (f :: G -> H)
  ) {
    have(thesis) by Tautology.from(monoidHom.definition)
  }

  val groupHom_isMonoidHom = Theorem(
    groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f) |- monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f)
  ) {
    have(thesis) by Tautology.from(groupHom.definition)
  }

  val groupHom_map_mul = Theorem(
    groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f) |- forall(x, x ∈ G ==> forall(y, y ∈ G ==> (app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y)))))
  ) {
    val gh = assume(groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f))
    have(monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f)) by Tautology.from(groupHom_isMonoidHom, gh)
    have(thesis) by Tautology.from(monoidHom_map_mul, lastStep)
  }

  val groupHom_map_one = Theorem(
    groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f) |- (app(f, oneG) === oneH)
  ) {
    val gh = assume(groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f))
    have(monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f)) by Tautology.from(groupHom_isMonoidHom, gh)
    have(thesis) by Tautology.from(monoidHom_map_one, lastStep)
  }

  val groupHom_map_inv = Theorem(
    groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f) |- forall(x, x ∈ G ==> (app(f, invApp(invG, x)) === invApp(invH, app(f, x))))
  ) {
    have(thesis) by Tautology.from(groupHom.definition)
  }
}
