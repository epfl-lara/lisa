package lisa.maths.MathlibPort.Algebra.Group

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

import Defs.{group, monoid}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Group/Hom`.
 *
 * Set-based monoid/group homomorphisms compatible with the structure predicates in [[Defs]].
 */
object HomSetLike extends lisa.Main {

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

  val monoidHom = DEF(
    λ(
      G,
      λ(
        mulG,
        λ(
          oneG,
          λ(
            H,
            λ(
              mulH,
              λ(
                oneH,
                λ(
                  f,
                  (f :: G -> H) /\
                    forall(
                      x,
                      x ∈ G ==>
                        forall(
                          y,
                          y ∈ G ==> (app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y)))
                        )
                    ) /\
                    (app(f, oneG) === oneH)
                )
              )
            )
          )
        )
      )
    )
  )

  val groupHom = DEF(
    λ(
      G,
      λ(
        mulG,
        λ(
          oneG,
          λ(
            invG,
            λ(
              H,
              λ(
                mulH,
                λ(
                  oneH,
                  λ(
                    invH,
                    λ(
                      f,
                      monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) /\
                        forall(x, x ∈ G ==> (app(f, invApp(invG, x)) === invApp(invH, app(f, x))))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

  val monoidHom_isFunction = Theorem(
    monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) |- (f :: G -> H)
  ) {
    have(thesis) by Tautology.from(monoidHom.definition)
  }

  val monoidHom_map_mul = Theorem(
    monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) |- forall(
      x,
      x ∈ G ==> forall(y, y ∈ G ==> (app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y))))
    )
  ) {
    have(thesis) by Tautology.from(monoidHom.definition)
  }

  val monoidHom_map_one = Theorem(
    monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f) |- (app(f, oneG) === oneH)
  ) {
    have(thesis) by Tautology.from(monoidHom.definition)
  }

  val groupHom_isMonoidHom = Theorem(
    groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f) |- monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f)
  ) {
    have(thesis) by Tautology.from(groupHom.definition)
  }

  val groupHom_map_inv = Theorem(
    groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f) |- forall(
      x,
      x ∈ G ==> (app(f, invApp(invG, x)) === invApp(invH, app(f, x)))
    )
  ) {
    have(thesis) by Tautology.from(groupHom.definition)
  }

  val monoidHom_comp = Theorem(
    (
      monoid(G)(mulG)(oneG),
      monoid(H)(mulH)(oneH),
      monoid(K0)(mulK0)(oneK0),
      monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f),
      monoidHom(H)(mulH)(oneH)(K0)(mulK0)(oneK0)(g)
    ) |- monoidHom(G)(mulG)(oneG)(K0)(mulK0)(oneK0)(g ∘ f)
  ) {
    val mG = assume(monoid(G)(mulG)(oneG))
    val mH = assume(monoid(H)(mulH)(oneH))
    val mK = assume(monoid(K0)(mulK0)(oneK0))
    val hf = assume(monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f))
    val hg = assume(monoidHom(H)(mulH)(oneH)(K0)(mulK0)(oneK0)(g))

    val fTy = have(f :: G -> H) by Tautology.from(monoidHom_isFunction, hf)
    val gTy = have(g :: H -> K0) by Tautology.from(
      monoidHom_isFunction of (G := H, H := K0, mulG := mulH, oneG := oneH, mulH := mulK0, oneH := oneK0, f := g),
      hg
    )

    have((g ∘ f) :: G -> K0) by Tautology.from(
      Functions.Operations.Composition.typing of (f := g, g := f, A := H, B := K0, C := G),
      gTy,
      fTy
    )
    val compTy = lastStep

    val fMapMul = have(forall(x, x ∈ G ==> forall(y, y ∈ G ==> (app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y)))))) by Tautology.from(
      monoidHom_map_mul,
      hf
    )
    val fMapOne = have(app(f, oneG) === oneH) by Tautology.from(monoidHom_map_one, hf)

    val gMapMul = have(forall(x, x ∈ H ==> forall(y, y ∈ H ==> (app(g, mulApp(mulH, x, y)) === mulApp(mulK0, app(g, x), app(g, y)))))) by Tautology.from(
      monoidHom_map_mul of (G := H, H := K0, mulG := mulH, oneG := oneH, mulH := mulK0, oneH := oneK0, f := g),
      hg
    )
    val gMapOne = have(app(g, oneH) === oneK0) by Tautology.from(
      monoidHom_map_one of (G := H, H := K0, mulG := mulH, oneG := oneH, mulH := mulK0, oneH := oneK0, f := g),
      hg
    )

    import BasicTheoremsSetLike.{G => G1, mul => mul1, one => one1}
    val oneGInG = have(oneG ∈ G) by Tautology.from(
      BasicTheoremsSetLike.one_mem_of_monoid of (G1 := G, mul1 := mulG, one1 := oneG),
      mG
    )

    have(
      forall(
        x,
        x ∈ G ==>
          forall(
            y,
            y ∈ G ==>
              (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y)))
          )
      )
    ) subproof {
      have(
        x ∈ G ==>
          forall(
            y,
            y ∈ G ==> (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y)))
          )
      ) subproof {
        val xInG = assume(x ∈ G)

        have(
          forall(
            y,
            y ∈ G ==> (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y)))
          )
        ) subproof {
          have(
            y ∈ G ==> (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y)))
          ) subproof {
            val yInG = assume(y ∈ G)

            val hasMulG = have(Defs.hasMul(G)(mulG)) by Tautology.from(
              Defs.monoid.definition of (Defs.G := G, Defs.mul := mulG, Defs.one := oneG),
              Defs.semigroup.definition of (Defs.G := G, Defs.mul := mulG),
              mG
            )
            import BasicTheoremsSetLike.{G => G2, mul => mul2, x => x2, y => y2}
            val xyInG = have(mulApp(mulG, x, y) ∈ G) by Tautology.from(
              BasicTheoremsSetLike.mul_closed of (G2 := G, mul2 := mulG, x2 := x, y2 := y),
              hasMulG,
              xInG,
              yInG
            )

            val compAtXY = have(app(g ∘ f, mulApp(mulG, x, y)) === app(g, app(f, mulApp(mulG, x, y)))) by Tautology.from(
              Functions.Operations.Composition.app_comp of (f := g, g := f, A := H, B := K0, C := G, x := mulApp(mulG, x, y)),
              gTy,
              fTy,
              xyInG
            )

            val fxInH = have(app(f, x) ∈ H) by Tautology.from(Functions.BasicTheorems.appTyping of (f := f, A := G, B := H, x := x), fTy, xInG)
            val fyInH = have(app(f, y) ∈ H) by Tautology.from(Functions.BasicTheorems.appTyping of (f := f, A := G, B := H, x := y), fTy, yInG)

            val fMapMulAtX = have(forall(y, y ∈ G ==> (app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y))))) by Tautology.from(
              fMapMul of x,
              xInG
            )
            val fMul = have(app(f, mulApp(mulG, x, y)) === mulApp(mulH, app(f, x), app(f, y))) by Tautology.from(fMapMulAtX of y, yInG)

            val gMapMulAtFx = have(forall(y, y ∈ H ==> (app(g, mulApp(mulH, app(f, x), y)) === mulApp(mulK0, app(g, app(f, x)), app(g, y))))) by Tautology.from(
              gMapMul of app(f, x),
              fxInH
            )
            val gMul = have(app(g, mulApp(mulH, app(f, x), app(f, y))) === mulApp(mulK0, app(g, app(f, x)), app(g, app(f, y)))) by Tautology.from(
              gMapMulAtFx of app(f, y),
              fyInH
            )

            val compAtX = have(app(g ∘ f, x) === app(g, app(f, x))) by Tautology.from(
              Functions.Operations.Composition.app_comp of (f := g, g := f, A := H, B := K0, C := G, x := x),
              gTy,
              fTy,
              xInG
            )
            val compAtY = have(app(g ∘ f, y) === app(g, app(f, y))) by Tautology.from(
              Functions.Operations.Composition.app_comp of (f := g, g := f, A := H, B := K0, C := G, x := y),
              gTy,
              fTy,
              yInG
            )

            have(app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y))) by Congruence.from(
              compAtXY,
              fMul,
              gMul,
              compAtX,
              compAtY
            )
            thenHave(thesis) by RightImplies.withParameters(
              y ∈ G,
              app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y))
            )
          }

          thenHave(thesis) by RightForall.withParameters(
            y ∈ G ==> (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y))),
            y
          )
        }

        thenHave(thesis) by RightImplies.withParameters(
          x ∈ G,
          forall(
            y,
            y ∈ G ==> (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y)))
          )
        )
      }

      thenHave(thesis) by RightForall.withParameters(
        x ∈ G ==>
          forall(
            y,
            y ∈ G ==> (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y)))
          ),
        x
      )
    }
    val mapMul = lastStep

    val compAtOne = have(app(g ∘ f, oneG) === app(g, app(f, oneG))) by Tautology.from(
      Functions.Operations.Composition.app_comp of (f := g, g := f, A := H, B := K0, C := G, x := oneG),
      gTy,
      fTy,
      oneGInG
    )
    val mapOne = have(app(g ∘ f, oneG) === oneK0) by Congruence.from(compAtOne, fMapOne, gMapOne)

    have(
      ((g ∘ f) :: G -> K0) /\
        forall(
          x,
          x ∈ G ==>
            forall(
              y,
              y ∈ G ==>
                (app(g ∘ f, mulApp(mulG, x, y)) === mulApp(mulK0, app(g ∘ f, x), app(g ∘ f, y)))
            )
        ) /\
        (app(g ∘ f, oneG) === oneK0)
    ) by Tautology.from(compTy, mapMul, mapOne)
    thenHave(thesis) by Substitute(
      monoidHom.definition of (H := K0, mulH := mulK0, oneH := oneK0, f := (g ∘ f))
    )
  }

  val groupHom_comp = Theorem(
    (
      group(G)(mulG)(oneG)(invG),
      group(H)(mulH)(oneH)(invH),
      group(K0)(mulK0)(oneK0)(invK0),
      groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f),
      groupHom(H)(mulH)(oneH)(invH)(K0)(mulK0)(oneK0)(invK0)(g)
    ) |- groupHom(G)(mulG)(oneG)(invG)(K0)(mulK0)(oneK0)(invK0)(g ∘ f)
  ) {
    val gG = assume(group(G)(mulG)(oneG)(invG))
    val gH = assume(group(H)(mulH)(oneH)(invH))
    val gK = assume(group(K0)(mulK0)(oneK0)(invK0))
    val hf = assume(groupHom(G)(mulG)(oneG)(invG)(H)(mulH)(oneH)(invH)(f))
    val hg = assume(groupHom(H)(mulH)(oneH)(invH)(K0)(mulK0)(oneK0)(invK0)(g))

    val mG = have(monoid(G)(mulG)(oneG)) by Tautology.from(
      Defs.group.definition of (Defs.G := G, Defs.mul := mulG, Defs.one := oneG, Defs.inv := invG),
      gG
    )
    val mH = have(monoid(H)(mulH)(oneH)) by Tautology.from(
      Defs.group.definition of (Defs.G := H, Defs.mul := mulH, Defs.one := oneH, Defs.inv := invH),
      gH
    )
    val mK = have(monoid(K0)(mulK0)(oneK0)) by Tautology.from(
      Defs.group.definition of (Defs.G := K0, Defs.mul := mulK0, Defs.one := oneK0, Defs.inv := invK0),
      gK
    )

    val hfM = have(monoidHom(G)(mulG)(oneG)(H)(mulH)(oneH)(f)) by Tautology.from(groupHom_isMonoidHom, hf)
    val hgM = have(monoidHom(H)(mulH)(oneH)(K0)(mulK0)(oneK0)(g)) by Tautology.from(
      groupHom_isMonoidHom of (G := H, H := K0, mulG := mulH, oneG := oneH, invG := invH, mulH := mulK0, oneH := oneK0, invH := invK0, f := g),
      hg
    )

    have(monoidHom(G)(mulG)(oneG)(K0)(mulK0)(oneK0)(g ∘ f)) by Tautology.from(monoidHom_comp, mG, mH, mK, hfM, hgM)
    val compMonoid = lastStep

    val fTy = have(f :: G -> H) by Tautology.from(monoidHom_isFunction, hfM)
    val gTy = have(g :: H -> K0) by Tautology.from(
      monoidHom_isFunction of (G := H, H := K0, mulG := mulH, oneG := oneH, mulH := mulK0, oneH := oneK0, f := g),
      hgM
    )

    val invMapF = have(forall(x, x ∈ G ==> (app(f, invApp(invG, x)) === invApp(invH, app(f, x))))) by Tautology.from(groupHom_map_inv, hf)
    val invMapG = have(forall(x, x ∈ H ==> (app(g, invApp(invH, x)) === invApp(invK0, app(g, x))))) by Tautology.from(
      groupHom_map_inv of (G := H, H := K0, mulG := mulH, oneG := oneH, invG := invH, mulH := mulK0, oneH := oneK0, invH := invK0, f := g),
      hg
    )

    have(forall(x, x ∈ G ==> (app(g ∘ f, invApp(invG, x)) === invApp(invK0, app(g ∘ f, x))))) subproof {
      have(x ∈ G ==> (app(g ∘ f, invApp(invG, x)) === invApp(invK0, app(g ∘ f, x)))) subproof {
        val xInG = assume(x ∈ G)

        import BasicTheoremsSetLike.{G => G3, mul => mul3, one => one3, inv => inv3}
        val invMem = have(forall(x, x ∈ G ==> (invApp(invG, x) ∈ G))) by Tautology.from(
          BasicTheoremsSetLike.inv_mem_of_group of (G3 := G, mul3 := mulG, one3 := oneG, inv3 := invG),
          gG
        )
        val invxInG = have(invApp(invG, x) ∈ G) by Tautology.from(invMem of x, xInG)

        val compAtInv = have(app(g ∘ f, invApp(invG, x)) === app(g, app(f, invApp(invG, x)))) by Tautology.from(
          Functions.Operations.Composition.app_comp of (f := g, g := f, A := H, B := K0, C := G, x := invApp(invG, x)),
          gTy,
          fTy,
          invxInG
        )

        val fInv = have(app(f, invApp(invG, x)) === invApp(invH, app(f, x))) by Tautology.from(invMapF of x, xInG)

        val fxInH = have(app(f, x) ∈ H) by Tautology.from(Functions.BasicTheorems.appTyping of (f := f, A := G, B := H, x := x), fTy, xInG)
        val gInv = have(app(g, invApp(invH, app(f, x))) === invApp(invK0, app(g, app(f, x)))) by Tautology.from(invMapG of app(f, x), fxInH)

        val compAtX = have(app(g ∘ f, x) === app(g, app(f, x))) by Tautology.from(
          Functions.Operations.Composition.app_comp of (f := g, g := f, A := H, B := K0, C := G, x := x),
          gTy,
          fTy,
          xInG
        )

        have(app(g ∘ f, invApp(invG, x)) === invApp(invK0, app(g ∘ f, x))) by Congruence.from(compAtInv, fInv, gInv, compAtX)
        thenHave(thesis) by RightImplies.withParameters(
          x ∈ G,
          app(g ∘ f, invApp(invG, x)) === invApp(invK0, app(g ∘ f, x))
        )
      }

      thenHave(thesis) by RightForall.withParameters(
        x ∈ G ==> (app(g ∘ f, invApp(invG, x)) === invApp(invK0, app(g ∘ f, x))),
        x
      )
    }
    val mapInv = lastStep

    have(
      monoidHom(G)(mulG)(oneG)(K0)(mulK0)(oneK0)(g ∘ f) /\
        forall(x, x ∈ G ==> (app(g ∘ f, invApp(invG, x)) === invApp(invK0, app(g ∘ f, x))))
    ) by Tautology.from(compMonoid, mapInv)
    thenHave(thesis) by Substitute(
      groupHom.definition of (H := K0, mulH := mulK0, oneH := oneK0, invH := invK0, f := (g ∘ f))
    )
  }

  val monoidHom_id = Theorem(
    monoid(G)(mulG)(oneG) |- monoidHom(G)(mulG)(oneG)(G)(mulG)(oneG)(Identity.id(G))
  ) {
    val mG = assume(monoid(G)(mulG)(oneG))

    have(Identity.id(G) :: G -> G) by Tautology.from(Functions.Operations.Identity.typing of (A := G))
    val idTy = lastStep

    import BasicTheoremsSetLike.{G => G1, mul => mul1, one => one1}
    val oneInG = have(oneG ∈ G) by Tautology.from(BasicTheoremsSetLike.one_mem_of_monoid of (G1 := G, mul1 := mulG, one1 := oneG), mG)

    val hasMulG = have(Defs.hasMul(G)(mulG)) by Tautology.from(
      Defs.monoid.definition of (Defs.G := G, Defs.mul := mulG, Defs.one := oneG),
      Defs.semigroup.definition of (Defs.G := G, Defs.mul := mulG),
      mG
    )

    have(
      forall(
        x,
        x ∈ G ==>
          forall(
            y,
            y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y)))
          )
      )
    ) subproof {
      have(
        x ∈ G ==>
          forall(
            y,
            y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y)))
          )
      ) subproof {
        val xInG = assume(x ∈ G)

        have(
          forall(
            y,
            y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y)))
          )
        ) subproof {
          have(
            y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y)))
          ) subproof {
            val yInG = assume(y ∈ G)

            import BasicTheoremsSetLike.{G => G2, mul => mul2, x => x2, y => y2}
            val xyInG = have(mulApp(mulG, x, y) ∈ G) by Tautology.from(
              BasicTheoremsSetLike.mul_closed of (G2 := G, mul2 := mulG, x2 := x, y2 := y),
              hasMulG,
              xInG,
              yInG
            )

            val idXY = have(app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, x, y)) by Tautology.from(
              Functions.Operations.Identity.app_id of (A := G, x := mulApp(mulG, x, y)),
              idTy,
              xyInG
            )

            val idx = have(app(Identity.id(G), x) === x) by Tautology.from(
              Functions.Operations.Identity.app_id of (A := G, x := x),
              idTy,
              xInG
            )
            val idy = have(app(Identity.id(G), y) === y) by Tautology.from(
              Functions.Operations.Identity.app_id of (A := G, x := y),
              idTy,
              yInG
            )

            have(app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y))) by Congruence.from(
              idXY,
              idx,
              idy
            )
            thenHave(thesis) by RightImplies.withParameters(
              y ∈ G,
              app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y))
            )
          }

          thenHave(thesis) by RightForall.withParameters(
            y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y))),
            y
          )
        }

        thenHave(thesis) by RightImplies.withParameters(
          x ∈ G,
          forall(
            y,
            y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y)))
          )
        )
      }

      thenHave(thesis) by RightForall.withParameters(
        x ∈ G ==>
          forall(
            y,
            y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y)))
          ),
        x
      )
    }
    val mapMul = lastStep

    val mapOne = have(app(Identity.id(G), oneG) === oneG) by Tautology.from(
      Functions.Operations.Identity.app_id of (A := G, x := oneG),
      idTy,
      oneInG
    )

    have(
      (Identity.id(G) :: G -> G) /\
        forall(
          x,
          x ∈ G ==>
            forall(
              y,
              y ∈ G ==> (app(Identity.id(G), mulApp(mulG, x, y)) === mulApp(mulG, app(Identity.id(G), x), app(Identity.id(G), y)))
            )
        ) /\
        (app(Identity.id(G), oneG) === oneG)
    ) by Tautology.from(idTy, mapMul, mapOne)
    thenHave(thesis) by Substitute(
      monoidHom.definition of (H := G, mulH := mulG, oneH := oneG, f := Identity.id(G))
    )
  }

  val groupHom_id = Theorem(
    group(G)(mulG)(oneG)(invG) |- groupHom(G)(mulG)(oneG)(invG)(G)(mulG)(oneG)(invG)(Identity.id(G))
  ) {
    val gG = assume(group(G)(mulG)(oneG)(invG))
    val mG = have(monoid(G)(mulG)(oneG)) by Tautology.from(
      Defs.group.definition of (Defs.G := G, Defs.mul := mulG, Defs.one := oneG, Defs.inv := invG),
      gG
    )

    val idMonoid = have(monoidHom(G)(mulG)(oneG)(G)(mulG)(oneG)(Identity.id(G))) by Tautology.from(monoidHom_id, mG)
    val idTy = have(Identity.id(G) :: G -> G) by Tautology.from(Functions.Operations.Identity.typing of (A := G))

    import BasicTheoremsSetLike.{G => G3, mul => mul3, one => one3, inv => inv3}
    val invMem = have(forall(x, x ∈ G ==> (invApp(invG, x) ∈ G))) by Tautology.from(
      BasicTheoremsSetLike.inv_mem_of_group of (G3 := G, mul3 := mulG, one3 := oneG, inv3 := invG),
      gG
    )

    have(forall(x, x ∈ G ==> (app(Identity.id(G), invApp(invG, x)) === invApp(invG, app(Identity.id(G), x))))) subproof {
      have(x ∈ G ==> (app(Identity.id(G), invApp(invG, x)) === invApp(invG, app(Identity.id(G), x)))) subproof {
        val xInG = assume(x ∈ G)
        val invxInG = have(invApp(invG, x) ∈ G) by Tautology.from(invMem of x, xInG)

        val idInv = have(app(Identity.id(G), invApp(invG, x)) === invApp(invG, x)) by Tautology.from(
          Functions.Operations.Identity.app_id of (A := G, x := invApp(invG, x)),
          idTy,
          invxInG
        )
        val idx = have(app(Identity.id(G), x) === x) by Tautology.from(
          Functions.Operations.Identity.app_id of (A := G, x := x),
          idTy,
          xInG
        )

        have(app(Identity.id(G), invApp(invG, x)) === invApp(invG, app(Identity.id(G), x))) by Congruence.from(idInv, idx)
        thenHave(thesis) by RightImplies.withParameters(
          x ∈ G,
          app(Identity.id(G), invApp(invG, x)) === invApp(invG, app(Identity.id(G), x))
        )
      }

      thenHave(thesis) by RightForall.withParameters(
        x ∈ G ==> (app(Identity.id(G), invApp(invG, x)) === invApp(invG, app(Identity.id(G), x))),
        x
      )
    }
    val mapInv = lastStep

    have(
      monoidHom(G)(mulG)(oneG)(G)(mulG)(oneG)(Identity.id(G)) /\
        forall(x, x ∈ G ==> (app(Identity.id(G), invApp(invG, x)) === invApp(invG, app(Identity.id(G), x))))
    ) by Tautology.from(idMonoid, mapInv)
    thenHave(thesis) by Substitute(
      groupHom.definition of (H := G, mulH := mulG, oneH := oneG, invH := invG, f := Identity.id(G))
    )
  }

}
