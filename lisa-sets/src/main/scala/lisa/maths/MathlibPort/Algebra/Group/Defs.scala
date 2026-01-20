package lisa.maths.MathlibPort.Algebra.Group

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Group/Defs`.
 *
 * Set-based algebraic predicates built on LISA's set-theoretic notion of function.
 */
object Defs extends lisa.Main {

  val G = variable[Ind]
  val mul = variable[Ind]
  val one = variable[Ind]
  val inv = variable[Ind]

  private val x0 = variable[Ind]
  private val y0 = variable[Ind]
  private val z0 = variable[Ind]

  private def mulApp(m: Expr[Ind], a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(m)((a, b))

  private def invApp(i: Expr[Ind], a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(i)(a)

  val hasMul = DEF(λ(G, λ(mul, mul :: (G × G) -> G)))
  val hasOne = DEF(λ(G, λ(one, one ∈ G)))
  val hasInv = DEF(λ(G, λ(inv, inv :: G -> G)))

  val associative = DEF(
    λ(
      G,
      λ(
        mul,
        forall(
          x0,
          (x0 ∈ G) ==>
            forall(
              y0,
              (y0 ∈ G) ==>
                forall(
                  z0,
                  (z0 ∈ G) ==>
                    (mulApp(mul, mulApp(mul, x0, y0), z0) === mulApp(mul, x0, mulApp(mul, y0, z0)))
                )
            )
        )
      )
    )
  )

  val commutative = DEF(
    λ(
      G,
      λ(
        mul,
        forall(
          x0,
          (x0 ∈ G) ==> forall(y0, (y0 ∈ G) ==> (mulApp(mul, x0, y0) === mulApp(mul, y0, x0)))
        )
      )
    )
  )

  val leftIdentity = DEF(
    λ(G, λ(mul, λ(one, forall(x0, (x0 ∈ G) ==> (mulApp(mul, one, x0) === x0)))))
  )

  val rightIdentity = DEF(
    λ(G, λ(mul, λ(one, forall(x0, (x0 ∈ G) ==> (mulApp(mul, x0, one) === x0)))))
  )

  val leftInverse = DEF(
    λ(
      G,
      λ(
        mul,
        λ(one, λ(inv, forall(x0, (x0 ∈ G) ==> (mulApp(mul, invApp(inv, x0), x0) === one))))
      )
    )
  )

  val rightInverse = DEF(
    λ(
      G,
      λ(
        mul,
        λ(one, λ(inv, forall(x0, (x0 ∈ G) ==> (mulApp(mul, x0, invApp(inv, x0)) === one))))
      )
    )
  )

  val semigroup = DEF(λ(G, λ(mul, hasMul(G)(mul) /\ associative(G)(mul))))

  val commSemigroup = DEF(λ(G, λ(mul, semigroup(G)(mul) /\ commutative(G)(mul))))

  val monoid = DEF(
    λ(
      G,
      λ(
        mul,
        λ(
          one,
          semigroup(G)(mul) /\ hasOne(G)(one) /\ leftIdentity(G)(mul)(one) /\ rightIdentity(G)(mul)(one)
        )
      )
    )
  )

  val commMonoid = DEF(λ(G, λ(mul, λ(one, monoid(G)(mul)(one) /\ commutative(G)(mul)))))

  val group = DEF(
    λ(
      G,
      λ(
        mul,
        λ(
          one,
          λ(
            inv,
            monoid(G)(mul)(one) /\ hasInv(G)(inv) /\ leftInverse(G)(mul)(one)(inv) /\ rightInverse(G)(mul)(one)(inv)
          )
        )
      )
    )
  )

  val commGroup = DEF(λ(G, λ(mul, λ(one, λ(inv, group(G)(mul)(one)(inv) /\ commutative(G)(mul))))))
}

