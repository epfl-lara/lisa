package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Algebra/Ring/Defs` (fragment).
 *
 * Set-based ring-like predicates on a carrier set `R` with set-coded operations.
 */
object Defs extends lisa.Main {

  val R = variable[Ind]

  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]

  val mul = variable[Ind]
  val one = variable[Ind]

  private val x0 = variable[Ind]
  private val y0 = variable[Ind]
  private val z0 = variable[Ind]

  private def addApp(add: Expr[Ind], a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def negApp(negOp: Expr[Ind], a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(negOp)(a)

  private def mulApp(mul: Expr[Ind], a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(mul)((a, b))

  val hasAdd = DEF(λ(R, λ(add, add :: (R × R) -> R)))
  val hasZero = DEF(λ(R, λ(zero, zero ∈ R)))
  val hasNeg = DEF(λ(R, λ(negOp, negOp :: R -> R)))

  val associativeAdd = DEF(
    λ(
      R,
      λ(
        add,
        forall(
          x0,
          (x0 ∈ R) ==>
            forall(
              y0,
              (y0 ∈ R) ==>
                forall(
                  z0,
                  (z0 ∈ R) ==>
                    (addApp(add, addApp(add, x0, y0), z0) === addApp(add, x0, addApp(add, y0, z0)))
                )
            )
        )
      )
    )
  )

  val commutativeAdd = DEF(
    λ(
      R,
      λ(
        add,
        forall(
          x0,
          (x0 ∈ R) ==> forall(y0, (y0 ∈ R) ==> (addApp(add, x0, y0) === addApp(add, y0, x0)))
        )
      )
    )
  )

  val leftZero = DEF(λ(R, λ(add, λ(zero, forall(x0, (x0 ∈ R) ==> (addApp(add, zero, x0) === x0))))))
  val rightZero = DEF(λ(R, λ(add, λ(zero, forall(x0, (x0 ∈ R) ==> (addApp(add, x0, zero) === x0))))))

  val leftNeg = DEF(
    λ(
      R,
      λ(
        add,
        λ(zero, λ(negOp, forall(x0, (x0 ∈ R) ==> (addApp(add, negApp(negOp, x0), x0) === zero))))
      )
    )
  )
  val rightNeg = DEF(
    λ(
      R,
      λ(
        add,
        λ(zero, λ(negOp, forall(x0, (x0 ∈ R) ==> (addApp(add, x0, negApp(negOp, x0)) === zero))))
      )
    )
  )

  val addSemigroup = DEF(λ(R, λ(add, hasAdd(R)(add) /\ associativeAdd(R)(add))))
  val addCommSemigroup = DEF(λ(R, λ(add, addSemigroup(R)(add) /\ commutativeAdd(R)(add))))

  val addMonoid = DEF(λ(R, λ(add, λ(zero, addSemigroup(R)(add) /\ hasZero(R)(zero) /\ leftZero(R)(add)(zero) /\ rightZero(R)(add)(zero)))))
  val addCommMonoid = DEF(λ(R, λ(add, λ(zero, addMonoid(R)(add)(zero) /\ commutativeAdd(R)(add)))))

  val addGroup = DEF(
    λ(
      R,
      λ(
        add,
        λ(
          zero,
          λ(
            negOp,
            addMonoid(R)(add)(zero) /\ hasNeg(R)(negOp) /\ leftNeg(R)(add)(zero)(negOp) /\ rightNeg(R)(add)(zero)(negOp)
          )
        )
      )
    )
  )

  val addCommGroup = DEF(λ(R, λ(add, λ(zero, λ(negOp, addGroup(R)(add)(zero)(negOp) /\ commutativeAdd(R)(add))))))

  val hasMul = DEF(λ(R, λ(mul, mul :: (R × R) -> R)))
  val hasOne = DEF(λ(R, λ(one, one ∈ R)))

  val associativeMul = DEF(
    λ(
      R,
      λ(
        mul,
        forall(
          x0,
          (x0 ∈ R) ==>
            forall(
              y0,
              (y0 ∈ R) ==>
                forall(
                  z0,
                  (z0 ∈ R) ==>
                    (mulApp(mul, mulApp(mul, x0, y0), z0) === mulApp(mul, x0, mulApp(mul, y0, z0)))
                )
            )
        )
      )
    )
  )

  val commutativeMul = DEF(
    λ(
      R,
      λ(
        mul,
        forall(
          x0,
          (x0 ∈ R) ==> forall(y0, (y0 ∈ R) ==> (mulApp(mul, x0, y0) === mulApp(mul, y0, x0)))
        )
      )
    )
  )

  val leftOne = DEF(λ(R, λ(mul, λ(one, forall(x0, (x0 ∈ R) ==> (mulApp(mul, one, x0) === x0))))))
  val rightOne = DEF(λ(R, λ(mul, λ(one, forall(x0, (x0 ∈ R) ==> (mulApp(mul, x0, one) === x0))))))

  val mulSemigroup = DEF(λ(R, λ(mul, hasMul(R)(mul) /\ associativeMul(R)(mul))))
  val mulMonoid = DEF(λ(R, λ(mul, λ(one, mulSemigroup(R)(mul) /\ hasOne(R)(one) /\ leftOne(R)(mul)(one) /\ rightOne(R)(mul)(one)))))

  val leftDistrib = DEF(
    λ(
      R,
      λ(
        add,
        λ(
          mul,
          forall(
            x0,
            (x0 ∈ R) ==>
              forall(
                y0,
                (y0 ∈ R) ==>
                  forall(
                    z0,
                    (z0 ∈ R) ==>
                      (mulApp(mul, x0, addApp(add, y0, z0)) ===
                        addApp(add, mulApp(mul, x0, y0), mulApp(mul, x0, z0)))
                  )
              )
          )
        )
      )
    )
  )

  val rightDistrib = DEF(
    λ(
      R,
      λ(
        add,
        λ(
          mul,
          forall(
            x0,
            (x0 ∈ R) ==>
              forall(
                y0,
                (y0 ∈ R) ==>
                  forall(
                    z0,
                    (z0 ∈ R) ==>
                      (mulApp(mul, addApp(add, x0, y0), z0) ===
                        addApp(add, mulApp(mul, x0, z0), mulApp(mul, y0, z0)))
                  )
              )
          )
        )
      )
    )
  )

  val distrib = DEF(λ(R, λ(add, λ(mul, leftDistrib(R)(add)(mul) /\ rightDistrib(R)(add)(mul)))))

  val ring = DEF(
    λ(
      R,
      λ(
        add,
        λ(
          zero,
          λ(
            negOp,
            λ(
              mul,
              λ(
                one,
                addCommGroup(R)(add)(zero)(negOp) /\ mulMonoid(R)(mul)(one) /\ distrib(R)(add)(mul)
              )
            )
          )
        )
      )
    )
  )
}
