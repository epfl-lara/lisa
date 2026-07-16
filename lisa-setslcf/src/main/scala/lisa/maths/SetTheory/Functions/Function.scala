package lisa.maths.SetTheory.Functions

import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations.Predef._
import lisa.maths.SetTheory.Relations.Relation

/**
 * A function `f : A -> B` is a relation `f ⊆ A × B` such that for any
 * `x ∈ A` there is a unique `y ∈ B` such that `(x, y) ∈ f`.
 */
object Function extends lisa.Main {

  private val T, T1 = variable[Ind]
  private val e = variable[Ind >>: Ind]

  /**
   * Definition --- `f : A -> B` is a function between `A` and `B` if `f ⊆ A × B`
   * such that for all `x ∈ A` there is a unique `y ∈ B` such that `(x, y) ∈ f`.
   */
  val functionBetween = DEF(λ(f, λ(A, λ(B, relationBetween(f)(A)(B) /\ ∀(x ∈ A, ∃!(y, (x, y) ∈ f))))))

  /**
   * Definition --- `f` is a function on `A` if the domain of `f` is `A`.
   */
  val functionOn = DEF(λ(f, λ(A, ∃(B, functionBetween(f)(A)(B)))))

  /**
   * Definition --- `f` is a function if there exists `A` and `B` such that `f : A -> B`.
   */
  val function = DEF(λ(f, ∃(A, ∃(B, functionBetween(f)(A)(B)))))

  /**
   * Function domain --- The domain of `f` is the set of elements that have a mapped value.
   *
   * @see [[Relation.dom]]
   */
  export Relation.dom

  /**
   * Function range --- The range of `f` is the set of elements that are mapped
   * by (at least) one value.
   *
   * @see [[Relation.dom]]
   */
  export Relation.range

  /**
   * Function application --- For any `x`, we denote by `f(x)` the application
   * of `f` to `x`.
   *
   * If `x ∉ A`, this value is undefined.
   */
  val app = DEF(λ(f, λ(x, ε(y, (x, y) ∈ f)))).printAs(args => {
    val f = args(0)
    val x = args(1)
    s"$f($x)"
  })

  /*
//TODO revisit later
  /**
   * Computes the list of consecutively applied arguments of an expression, including through the small `app`.
   * Example:
   * {{{
   * unfoldAllApp(Abs(x, f(x))(a)(b)(c)) == (Abs(x, f(x)), List(a, b, c))
   *
   * @param e
   * @return
   */
  def unfoldAllAppAndSmallapp(e: Expr[?]): (Expr[?], List[Expr[?]]) =
    def rec(e: Expr[?]): (Expr[?], List[Expr[?]]) = e match
      case App(App(`app`, f), g) =>
        val (f1, args) = rec(f)
        (f1, g :: args)
      case App(f, arg) =>
        val (f1, args) = rec(f)
        (f1, arg :: args)
      case _ => (e, Nil)
    val (f, args) = rec(e)
    (f, args.reverse)

  {
    def appPrint(args: Seq[Expr[?]]): String =
      args match
        case Nil       => ""
        case func :: Nil => s"$this($func)"
        case func :: rest => func.mkString(args)

    app.printAs(args => appPrint(args))
  }

   */

  /**
   * Implicit conversion enabling the function application syntax `f(x)` for set-theoretic terms.
   *
   * This allows writing `f(x)` directly instead of using the explicit `app(f)(x)` combinator,
   * aligning the code syntax with the printed notation.
   *
   * To use this notation, import it as follows:
   * {{{
   * import lisa.maths.SetTheory.Functions.Predef.given
   * }}}
   */
  class AppliableTerm(val f: Expr[Ind]) extends AnyVal:
    def apply(arg1: Expr[Ind], args: Expr[Ind]*): Expr[Ind] =
      args.foldLeft(app(f)(arg1))((acc, arg) => app(acc)(arg))

  given Conversion[Expr[Ind], AppliableTerm] = AppliableTerm(_)

  /**
   * Injective function --- `f` is said to be injective on `A` if `f(x) = f(y)` implies `x = y`.
   */
  val injective = DEF(λ(f, λ(A, ∀(x ∈ A, ∀(y ∈ A, (f(x) === f(y)) ==> (x === y))))))
  inline def oneToOne = injective

  /**
   * Surjective function --- `f` is said to be surjective on (or onto) `B` if `range(f) = B`.
   */
  val surjective = DEF(λ(f, λ(B, range(f) === B)))
  inline def onto = surjective

  /**
   * Bijective function --- `f : A -> B` is said to be bijective if is both injective
   * and surjective.
   */
  val bijective = DEF(λ(f, λ(A, λ(B, (functionBetween(f)(A)(B)) /\ injective(f)(A) /\ surjective(f)(B)))))

  val abs: Constant[Ind >>: (Ind >>: Ind) >>: Ind] = DEF(λ(T, λ(e, { (x, e(x)) | x ∈ T })))
    .printAs(args =>
      val typ = args(0)
      val (v, body) = args(1) match
        case Abs(v, b) => (v, b)
        case _ => (x, args(1))
      s"λ($v: $typ). $body"
    )

  // Pattern extractor for the 'abs' Shallow Embedding constant.
  // It allows matching expressions of the form abs(typ)(body) using the pattern Sabs(typ, body).
  object Sabs:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind >>: Ind])] =
      e match
        // We match against the specific Constant 'abs' being applied twice: App(App(abs, typ), body)
        case App(App(`abs`, typ), body) =>
          Some((typ.asInstanceOf[Expr[Ind]], body.asInstanceOf[Expr[Ind >>: Ind]]))
        case _ => None

}
