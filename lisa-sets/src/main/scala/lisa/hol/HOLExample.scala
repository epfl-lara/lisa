package lisa.hol
import lisa.utils.fol.FOL.{_, given}

/**
 * Example HOL theorems in Lisa, demonstrating multi-step proofs
 * combining primitive deduction rules.
 */
object HOLExample extends lisa.HOL {

  private val A = typevar
  private val B = typevar
  private val C = typevar

  private val x = typedvar(A)
  private val y = typedvar(A)
  private val z = typedvar(A)
  private val w = typedvar(A)

  private val d = typedvar(B)
  private val e = typedvar(C)

  private val f = typedvar(A ->: B)
  private val g = typedvar(A ->: B)

  private val p = typedvar(𝔹)
  private val q = typedvar(𝔹)
  private val r = typedvar(𝔹)

  // 1. Beta-normalisation chains

  /**
   * ⊢ (λx. (λx. y)(x))(y) = y
   */
  val doubleBeta = HOLTheorem(fun(x, fun(x, y) * x) * y =:= y) {
    val s1 = BETA(fun(x, fun(x, y) * x) * x)
    val s2 = INST(Seq((x, y)), s1)
    val s3 = BETA(fun(x, y) * x)
    val s4 = INST(Seq((x, y)), s3)
    TRANS(s2, s4)
  }

  /**
   * ⊢ (λx. (λy. y)(x))(z) = z
   */
  val composeId = HOLTheorem(fun(x, fun(y, y) * x) * z =:= z) {
    val s1 = BETA(fun(x, fun(y, y) * x) * x)
    val s2 = INST(Seq((x, z)), s1)
    val s3 = BETA(fun(y, y) * y)
    val s4 = INST(Seq((y, z)), s3)
    TRANS(s2, s4)
  }

  /**
   * ⊢ (λx. (λy. (λx. y))(x))(w) = (λx. w)
   */
  val multiBeta = HOLTheorem(fun(x, fun(y, fun(x, y)) * x) * w =:= fun(x, w)) {
    val b1 = BETA(fun(x, fun(y, fun(x, y)) * x) * x)
    val b1w = INST(Seq((x, w)), b1)
    val b2 = BETA(fun(y, fun(x, y)) * y)
    val b2w = INST(Seq((y, w)), b2)
    TRANS(b1w, b2w)
  }

  // 2. ABS + BETA: simplifying under a binder

  /**
   * ⊢ (λx. (λy. y)(x)) = (λx. x)
   */
  val betaUnderLambda = HOLTheorem(fun(x, fun(y, y) * x) =:= fun(x, x)) {
    val b = BETA(fun(y, y) * x)
    ABS(x)(b)
  }

  /**
   * ⊢ (λx. (λy. z)(x)) = (λx. z)
   */
  val constUnderLambda = HOLTheorem(fun(x, fun(y, z) * x) =:= fun(x, z)) {
    val b = BETA(fun(y, z) * x)
    ABS(x)(b)
  }

  /**
   * ⊢ (λx. λd. (λd. d)(d)) = (λx. λd. d)
   */
  val doubleAbs = HOLTheorem(fun(x, fun(d, fun(d, d) * d)) =:= fun(x, fun(d, d))) {
    val b = BETA(fun(d, d) * d)
    val abs1 = ABS(d)(b)
    ABS(x)(abs1)
  }

  // 3. MK_COMB + ABS: congruence under binders

  /**
   * f = g ⊢ (λx. f(x)) = (λx. g(x))
   */
  val congAbs = HOLTheorem((f =:= g) |- (fun(x, f * x) =:= fun(x, g * x))) {
    val h = HOLassume(f =:= g)
    val comb = MK_COMB(h, REFL(x))
    ABS(x)(comb)
  }

  /**
   * ⊢ (λx. (λx. f(x))(x)) = f — double eta-expansion round-trip.
   */
  val doubleEta = HOLTheorem(fun(x, fun(x, f * x) * x) =:= f) {
    val beta = BETA(fun(x, f * x) * x)
    val abs = ABS(x)(beta)
    val eta = ETA(x, f)
    TRANS(abs, eta)
  }

  // 4. Propositional reasoning via DEDUCT_ANTISYM_RULE + EQ_MP

  /**
   * (λp. q)(r) ⊢ q — modus ponens through beta.
   */
  val betaMP = HOLTheorem((fun(p, q) * r) |- q) {
    val beta = BETA(fun(p, q) * r)
    val h = HOLassume(fun(p, q) * r)
    EQ_MP(beta, h)
  }

  /**
   * ⊢ (λp. p)(p) = p
   */
  val boolBetaEq = HOLTheorem(fun(p, p) * p =:= p) {
    BETA(fun(p, p) * p)
  }

  /**
   * ⊢ p = p — via DEDUCT_ANTISYM_RULE.
   */
  val boolReflViaDeduct = HOLTheorem(p =:= p) {
    val h1 = ASSUME(p)
    DEDUCT_ANTISYM_RULE(h1, h1)
  }

  /**
   * q ⊢ q
   */
  val deductAndMP = HOLTheorem(q |- q) {
    val fwd = EQ_MP(BETA(fun(p, q) * r), HOLassume(fun(p, q) * r))
    ASSUME(q)
  }

}
