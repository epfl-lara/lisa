package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.Functions.Pi.Pi
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingTheorems.arrowElim
import lisa.maths.SetTheory.Types.TypingRules.TAbs

object FunctionAbstractions {

  private val domainVar = variable[Ind]("domain")
  private val codomainVar = variable[Ind]("codomain")
  private val bodyVar = variable[Ind >>: Ind]("body")
  private val pointVar = variable[Ind]("point")

  def nestedAbstraction(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      body: Expr[Ind]
  ): Expr[Ind] =
    signature.reverse.foldLeft(body) { case (acc, (v, domain)) =>
      TypingHelpers.fun(v :: domain, acc)
    }

  private lazy val TAbsConstOnGeneral: THM = Lemma(
    ∀(pointVar ∈ domainVar, bodyVar(pointVar) ∈ codomainVar) |- abs(domainVar)(bodyVar) ∈ Pi(
      domainVar
    )(λ(x, codomainVar))
  ) {
    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val e = variable[Ind >>: Ind]

    assume(∀(pointVar ∈ domainVar, bodyVar(pointVar) ∈ codomainVar))
    val premiseAtX = have(pointVar ∈ domainVar ==> bodyVar(pointVar) ∈ codomainVar) by InstantiateForall
    have(pointVar ∈ domainVar ==> bodyVar(pointVar) ∈ λ(x, codomainVar)(pointVar)) by
      Tautology.from(premiseAtX)
    thenHave(∀(pointVar ∈ domainVar, bodyVar(pointVar) ∈ λ(x, codomainVar)(pointVar))) by RightForall
    have(thesis) by Tautology.from(lastStep, TAbs of (T1 := domainVar, T2 := λ(x, codomainVar), e := bodyVar))
  }

  def TAbsConstOn(
      domain: Expr[Ind],
      codomain: Expr[Ind],
      body: Expr[Ind >>: Ind]
  ): THM = Lemma(
    ∀(pointVar ∈ domain, body(pointVar) ∈ codomain) |- abs(domain)(body) ∈ Pi(domain)(λ(pointVar, codomain))
  ) {
    have(thesis) by Tautology.from(
      TAbsConstOnGeneral.of(
        domainVar := domain,
        codomainVar := codomain,
        bodyVar := body
      )
    )
  }

  // Function extensionality phrased directly on the function-space membership form (`f ∈ (A ->: B)`,
  // i.e. `f :: (A ->: B)`), so callers in this form need no per-use `functionBetween` conversion.
  private lazy val funcExtInFuncSpace: THM = Lemma(
    (f ∈ (A ->: B), g ∈ (A ->: B), ∀(x, (x ∈ A) ==> (f * x === g * x))) |- (f === g)
  ) {
    have(thesis) by Tautology.from(
      BasicTheorems.functionalExtentionality,
      BasicTheorems.funcBetweenEqInFuncSpace,
      BasicTheorems.funcBetweenEqInFuncSpace of (f := g)
    )
  }

  /**
   * Curried extensionality specialised to the case where `left` and `right` both reduce, on every
   * well-typed argument tuple, to the *same* `commonValue`. Taking the two reduction schemas
   * directly (rather than a pre-combined "they agree" schema) lets the single instantiation at the
   * fresh points happen here, instead of being done once by the caller and again inside this lemma.
   */
  def curriedCommonValue(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      resultType: Expr[Ind],
      left: Expr[Ind],
      right: Expr[Ind],
      commonValue: Expr[Ind]
  ): THM = {
    val vars = signature.map(_._1)
    val domains = signature.map(_._2)
    val n = signature.size

    // Type of `left`/`right` once their first `k` arguments have been supplied.
    def suffixType(k: Int): Expr[Ind] =
      domains.drop(k).foldRight[Expr[Ind]](resultType)(_ ->: _)

    val finalType = suffixType(0)
    // Built through a fresh placeholder and a capture-avoiding substitution, so the schema matches
    // the caller's even when `fn`'s name clashes with one of the bound argument variables.
    def schemaFor(fn: Expr[Ind]): Expr[Prop] =
      val placeholder = variable[Ind]("curriedfn")
      forallSeq(vars, wellTypedFormula(signature) ==> (appSeq(placeholder)(vars) === commonValue)).substitute(placeholder := fn)
    val leftSchema = schemaFor(left)
    val rightSchema = schemaFor(right)

    // One fresh point per argument position, and the partial applications they induce.
    val points = signature.indices.map(i => variable[Ind](s"pointarg$i"))
    val pointTyped = points.zip(domains).map((p, d) => (p :: d): Expr[Prop])
    def leftAt(k: Int): Expr[Ind] = appSeq(left)(points.take(k))
    def rightAt(k: Int): Expr[Ind] = appSeq(right)(points.take(k))

    Lemma((left :: finalType, right :: finalType, leftSchema, rightSchema) |- (left === right)) {
      assume(left :: finalType, right :: finalType, leftSchema, rightSchema)

      // Typing of the partial applications: under the first `k` points being well-typed,
      // `leftAt(k)`/`rightAt(k) :: suffixType(k)`, by repeated arrow elimination.
      def typingChain(fun: Int => Expr[Ind]) =
        (1 to n).foldLeft(Vector(have(fun(0) :: finalType) by Restate)) { (chain, k) =>
          chain :+ (have(pointTyped.take(k) |- (fun(k) :: suffixType(k))) by Tautology.from(
            chain(k - 1),
            arrowElim of (f := fun(k - 1), a := domains(k - 1), b := suffixType(k), x := points(k - 1))
          ))
        }
      val leftTyped = typingChain(leftAt)
      val rightTyped = typingChain(rightAt)

      // Base case: instantiating each schema at the points shows both sides reduce to the same
      // `commonValue`, hence agree there.
      val pointSubst = vars.zip(points).map((v, p) => v := p)
      val commonAt = commonValue.substitute(pointSubst*).asInstanceOf[Expr[Ind]]

      val leftSchemaFact = have(leftSchema) by Restate
      have(wellTypedFormula(signature).substitute(pointSubst*) ==> (leftAt(n) === commonAt)) by
        InstantiateForallSeq(points)(leftSchemaFact)
      val leftBase = have(pointTyped |- (leftAt(n) === commonAt)) by Tautology.from(lastStep)

      val rightSchemaFact = have(rightSchema) by Restate
      have(wellTypedFormula(signature).substitute(pointSubst*) ==> (rightAt(n) === commonAt)) by
        InstantiateForallSeq(points)(rightSchemaFact)
      val rightBase = have(pointTyped |- (rightAt(n) === commonAt)) by Tautology.from(lastStep)

      have(pointTyped |- (leftAt(n) === rightAt(n))) by Congruence.from(leftBase, rightBase)

      // Ascend: peel one domain at a time with function extensionality, discharging each point.
      (n to 1 by -1).foreach { k =>
        val d = domains(k - 1)
        thenHave(pointTyped.take(k - 1) |- (points(k - 1) :: d) ==> (leftAt(k - 1) * points(k - 1) === rightAt(k - 1) * points(k - 1))) by RightImplies
        thenHave(pointTyped.take(k - 1) |- ∀(points(k - 1), (points(k - 1) :: d) ==> (leftAt(k - 1) * points(k - 1) === rightAt(k - 1) * points(k - 1)))) by RightForall
        have(pointTyped.take(k - 1) |- (leftAt(k - 1) === rightAt(k - 1))) by Tautology.from(
          lastStep,
          leftTyped(k - 1),
          rightTyped(k - 1),
          funcExtInFuncSpace of (f := leftAt(k - 1), g := rightAt(k - 1), A := d, B := suffixType(k))
        )
      }
      thenHave(thesis) by Restate
    }
  }
}
