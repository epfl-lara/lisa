package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Function.functionBetween
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.Functions.Pi.Pi
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.maths.SetTheory.Types.TypingHelpers.{::, `*`}
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.maths.SetTheory.Types.TypingTheorems.arrowElim
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.QuantifiersIntro

private[encoding] final class ConstructorInternals[N <: Arity](
    adt: SyntacticADT[N],
    underlying: SyntacticConstructor,
    semanticSignature: Seq[(Variable[Ind], Expr[Ind])],
    variables: Seq[Variable[Ind]],
    structuralTerm: Expr[Ind],
    typ: Expr[Ind]
) {
  val untypedDefinition: Expr[Prop] = (c :: typ) /\ forallSeq(
    variables,
    wellTypedFormula(semanticSignature) ==> (appSeq(c)(variables) === structuralTerm)
  )

  private def nestedAbstraction(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      body: Expr[Ind]
  ): Expr[Ind] =
    signature.reverse.foldLeft(body) { case (acc, (v, domain)) =>
      TypingHelpers.fun(v :: domain, acc)
    }

  private val witness: Expr[Ind] = nestedAbstraction(semanticSignature, structuralTerm)

  private val witnessTyping: THM = Lemma(witness :: typ) {
    def witnessAt(index: Int): Expr[Ind] =
      nestedAbstraction(semanticSignature.drop(index), structuralTerm)

    def suffixType(index: Int): Expr[Ind] =
      semanticSignature.drop(index).map(_._2).foldRight[Expr[Ind]](adt.term)((a, b) => a ->: b)

    def proveTyping(index: Int): THM = {
      val prefixSig = semanticSignature.take(index)

      if index == variables.size then
        Lemma(wellTypedFormula(prefixSig) |- (witnessAt(index) :: suffixType(index))) {
          have(thesis) by Restate.from(adt.intro(underlying))
        }
      else
        val next = proveTyping(index + 1)
        val v = variables(index)
        val domain = semanticSignature(index)._2
        val nextType = suffixType(index + 1)
        val body = witnessAt(index + 1)

        Lemma(wellTypedFormula(prefixSig) |- (witnessAt(index) :: suffixType(index))) {
          assume(wellTypedFormula(prefixSig))
          have(v ∈ domain ==> (body :: nextType)) subproof {
            have(v ∈ domain |- wellTypedFormula(prefixSig :+ ((v, domain)))) by Tautology
            have(v ∈ domain |- body :: nextType) by Cut(lastStep, next)
            thenHave(thesis) by Restate
          }
          thenHave(∀(v ∈ domain, body :: nextType)) by RightForall

          val T1 = variable[Ind]
          val T = variable[Ind]
          val T2 = variable[Ind >>: Ind]
          val e = variable[Ind >>: Ind]
          val e2 = variable[Ind]

          val bodyTypedAtPoint = have(v ∈ domain ==> (body :: nextType)) by InstantiateForall(v)(lastStep)
          val bodyTypedAtV = have(v ∈ domain |- body ∈ nextType) by Restate.from(bodyTypedAtPoint)

          val bodyAtPoint = have(v ∈ domain |- λ(v, body)(v) === body) by
            Weakening(BetaReduction of (T := domain, e := λ(v, body), e2 := v))
          val typeAtPoint = have(v ∈ domain |- λ(v, nextType)(v) === nextType) by
            Weakening(BetaReduction of (T := domain, e := λ(v, nextType), e2 := v))

          have(v ∈ domain |- λ(v, body)(v) ∈ λ(v, nextType)(v)) by
            Congruence.from(bodyAtPoint, typeAtPoint, bodyTypedAtV)
          thenHave((v ∈ domain) ==> (λ(v, body)(v) ∈ λ(v, nextType)(v))) by Restate
          thenHave(∀(v ∈ domain, λ(v, body)(v) ∈ λ(v, nextType)(v))) by RightForall
          have(abs(domain)(λ(v, body)) ∈ Pi(domain)(λ(x, nextType))) by
            Cut(lastStep, TAbs of (T1 := domain, T2 := λ(x, nextType), e := λ(v, body)))
          thenHave(thesis) by Restate
        }
    }

    have(thesis) by Restate.from(proveTyping(0))
  }

  private val witnessEquations: THM = Lemma(
    forallSeq(
      variables,
      wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)
    )
  ) {
    val witness = nestedAbstraction(semanticSignature, structuralTerm)
    val T = variable[Ind]
    val e = variable[Ind >>: Ind]
    val e2 = variable[Ind]

    val betas = semanticSignature.indices.map { k =>
      val (v, domain) = semanticSignature(k)
      val wNext = nestedAbstraction(semanticSignature.drop(k + 1), structuralTerm)
      have(wellTypedFormula(semanticSignature) |- nestedAbstraction(semanticSignature.drop(k), structuralTerm) * v === wNext) by
        Tautology.from(BetaReduction of (T := domain, e := λ(v, wNext), e2 := v))
    }
    have(wellTypedFormula(semanticSignature) |- (appSeq(witness)(variables) === structuralTerm)) by Congruence.from(betas*)

    thenHave(wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)) by
      Restate
      
    thenHave(thesis) by QuantifiersIntro(variables)
  }

  val existence: THM = Lemma(∃(c, untypedDefinition)) {
    have(
      (witness :: typ) /\
        forallSeq(
          variables,
          wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)
        )
    ) by RightAnd(witnessEquations, witnessTyping)
    thenHave(thesis) by RightExists
  }

  private val xDef = untypedDefinition.substitute(c := x)
  private val yDef = untypedDefinition.substitute(c := y)

  /**
   * Curried extensionality specialised to the case where `left` and `right` both reduce, on every
   * well-typed argument tuple, to the *same* `commonValue`. Taking the two reduction schemas
   * directly (rather than a pre-combined "they agree" schema) lets the single instantiation at the
   * fresh points happen here, instead of being done once by the caller and again inside this lemma.
   */
  private def curriedCommonValue(
      semanticSignature: Seq[(Variable[Ind], Expr[Ind])],
      resultType: Expr[Ind],
      left: Expr[Ind],
      right: Expr[Ind],
      commonValue: Expr[Ind]
  ): THM = {
    val vars = semanticSignature.map(_._1)
    val domains = semanticSignature.map(_._2)
    val n = semanticSignature.size

    // Type of `left`/`right` once their first `k` arguments have been supplied.
    def suffixType(k: Int): Expr[Ind] =
      domains.drop(k).foldRight[Expr[Ind]](resultType)(_ ->: _)

    val finalType = suffixType(0)
    // Built through a fresh placeholder and a capture-avoiding substitution, so the schema matches
    // the caller's even when `fn`'s name clashes with one of the bound argument variables.
    def schemaFor(fn: Expr[Ind]): Expr[Prop] =
      val placeholder = variable[Ind]("curriedfn")
      forallSeq(vars, wellTypedFormula(semanticSignature) ==> (appSeq(placeholder)(vars) === commonValue)).substitute(placeholder := fn)
    val leftSchema = schemaFor(left)
    val rightSchema = schemaFor(right)

    // One fresh point per argument position, and the partial applications they induce.
    val points = semanticSignature.indices.map(i => variable[Ind](s"pointarg$i"))
    val pointTyped = points.zip(domains).map((p, d) => (p :: d): Expr[Prop])
    def leftAt(k: Int): Expr[Ind] = appSeq(left)(points.take(k))
    def rightAt(k: Int): Expr[Ind] = appSeq(right)(points.take(k))

    Lemma((left :: finalType, right :: finalType, leftSchema, rightSchema) |- (left === right)) {
      assume(left :: finalType, right :: finalType, leftSchema, rightSchema)

      // Base case: instantiating each schema at the points shows both sides reduce to the same
      // `commonValue`, hence agree there.
      val pointSubst = vars.zip(points).map((v, p) => v := p)
      val commonAt = commonValue.substitute(pointSubst*).asInstanceOf[Expr[Ind]]

      val leftSchemaFact = have(leftSchema) by Restate
      have(wellTypedFormula(semanticSignature).substitute(pointSubst*) ==> (leftAt(n) === commonAt)) by
        InstantiateForallSeq(points)(leftSchemaFact)
      val leftBase = have(pointTyped |- (leftAt(n) === commonAt)) by Restate.from(lastStep)

      val rightSchemaFact = have(rightSchema) by Restate
      have(wellTypedFormula(semanticSignature).substitute(pointSubst*) ==> (rightAt(n) === commonAt)) by
        InstantiateForallSeq(points)(rightSchemaFact)
      val rightBase = have(pointTyped |- (rightAt(n) === commonAt)) by Restate.from(lastStep)

      // Typing of the partial applications: under the first `k` points being well-typed,
      // `leftAt(k)`/`rightAt(k) :: suffixType(k)`, by repeated arrow elimination.
      def typingChain(fun: Int => Expr[Ind]) =
        (1 to n).foldLeft(Vector(have(fun(0) :: finalType) by Restate)) { (chain, k) =>
          val applyStep = have(
            pointTyped.take(k - 1) |- (points(k - 1) :: domains(k - 1)) ==> (fun(k) :: suffixType(k))
          ) by Cut(
            chain(k - 1),
            arrowElim of (f := fun(k - 1), a := domains(k - 1), b := suffixType(k), x := points(k - 1))
          )
          // `pointTyped.take(k)` is `pointTyped.take(k - 1)` plus the implication's antecedent,
          // so discharging the implication is a plain Restate.
          chain :+ (have(pointTyped.take(k) |- (fun(k) :: suffixType(k))) by Restate.from(applyStep))
        }
      val leftTyped = typingChain(leftAt)
      val rightTyped = typingChain(rightAt)

      have(pointTyped |- (leftAt(n) === rightAt(n))) by Congruence.from(leftBase, rightBase)

      // Ascend: peel one domain at a time with function extensionality, discharging each point.
      (n to 1 by -1).foreach { k =>
        val d = domains(k - 1)
        val suffix = suffixType(k)
        val leftIsFun = functionBetween(leftAt(k - 1))(d)(suffix)
        val rightIsFun = functionBetween(rightAt(k - 1))(d)(suffix)
        val pointwiseEq = ∀(points(k - 1), (points(k - 1) :: d) ==> (leftAt(k - 1) * points(k - 1) === rightAt(k - 1) * points(k - 1)))
        val extPremise = leftIsFun /\ rightIsFun /\ pointwiseEq

        thenHave(
          pointTyped.take(k - 1) |- (points(k - 1) :: d) ==> (leftAt(k - 1) * points(k - 1) === rightAt(k - 1) * points(k - 1))
        ) by RightImplies
        val pointwiseAtD = thenHave(
          pointTyped.take(k - 1) |- pointwiseEq
        ) by RightForall

        // Rephrase the function-space iff as a local sequent, then cut it with the typed partial application.
        val leftBetweenBridge = have((leftAt(k - 1) ∈ (d ->: suffix)) |- leftIsFun) by 
          Weakening(BasicTheorems.funcBetweenEqInFuncSpace of (f := leftAt(k - 1), A := d, B := suffix))
        val leftBetween = have(pointTyped.take(k - 1) |- leftIsFun) by
          Cut(leftTyped(k - 1), leftBetweenBridge)

        val rightBetweenBridge = have((rightAt(k - 1) ∈ (d ->: suffix)) |- rightIsFun) by 
          Weakening(BasicTheorems.funcBetweenEqInFuncSpace of (f := rightAt(k - 1), A := d, B := suffix))
        val rightBetween = have(pointTyped.take(k - 1) |- rightIsFun) by
          Cut(rightTyped(k - 1), rightBetweenBridge)

        val extensionalityPremise = have(pointTyped.take(k - 1) |- extPremise) by 
          RightAnd(leftBetween, rightBetween, pointwiseAtD)
        val extensionality = have(extPremise |- (leftAt(k - 1) === rightAt(k - 1))) by Weakening(
          BasicTheorems.functionalExtentionality of (
            f := leftAt(k - 1),
            g := rightAt(k - 1),
            A := d,
            B := suffix
          )
        )
        have(pointTyped.take(k - 1) |- (leftAt(k - 1) === rightAt(k - 1))) by
          Cut(extensionalityPremise, extensionality)
      }
      thenHave(thesis) by Restate
    }
  }
  
  val pairwiseUniqueness: THM = Lemma(xDef /\ yDef ==> (x === y)) {
    assume(xDef, yDef)

    if variables.isEmpty then
      // No arguments: both definitions pin `x` and `y` to the same structural term.
      val xEq = have(x === structuralTerm) by Restate
      val yEq = have(y === structuralTerm) by Restate
      have(x === y) by Congruence.from(xEq, yEq)
      thenHave(thesis) by Restate
    else
      // `x` and `y` both reduce to `structuralTerm` on every well-typed tuple, so are equal:
      // curried extensionality combines the two reduction schemas and lifts the agreement.
      have(thesis) by Restate.from(
        curriedCommonValue(semanticSignature, adt.term, x, y, structuralTerm)
      )
  }

}
