package lisa.maths.SetTheory.Types.ADT.encoding

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.BasicStep.RightForall
import lisa.utils.prooflib.QuantifiersIntro
import lisa.utils.prooflib.Thm

/**
 * Constructs the curried constructor encoding and proves its typing and equations.
 */
private[encoding] final class ConstructorInternals(
    adt: SyntacticADT,
    underlying: SyntacticConstructor,
    semanticSignature: Seq[(Variable[Ind], Expr[Ind])],
    variables: Seq[Variable[Ind]],
    structuralTerm: Expr[Ind],
    typ: Expr[Ind]
) {
  private val abstractions = semanticSignature.scanRight(structuralTerm) { case ((v, domain), body) =>
    TypingHelpers.fun(v :: domain, body)
  }
  private val suffixTypes = semanticSignature.scanRight(adt.term) { case ((_, domain), codomain) =>
    domain ->: codomain
  }

  /**
   * The constructor's curried set-theoretic lambda, or its value when nullary.
   */
  val witness: Expr[Ind] = abstractions.head

  /**
   * The explicit encoding has the declared constructor type.
   */
  val witnessTyping: Theorem = Lemma.generated(witness :: typ) { sp ?=>
    val T1 = variable[Ind]
    val T2, e = variable[Ind >>: Ind]

    def proveTyping(index: Int): Thm = {
      val prefixTyping = wellTypedFormula(semanticSignature.take(index))
      if index == variables.size then have(prefixTyping |- abstractions(index) :: suffixTypes(index)) by Restate.from(adt.intro(underlying))
      else
        val next = proveTyping(index + 1)
        val (v, domain) = semanticSignature(index)
        val body = abstractions(index + 1)
        val codomain = suffixTypes(index + 1)
        have(prefixTyping |- v ∈ domain ==> body ∈ codomain) by Restate.from(next)
        val universallyTyped = thenHave(prefixTyping |- ∀(v ∈ domain, body ∈ codomain)) by RightForall
        have(prefixTyping |- abstractions(index) :: suffixTypes(index)) by
          Cut(universallyTyped, TAbs of (T1 := domain, T2 := λ(v, codomain), e := λ(v, body)))
    }

    have(thesis) by Restate.from(proveTyping(0))
  }

  /**
   * Applying the encoding to well-typed arguments yields its tagged tuple.
   */
  val witnessEquations: Theorem = Lemma.generated(
    forallSeq(
      variables,
      wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)
    )
  ) {
    val T = variable[Ind]
    val e = variable[Ind >>: Ind]
    val e2 = variable[Ind]

    val betas = semanticSignature.indices.map { k =>
      val (v, domain) = semanticSignature(k)
      val wNext = abstractions(k + 1)
      have(wellTypedFormula(semanticSignature) |- abstractions(k) * v === wNext) by
        Tautology.from(BetaReduction of (T := domain, e := λ(v, wNext), e2 := v))
    }
    have(wellTypedFormula(semanticSignature) |- (appSeq(witness)(variables) === structuralTerm)) by Congruence.from(betas*)

    thenHave(wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)) by
      Restate

    thenHave(thesis) by QuantifiersIntro(variables)
  }
}
