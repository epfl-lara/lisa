package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.FunctionAbstractions
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.ExistsOneBuilder
import lisa.maths.SetTheory.Types.TypingHelpers.{::, `*`}
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.utils.prooflib.ProofTacticLib.Arity

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

  private val witness: Expr[Ind] = FunctionAbstractions.nestedAbstraction(semanticSignature, structuralTerm)

  private val witnessTyping: THM = Lemma(witness :: typ) {
    def witnessAt(index: Int): Expr[Ind] =
      FunctionAbstractions.nestedAbstraction(semanticSignature.drop(index), structuralTerm)

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

          have(thesis) by
            Tautology.from(
              lastStep,
              FunctionAbstractions.TAbsConstOn(domain, nextType, λ(v, body))
            )
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
    val witness = FunctionAbstractions.nestedAbstraction(semanticSignature, structuralTerm)
    val T = variable[Ind]
    val e = variable[Ind >>: Ind]
    val e2 = variable[Ind]

    val betas = semanticSignature.indices.map { k =>
      val (v, domain) = semanticSignature(k)
      val wNext = FunctionAbstractions.nestedAbstraction(semanticSignature.drop(k + 1), structuralTerm)
      have(wellTypedFormula(semanticSignature) |- FunctionAbstractions.nestedAbstraction(semanticSignature.drop(k), structuralTerm) * v === wNext) by
        Tautology.from(BetaReduction of (T := domain, e := λ(v, wNext), e2 := v))
    }
    have(wellTypedFormula(semanticSignature) |- (appSeq(witness)(variables) === structuralTerm)) by Congruence.from(betas*)

    thenHave(wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)) by
      Restate
      
    thenHave(thesis) by QuantifiersIntro(variables)
  }

  private val existence: THM = Lemma(∃(c, untypedDefinition)) {
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
  
  private val pairwiseUniqueness: THM = Lemma(xDef /\ yDef ==> (x === y)) {
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
        FunctionAbstractions.curriedCommonValue(semanticSignature, adt.term, x, y, structuralTerm)
      )
  }

  val uniqueness: THM =
    ExistsOneBuilder(
      witnessVar = c,
      definitionAt = f0 => untypedDefinition.substitute(c := f0),
      existence = existence,
      pairwiseUniqueness = pairwiseUniqueness
    ).theorem
}
