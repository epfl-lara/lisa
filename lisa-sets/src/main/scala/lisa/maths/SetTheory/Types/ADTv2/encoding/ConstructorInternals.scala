package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

import lisa.maths.SetTheory.Types.ADTv2.support.ExistsOneBuilder
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.`**`

private[encoding] final class ConstructorInternals[N <: Arity](
    adt: SyntacticADT[N],
    semanticSignature: Seq[(Variable[Ind], Expr[Ind])],
    variables: Seq[Variable[Ind]],
    structuralTerm: Expr[Ind],
    typ: Expr[Ind]
) {

  val untypedDefinition: Expr[Prop] = (c :: typ) /\ forallSeq(
    variables,
    wellTypedFormula(semanticSignature) ==> (appSeq(c)(variables) === structuralTerm)
  )

  val existence: THM = Lemma(∃(c, untypedDefinition)) {
    // Phase 3 placeholder: direct constructor witness existence still needs a real proof.
    have(thesis) by Sorry
  }

  val pairwiseUniqueness: THM = Lemma(
    untypedDefinition.substitute(c := x) /\ untypedDefinition.substitute(c := y) ==> (x === y)
  ) {
    // Phase 3 placeholder: extensional constructor uniqueness still needs a real proof.
    have(thesis) by Sorry
  }

  val uniqueness: THM =
    ExistsOneBuilder(
      witnessVar = c,
      definitionAt = f0 => untypedDefinition.substitute(c := f0),
      existence = existence,
      pairwiseUniqueness = pairwiseUniqueness
    ).theorem
}
