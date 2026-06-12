package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.FunctionAbstractions
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems._
import lisa.maths.SetTheory.Types.TypingHelpers.::
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
      val prefixVars = variables.take(index)
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
            assume(v ∈ domain)
            have(wellTypedFormula(prefixSig :+ ((v, domain)))) by Tautology
            have(body :: nextType) by Cut(lastStep, next)
            thenHave(thesis) by Restate
          }
          thenHave(∀(v ∈ domain, body :: nextType)) by RightForall

          have(witnessAt(index) :: (domain ->: nextType)) by
            Tautology.from(
              lastStep,
              FunctionAbstractions.TAbsConstOn(domain, nextType, λ(v, body))
            )
          thenHave(thesis) by Restate
        }
    }

    have(⊤ |- (witness :: typ)) by Restate.from(proveTyping(0))
    thenHave(thesis) by Tautology
  }

  private val witnessEquations: THM = Lemma(
    forallSeq(
      variables,
      wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)
    )
  ) {
    have(wellTypedFormula(semanticSignature) |- (appSeq(witness)(variables) === structuralTerm)) by
      Restate.from(FunctionAbstractions.curriedBeta(semanticSignature, structuralTerm))
    thenHave(wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)) by
      RightImplies
    thenHave(thesis) by QuantifiersIntro(variables)
  }

  val existence: THM = Lemma(∃(c, untypedDefinition)) {
    have(witness :: typ) by Restate.from(witnessTyping)
    have(
      forallSeq(
        variables,
        wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)
      )
    ) by Restate.from(witnessEquations)

    have(
      (witness :: typ) /\
        forallSeq(
          variables,
          wellTypedFormula(semanticSignature) ==> (appSeq(witness)(variables) === structuralTerm)
        )
    ) by Tautology.from(lastStep, witnessTyping)

    thenHave(thesis) by RightExists
  }

  val pairwiseUniqueness: THM = Lemma(
    untypedDefinition.substitute(c := x) /\ untypedDefinition.substitute(c := y) ==> (x === y)
  ) {
    if variables.isEmpty then
      val xDef = untypedDefinition.substitute(c := x)
      val yDef = untypedDefinition.substitute(c := y)
      assume(xDef /\ yDef)
      val xEq = have(x === structuralTerm) by Tautology
      val yEq = have(y === structuralTerm) by Tautology
      val yEqRev = have(structuralTerm === y) by Congruence.from(yEq)
      have(x === y) by Tautology.from(
        altEqualityTransitivity of (x := x, y := structuralTerm, z := y),
        xEq,
        yEqRev
      )
      thenHave(thesis) by Tautology
    else
      val xDef = untypedDefinition.substitute(c := x)
      val yDef = untypedDefinition.substitute(c := y)
      assume(xDef /\ yDef)

      val xDefinition = have(xDef) by Tautology
      val yDefinition = have(yDef) by Tautology

      val xTyped = have(x :: typ) by Tautology.from(xDefinition)
      val yTyped = have(y :: typ) by Tautology.from(yDefinition)

      val xSchemaFormula = xDefinition.statement.right.head match
        case _ /\ phi => phi
        case _ => throw UnreachableException
      val ySchemaFormula = yDefinition.statement.right.head match
        case _ /\ phi => phi
        case _ => throw UnreachableException

      val xSchema = have(xSchemaFormula) by Tautology.from(xDefinition)

      val ySchema = have(ySchemaFormula) by Tautology.from(yDefinition)

      val pointwiseVars = semanticSignature.indices.map(i => variable[Ind](s"constructoruniq$i"))
      val pointwiseSignature = pointwiseVars.zip(semanticSignature.map(_._2))
      val instantiatedStructuralTerm =
        structuralTerm
          .substitute(variables.zip(pointwiseVars).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]

      val pointwiseEquality = have(
        forallSeq(
          pointwiseVars,
          wellTypedFormula(pointwiseSignature) ==> (appSeq(x)(pointwiseVars) === appSeq(y)(pointwiseVars))
        )
      ) subproof {
        val xSchemaLocal = have(xSchema.statement.right.head) by Tautology.from(xSchema)
        val ySchemaLocal = have(ySchema.statement.right.head) by Tautology.from(ySchema)
        val xAtVars = have(
          wellTypedFormula(pointwiseSignature) ==> (appSeq(x)(pointwiseVars) === instantiatedStructuralTerm)
        ) by InstantiateForallSeq(pointwiseVars)(xSchemaLocal)
        val yAtVars = have(
          wellTypedFormula(pointwiseSignature) ==> (appSeq(y)(pointwiseVars) === instantiatedStructuralTerm)
        ) by InstantiateForallSeq(pointwiseVars)(ySchemaLocal)

        have(wellTypedFormula(pointwiseSignature) |- (appSeq(x)(pointwiseVars) === appSeq(y)(pointwiseVars))) subproof {
          val varsTyped = assume(wellTypedFormula(pointwiseSignature))
          val xAtBody = have(appSeq(x)(pointwiseVars) === instantiatedStructuralTerm) by
            Tautology.from(xAtVars, varsTyped)
          val yAtBody = have(appSeq(y)(pointwiseVars) === instantiatedStructuralTerm) by
            Tautology.from(yAtVars, varsTyped)
          val yAtBodyRev = have(instantiatedStructuralTerm === appSeq(y)(pointwiseVars)) by Congruence.from(yAtBody)
          have(appSeq(x)(pointwiseVars) === appSeq(y)(pointwiseVars)) by Tautology.from(
            altEqualityTransitivity of (
              x := appSeq(x)(pointwiseVars),
              y := instantiatedStructuralTerm,
              z := appSeq(y)(pointwiseVars)
            ),
            xAtBody,
            yAtBodyRev
          )
        }
        thenHave(wellTypedFormula(pointwiseSignature) ==> (appSeq(x)(pointwiseVars) === appSeq(y)(pointwiseVars))) by
          RightImplies
        thenHave(thesis) by QuantifiersIntro(pointwiseVars)
      }

      have(x === y) by Tautology.from(
        xTyped,
        yTyped,
        pointwiseEquality,
        FunctionAbstractions.curriedExtensionality(pointwiseSignature, adt.term, x, y)
      )
      thenHave(thesis) by Tautology
  }

  val uniqueness: THM =
    ExistsOneBuilder(
      witnessVar = c,
      definitionAt = f0 => untypedDefinition.substitute(c := f0),
      existence = existence,
      pairwiseUniqueness = pairwiseUniqueness
    ).theorem
}
