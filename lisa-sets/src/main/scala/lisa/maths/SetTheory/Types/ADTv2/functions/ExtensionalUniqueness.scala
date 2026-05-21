package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate

private[functions] final class ExtensionalUniqueness[N <: Arity](
    adt: SemanticADT[N],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    returnType: Expr[Ind],
    typ: Expr[Ind],
    untypedDefinition: Expr[Prop]
) {

  private def definitionFormula(v: Variable[Ind]): Expr[Prop] =
    untypedDefinition.substitute(f := v)

  lazy val nonRecursivePointwise: THM =
    Lemma(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) {
      assume(definitionFormula(x) /\ definitionFormula(y))
      val xDefinition = have(definitionFormula(x)) by Tautology
      val yDefinition = have(definitionFormula(y)) by Tautology

      val xTyped = have(x :: typ) by Tautology.from(xDefinition)
      val yTyped = have(y :: typ) by Tautology.from(yDefinition)

      val xBetween = have(Function.functionBetween(x)(adt.term)(returnType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := x,
          A := adt.term,
          B := returnType
        ),
        xTyped
      )
      val yBetween = have(Function.functionBetween(y)(adt.term)(returnType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := y,
          A := adt.term,
          B := returnType
        ),
        yTyped
      )

      val xOnDomain = have(Function.functionOn(x)(adt.term)) by Tautology.from(
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := x,
          A := adt.term,
          B := returnType
        ),
        xBetween
      )
      val yOnDomain = have(Function.functionOn(y)(adt.term)) by Tautology.from(
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := y,
          A := adt.term,
          B := returnType
        ),
        yBetween
      )

      val pointInput = variable[Ind]
      val constructorBranch = adt.constructors.map(c =>
        c -> simplify(
          existsSeq(
            c.variables2,
            wellTypedFormula(c.semanticSignature2) /\ (pointInput === c.appliedTerm2)
          )
        )
      ).toMap
      val constructorDisjunction = simplify(seqOr(adt.constructors.map(c => constructorBranch(c))))

      val decompositionAtInput = have(pointInput ∈ adt.term |- constructorDisjunction) subproof {
        have(pointInput ∈ adt.term ==> constructorDisjunction) by
          InstantiateForall(pointInput)(adt.elim)
        thenHave(thesis) by Restate
      }

      val branchEqualities = adt.constructors.map(c =>
        val (caseVars, caseBody) = cases(c)

        val directBranch = have(
          wellTypedFormula(c.semanticSignature2) /\ (pointInput === c.appliedTerm2) |- (x * pointInput === y * pointInput)
        ) subproof {
          assume(wellTypedFormula(c.semanticSignature2) /\ (pointInput === c.appliedTerm2))
          val argsTyped = have(wellTypedFormula(c.semanticSignature2)) by Tautology
          val pointEqCtor = have(pointInput === c.appliedTerm2) by Tautology

          val xCaseSchema = have(
            forallSeq(
              caseVars,
              wellTypedFormula(c.semanticSignature(caseVars)) ==> (x * c.appliedTerm(caseVars) === caseBody)
            )
          ) by Tautology.from(xDefinition)
          val yCaseSchema = have(
            forallSeq(
              caseVars,
              wellTypedFormula(c.semanticSignature(caseVars)) ==> (y * c.appliedTerm(caseVars) === caseBody)
            )
          ) by Tautology.from(yDefinition)

          val substitutions = caseVars.zip(c.variables2).map((from, to) =>
            lisa.utils.fol.FOL.SubstPair(from, to)
          )
          val instantiatedCaseBody: Expr[Ind] =
            caseBody.substitute(substitutions*).asInstanceOf[Expr[Ind]]

          val xCaseAtVars2 = caseVars.zip(c.variables2).foldLeft(xCaseSchema)((fact, varsPair) =>
            fact.statement.right.head match
              case forall(v, phi) =>
                have(phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]) by InstantiateForall(varsPair._2)(fact)
              case _ => fact
          )
          val xAtCtor = xCaseAtVars2.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(xCaseAtVars2, argsTyped)
            case _ => throw UnreachableException

          val yCaseAtVars2 = caseVars.zip(c.variables2).foldLeft(yCaseSchema)((fact, varsPair) =>
            fact.statement.right.head match
              case forall(v, phi) =>
                have(phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]) by InstantiateForall(varsPair._2)(fact)
              case _ => fact
          )
          val yAtCtor = yCaseAtVars2.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(yCaseAtVars2, argsTyped)
            case _ => throw UnreachableException

          val xAtInputArg = have(x * pointInput === x * c.appliedTerm2) by Congruence.from(pointEqCtor)
          val xAtInput = have(x * pointInput === instantiatedCaseBody) by
            Congruence.from(xAtInputArg, xAtCtor)

          val yAtInputArg = have(y * pointInput === y * c.appliedTerm2) by Congruence.from(pointEqCtor)
          val yAtInput = have(y * pointInput === instantiatedCaseBody) by
            Congruence.from(yAtInputArg, yAtCtor)
          val yAtInputRev = have(instantiatedCaseBody === y * pointInput) by
            Congruence.from(yAtInput)

          have(x * pointInput === y * pointInput) by Tautology.from(
            altEqualityTransitivity of (
              x := x * pointInput,
              y := instantiatedCaseBody,
              z := y * pointInput
            ),
            xAtInput,
            yAtInputRev
          )
        }

        val rawBranch = c.variables2.reverse.foldLeft(directBranch)((fact, v) =>
          thenHave(∃(v, fact.statement.left.head) |- (x * pointInput === y * pointInput)) by LeftExists
        )

        have(constructorBranch(c) |- (x * pointInput === y * pointInput)) by Tautology.from(rawBranch)
      )

      val equalityFromCases =
        if branchEqualities.size == 1 then
          have(constructorDisjunction |- (x * pointInput === y * pointInput)) by
            Restate.from(branchEqualities.head)
        else
          have(constructorDisjunction |- (x * pointInput === y * pointInput)) by
            LeftOr(branchEqualities*)

      have(pointInput ∈ adt.term |- (x * pointInput === y * pointInput)) by
        Cut(decompositionAtInput, equalityFromCases)
      thenHave(pointInput ∈ adt.term ==> (x * pointInput === y * pointInput)) by RightImplies
      val pointwiseOnDomain = thenHave(
        ∀(pointInput, pointInput ∈ adt.term ==> (x * pointInput === y * pointInput))
      ) by RightForall

      have(x === y) by Tautology.from(
        BasicTheorems.extensionality of (
          f := x,
          g := y,
          A := adt.term,
          x := pointInput
        ),
        xOnDomain,
        yOnDomain,
        pointwiseOnDomain
      )
      thenHave(thesis) by Tautology
    }

}
