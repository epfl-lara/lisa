package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Base.{Comprehension, CartesianProduct, Pair}
import lisa.maths.SetTheory.Base.Symbols.{φ, X, Y}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.maths.SetTheory.Relations.Relation.{relationBetween, R}
import lisa.maths.Quantifiers.∃!
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall


private[functions] final class WitnessTyping[N <: Arity](
    adt: SemanticADT[N],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    returnType: Expr[Ind],
    checkReturnType: Map[SemanticConstructor[N], JUSTIFICATION],
    typ: Expr[Ind],
    witness: Expr[Ind],
    witnessDef: JUSTIFICATION,
    witnessBound: Expr[Ind],
    pairWitness: Variable[Ind],
    caseMembership: Expr[Ind] => Expr[Prop],
    constructorApplicationTyping: (SemanticConstructor[N], Seq[Variable[Ind]]) => THM,
    constructorTagDisequalities: Map[(SemanticConstructor[N], SemanticConstructor[N]), THM]
) {

  private val inputTerm = variable[Ind]
  private val outputTerm = variable[Ind]
  private val alternateOutputTerm = variable[Ind]
  private val witnessBody = { pairWitness ∈ witnessBound | caseMembership(pairWitness) }

  val witnessMembershipByConstructor: Map[SemanticConstructor[N], THM] =
    (for c <- cases.keys yield
      val (vars, body) = cases(c)
      c -> Lemma(
        forallSeq(
          vars,
          wellTypedFormula(c.semanticSignature(vars)) ==> pair(c.appliedTerm(vars), body) ∈ witness
        )
      ) {
        
        val wellTypedArgs = wellTypedFormula(c.semanticSignature(vars))
        val pairTerm = pair(c.appliedTerm(vars), body)

        val inputTyping = have(wellTypedArgs |- c.appliedTerm(vars) :: adt.term) by
          Restate.from(constructorApplicationTyping(c, vars))
        val outputTyping = have(wellTypedArgs |- body :: returnType) by Restate.from(checkReturnType(c))

        val pairInBound = have(wellTypedArgs |- pairTerm ∈ witnessBound) by Tautology.from(
          CartesianProduct.pairMembership of (
            A := adt.term,
            B := returnType,
            x := c.appliedTerm(vars),
            y := body
          ),
          inputTyping,
          outputTyping
        )

        val ownBranchBody = body
          .substitute(vars.zip(c.variables2).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]
        val baseCaseBody = wellTypedFormula(c.semanticSignature2) /\ (pairTerm === pair(c.appliedTerm2, ownBranchBody))
        val ownCaseBranchRaw = existsSeq(c.variables2, baseCaseBody)
        val ownCaseBranch = simplify(ownCaseBranchRaw)

        val fullyInstantiatedCaseBody = baseCaseBody
          .substitute(c.variables2.zip(vars).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Prop]]

        val ownBranchAtCurrentVars = have(
          wellTypedArgs |- fullyInstantiatedCaseBody
        ) by Tautology.from(
          have(wellTypedArgs |- wellTypedArgs) by Hypothesis,
          have(wellTypedArgs |- pairTerm === pair(c.appliedTerm(vars), body)) by RightRefl
        )

        val inOwnCaseBranchRaw = c.variables2.indices.reverse.foldLeft(ownBranchAtCurrentVars)((fact, idx) =>
          val quantifiedVar = c.variables2(idx)
          val witnessVar = vars(idx)
          val priorSubst = c.variables2.take(idx).zip(vars.take(idx)).map((from, to) => from := to)
          val phi = existsSeq(
            c.variables2.drop(idx + 1),
            baseCaseBody.substitute(priorSubst*).asInstanceOf[Expr[Prop]]
          )
          have(wellTypedArgs |- ∃(quantifiedVar, phi)) by
            RightExists.withParameters(phi, quantifiedVar, witnessVar)(fact)
        )

        val inOwnCaseBranch = have(wellTypedArgs |- ownCaseBranch) by Tautology.from(inOwnCaseBranchRaw)
        val rawCaseMembership = have(wellTypedArgs |- caseMembership(pairTerm)) by Tautology.from(inOwnCaseBranch)


        have(
          pairTerm ∈ witnessBody <=> (pairTerm ∈ witnessBound /\ caseMembership(pairTerm))
        ) by Tautology.from(
          Comprehension.membership of (
            x := pairTerm,
            y := witnessBound,
            φ := λ(pairWitness, caseMembership(pairWitness))
          )
        )

        val witnessMembershipEq = have(
          wellTypedArgs |- pairTerm ∈ witness <=> (pairTerm ∈ witnessBound /\ caseMembership(pairTerm))
        ) by Congruence.from(witnessDef, lastStep)

        val pairInBoundAndCase = have(wellTypedArgs |- pairTerm ∈ witnessBound /\ caseMembership(pairTerm)) by
          Tautology.from(pairInBound, rawCaseMembership)

        have(wellTypedArgs |- pairTerm ∈ witness) by Tautology.from(
          witnessMembershipEq,
          pairInBoundAndCase
        )
        thenHave(wellTypedArgs ==> (pairTerm ∈ witness)) by RightImplies
        thenHave(thesis) by QuantifiersIntro(vars)
      }
    ).toMap

  private val witnessRelationBetween: THM = Lemma(relationBetween(witness)(adt.term)(returnType)) {
        have(witnessBody ⊆ witnessBound) by Tautology.from(
          Comprehension.subset of (
            y := witnessBound,
            φ := λ(pairWitness, caseMembership(pairWitness))
          )
        )
        val subsetBound = have(witness ⊆ witnessBound) by Congruence.from(
          lastStep,
          witnessDef
        )
        val relationFromSubset = have(
          relationBetween(witness)(adt.term)(returnType)
        ) by Tautology.from(
          subsetBound,
          relationBetween.definition of (
            R := witness,
            X := adt.term,
            Y := returnType
          )
        )
        have(thesis) by Restate.from(relationFromSubset)
      }


  private val witnessTotality: THM = Lemma(
      ∀(
        inputTerm,
        (inputTerm ∈ adt.term) ==> ∃(outputTerm, in(pair(inputTerm, outputTerm), witness))
      )
    ) {
      val totalityAtInput = ∃(outputTerm, in(pair(inputTerm, outputTerm), witness))
      val constructorBranch = adt.constructors.map(c =>
        c -> simplify(
          existsSeq(
            c.variables2,
            wellTypedFormula(c.semanticSignature2) /\ (inputTerm === c.appliedTerm2)
          )
        )
      ).toMap
      val constructorDisjunction = simplify(seqOr(adt.constructors.map(c => constructorBranch(c))))

      val decompositionAtInput = have(inputTerm ∈ adt.term |- constructorDisjunction) subproof {
        have(inputTerm ∈ adt.term ==> constructorDisjunction) by
          InstantiateForall(inputTerm)(adt.elim)
        thenHave(thesis) by Restate
      }

      val branchToWitness = adt.constructors.map(c =>
        val (caseVars, caseBody) = cases(c)

        val directBranch = have(
          wellTypedFormula(c.semanticSignature2) /\ (inputTerm === c.appliedTerm2) |- totalityAtInput
        ) subproof {
          assume(wellTypedFormula(c.semanticSignature2) /\ (inputTerm === c.appliedTerm2))
          val argsTyped = have(wellTypedFormula(c.semanticSignature2)) by Tautology
          val inputEqCtor = have(inputTerm === c.appliedTerm2) by Tautology

          have(
            forallSeq(
              caseVars,
              wellTypedFormula(c.semanticSignature(caseVars)) ==> pair(c.appliedTerm(caseVars), caseBody) ∈ witness
            )
          ) by Tautology.from(witnessMembershipByConstructor(c))

          val instantiatedMembership = caseVars.zip(c.variables2).foldLeft(lastStep)((fact, varsPair) =>
            fact.statement.right.head match
              case forall(v, phi) =>
                thenHave(phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]) by InstantiateForall(varsPair._2)
              case _ => throw UnreachableException
          )

          val pairInWitnessAtCtor = instantiatedMembership.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(instantiatedMembership, argsTyped)
            case _ => throw UnreachableException

          val existsAtCtorInput = have(∃(outputTerm, in(pair(c.appliedTerm2, outputTerm), witness))) by
            RightExists(pairInWitnessAtCtor)

          val transferAtWitness = have(
            (inputTerm === c.appliedTerm2, in(pair(c.appliedTerm2, outputTerm), witness)) |- totalityAtInput
          ) subproof {
            assume(inputTerm === c.appliedTerm2)
            val eqInput = have(inputTerm === c.appliedTerm2) by Hypothesis
            assume(in(pair(c.appliedTerm2, outputTerm), witness))
            val pairAtCtorInput = have(in(pair(c.appliedTerm2, outputTerm), witness)) by Hypothesis
            val pairAtInput = have(in(pair(inputTerm, outputTerm), witness)) by Congruence.from(pairAtCtorInput, eqInput)
            have(totalityAtInput) by RightExists(pairAtInput)
          }

          val transferExistential = have(
            (inputTerm === c.appliedTerm2, ∃(outputTerm, in(pair(c.appliedTerm2, outputTerm), witness))) |- totalityAtInput
          ) by LeftExists(transferAtWitness)

          have(totalityAtInput) by Tautology.from(inputEqCtor, existsAtCtorInput, transferExistential)
        }

        val rawBranch = c.variables2.reverse.foldLeft(directBranch)((fact, v) =>
          thenHave(∃(v, fact.statement.left.head) |- totalityAtInput) by LeftExists
        )

        have(constructorBranch(c) |- totalityAtInput) by Tautology.from(rawBranch)
      )

      val totalityFromCases =
        if branchToWitness.size == 1 then
          have(constructorDisjunction |- totalityAtInput) by Restate.from(branchToWitness.head)
        else
          have(constructorDisjunction |- totalityAtInput) by LeftOr(branchToWitness*)

      have(inputTerm ∈ adt.term |- totalityAtInput) by Cut(decompositionAtInput, totalityFromCases)
      thenHave((inputTerm ∈ adt.term) ==> totalityAtInput) by RightImplies
      thenHave(
        ∀(
          inputTerm,
          (inputTerm ∈ adt.term) ==> totalityAtInput
        )
      ) by RightForall
      thenHave(thesis) by Restate
    }


  private val witnessSingleValued: THM = Lemma(
      ∀(
        inputTerm,
        (inputTerm ∈ adt.term) ==> ∀(
          outputTerm,
          ∀(
            alternateOutputTerm,
            (in(pair(inputTerm, outputTerm), witness) /\
              in(pair(inputTerm, alternateOutputTerm), witness)) ==> (outputTerm === alternateOutputTerm)
          )
        )
      )
    ) {
      val pairAtOutput = pair(inputTerm, outputTerm)
      val pairAtAlternateOutput = pair(inputTerm, alternateOutputTerm)

      def caseBranchAtOutputWithVars1(c: SemanticConstructor[N]): Expr[Prop] = {
        val (caseVars, caseBody) = cases(c)
        val bodyAtVars1 = caseBody
          .substitute(caseVars.zip(c.variables1).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]
        existsSeq(
          c.variables1,
          wellTypedFormula(c.semanticSignature1) /\
            (pairAtOutput === pair(c.appliedTerm1, bodyAtVars1))
        )
      }

      def caseBranchAtAlternateOutput(c: SemanticConstructor[N]): Expr[Prop] = {
        val (caseVars, caseBody) = cases(c)
        val bodyAtVars2 = caseBody
          .substitute(caseVars.zip(c.variables2).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]
        existsSeq(
          c.variables2,
          wellTypedFormula(c.semanticSignature2) /\
            (pairAtAlternateOutput === pair(c.appliedTerm2, bodyAtVars2))
        )
      }

      val caseDisjunctionAtOutputWithVars1 = seqOr(adt.constructors.map(c => caseBranchAtOutputWithVars1(c)))
      val caseDisjunctionAtAlternateOutput = seqOr(adt.constructors.map(c => caseBranchAtAlternateOutput(c)))

      val outputCaseRenaming = have(caseMembership(pairAtOutput) |- caseDisjunctionAtOutputWithVars1) by Tableau


      val outputMembershipEqBody = have(
        pairAtOutput ∈ witnessBody <=> (pairAtOutput ∈ witnessBound /\ caseMembership(pairAtOutput))
      ) by Tautology.from(
        Comprehension.membership of (
          x := pairAtOutput,
          y := witnessBound,
          φ := λ(pairWitness, caseMembership(pairWitness))
        )
      )

      
      val outputMembershipEq = have(
        pairAtOutput ∈ witness <=> (pairAtOutput ∈ witnessBound /\ caseMembership(pairAtOutput))
      ) by Congruence.from(witnessDef, outputMembershipEqBody)

      have(
        pairAtAlternateOutput ∈ witnessBody <=>
          (pairAtAlternateOutput ∈ witnessBound /\ caseMembership(pairAtAlternateOutput))
      ) by Tautology.from(
        Comprehension.membership of (
          x := pairAtAlternateOutput,
          y := witnessBound,
          φ := λ(pairWitness, caseMembership(pairWitness))
        )
      )
      val alternateMembershipEq = have(
        pairAtAlternateOutput ∈ witness <=>
          (pairAtAlternateOutput ∈ witnessBound /\ caseMembership(pairAtAlternateOutput))
      ) by Congruence.from(witnessDef, lastStep)

      val singleValuedAtInput = have(
        (inputTerm ∈ adt.term, in(pairAtOutput, witness), in(pairAtAlternateOutput, witness)) |- (outputTerm === alternateOutputTerm)
      ) subproof {
        assume(inputTerm ∈ adt.term)
        val inputInAdt = have(inputTerm ∈ adt.term) by Hypothesis

        assume(in(pairAtOutput, witness))
        val pairOutputInWitness = have(in(pairAtOutput, witness)) by Hypothesis

        assume(in(pairAtAlternateOutput, witness))
        val pairAlternateInWitness = have(in(pairAtAlternateOutput, witness)) by Hypothesis

        val outputCaseRaw = have(caseMembership(pairAtOutput)) by Tautology.from(
          pairOutputInWitness,
          outputMembershipEq
        )
        val outputCase = have(caseDisjunctionAtOutputWithVars1) by Tautology.from(
          outputCaseRaw,
          outputCaseRenaming
        )

        val alternateCaseRaw = have(caseMembership(pairAtAlternateOutput)) by Tautology.from(
          pairAlternateInWitness,
          alternateMembershipEq
        )
        val alternateCase = have(caseDisjunctionAtAlternateOutput) by Restate.from(alternateCaseRaw)

        val branchByOutputConstructor = adt.constructors.map(c1 =>
          val (caseVars1, caseBody1) = cases(c1)
          val bodyAtVars1 = caseBody1
            .substitute(caseVars1.zip(c1.variables1).map((from, to) => from := to)*)
            .asInstanceOf[Expr[Ind]]
          val branchAtOutputWithVars1 =
            wellTypedFormula(c1.semanticSignature1) /\
              (pairAtOutput === pair(c1.appliedTerm1, bodyAtVars1))

          val branchByAlternateConstructor = adt.constructors.map(c2 =>
            val (caseVars2, caseBody2) = cases(c2)
            val bodyAtVars2 = caseBody2
              .substitute(caseVars2.zip(c2.variables2).map((from, to) => from := to)*)
              .asInstanceOf[Expr[Ind]]
            val branchAtAlternate =
              wellTypedFormula(c2.semanticSignature2) /\
                (pairAtAlternateOutput === pair(c2.appliedTerm2, bodyAtVars2))

            val directCase = have(
              (branchAtOutputWithVars1, branchAtAlternate, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)
            ) subproof {
              assume(branchAtOutputWithVars1)
              val branchOutputTyped = have(wellTypedFormula(c1.semanticSignature1)) by Tautology
              val branchOutputPairEq = have(pairAtOutput === pair(c1.appliedTerm1, bodyAtVars1)) by Tautology

              assume(branchAtAlternate)
              val branchAlternateTyped = have(wellTypedFormula(c2.semanticSignature2)) by Tautology
              val branchAlternatePairEq = have(pairAtAlternateOutput === pair(c2.appliedTerm2, bodyAtVars2)) by Tautology

              assume(inputTerm ∈ adt.term)

              val outputPairDecomposition = have(
                pairAtOutput === pair(c1.appliedTerm1, bodyAtVars1) |- (inputTerm === c1.appliedTerm1) /\ (outputTerm === bodyAtVars1)
              ) by Tautology.from(
                Pair.extensionality of (
                  a := inputTerm,
                  b := outputTerm,
                  c := c1.appliedTerm1,
                  d := bodyAtVars1
                )
              )
              val outputComponents = have((inputTerm === c1.appliedTerm1) /\ (outputTerm === bodyAtVars1)) by
                Tautology.from(branchOutputPairEq, outputPairDecomposition)
              val inputEqFromOutput = have(inputTerm === c1.appliedTerm1) by Tautology.from(outputComponents)
              val outputEqToBody = have(outputTerm === bodyAtVars1) by Tautology.from(outputComponents)

              val alternatePairDecomposition = have(
                pairAtAlternateOutput === pair(c2.appliedTerm2, bodyAtVars2) |- (inputTerm === c2.appliedTerm2) /\ (alternateOutputTerm === bodyAtVars2)
              ) by Tautology.from(
                Pair.extensionality of (
                  a := inputTerm,
                  b := alternateOutputTerm,
                  c := c2.appliedTerm2,
                  d := bodyAtVars2
                )
              )
              val alternateComponents = have((inputTerm === c2.appliedTerm2) /\ (alternateOutputTerm === bodyAtVars2)) by
                Tautology.from(branchAlternatePairEq, alternatePairDecomposition)
              val inputEqFromAlternate = have(inputTerm === c2.appliedTerm2) by Tautology.from(alternateComponents)
              val alternateEqToBody = have(alternateOutputTerm === bodyAtVars2) by Tautology.from(alternateComponents)

              val c1EqInput = have(c1.appliedTerm1 === inputTerm) by Congruence.from(inputEqFromOutput)
              val c1EqC2 = have(c1.appliedTerm1 === c2.appliedTerm2) by Tautology.from(
                altEqualityTransitivity of (
                  x := c1.appliedTerm1,
                  y := inputTerm,
                  z := c2.appliedTerm2
                ),
                c1EqInput,
                inputEqFromAlternate
              )

              if c1 == c2 then
                val bodyEq =
                  if c1.arity == 0 then
                    have(bodyAtVars1 === bodyAtVars2) by RightRefl
                  else
                    val argsEqConjunction = have(c1.variables1 === c1.variables2) by Tautology.from(
                      c1.injectivity,
                      branchOutputTyped,
                      branchAlternateTyped,
                      c1EqC2
                    )
                    val argumentEqualities = c1.variables1.zip(c1.variables2).map((u, v) =>
                      have(u === v) by Tautology.from(argsEqConjunction)
                    )
                    have(bodyAtVars1 === bodyAtVars2) by Congruence.from(argumentEqualities*)

                val body2EqAlternate = have(bodyAtVars2 === alternateOutputTerm) by Congruence.from(alternateEqToBody)
                val outputEqToAlternate = have(outputTerm === alternateOutputTerm) by Tautology.from(
                  altEqualityTransitivity of (
                    x := outputTerm,
                    y := bodyAtVars1,
                    z := alternateOutputTerm
                  ),
                  outputEqToBody,
                  have(bodyAtVars1 === alternateOutputTerm) by Tautology.from(
                    altEqualityTransitivity of (
                      x := bodyAtVars1,
                      y := bodyAtVars2,
                      z := alternateOutputTerm
                    ),
                    bodyEq,
                    body2EqAlternate
                  )
                )
                have(thesis) by Restate.from(outputEqToAlternate)
              else
                val c1ShortBase = have(c1.shortDefinition.statement.right.head) by Tautology.from(c1.shortDefinition)
                val c1ShortAtVars1 = c1.variables1.foldLeft(c1ShortBase)((_, v1) =>
                  lastStep.statement.right.head match
                    case forall(v, phi) =>
                      thenHave(phi.substituteUnsafe(Map(v -> v1)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v1)
                    case _ => throw UnreachableException
                )
                val c1StructuralEq = c1ShortAtVars1.statement.right.head match
                  case _ ==> consequent =>
                    have(consequent) by Tautology.from(c1ShortAtVars1, branchOutputTyped)
                  case _ => throw UnreachableException

                val c2ShortBase = have(c2.shortDefinition.statement.right.head) by Tautology.from(c2.shortDefinition)
                val c2ShortAtVars2 = c2.variables2.foldLeft(c2ShortBase)((_, v2) =>
                  lastStep.statement.right.head match
                    case forall(v, phi) =>
                      thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v2)
                    case _ => throw UnreachableException
                )
                val c2StructuralEq = c2ShortAtVars2.statement.right.head match
                  case _ ==> consequent =>
                    have(consequent) by Tautology.from(c2ShortAtVars2, branchAlternateTyped)
                  case _ => throw UnreachableException

                val c1StructuralToApplied = have(c1.structuralTerm1 === c1.appliedTerm1) by
                  Congruence.from(c1StructuralEq)

                val c1StructuralEqC2Applied = have(c1.structuralTerm1 === c2.appliedTerm2) by Tautology.from(
                  altEqualityTransitivity of (
                    x := c1.structuralTerm1,
                    y := c1.appliedTerm1,
                    z := c2.appliedTerm2
                  ),
                  c1StructuralToApplied,
                  c1EqC2
                )

                val structuralEq = have(c1.structuralTerm1 === c2.structuralTerm2) by Tautology.from(
                  altEqualityTransitivity of (
                    x := c1.structuralTerm1,
                    y := c2.appliedTerm2,
                    z := c2.structuralTerm2
                  ),
                  c1StructuralEqC2Applied,
                  c2StructuralEq
                )

                val tagsFromStructuralEq = have(
                  c1.structuralTerm1 === c2.structuralTerm2 |-
                    (c1.underlying.tagTerm === c2.underlying.tagTerm) /\
                    (c1.underlying.subterm1 === c2.underlying.subterm2)
                ) by Tautology.from(
                  Pair.extensionality of (
                    a := c1.underlying.tagTerm,
                    b := c1.underlying.subterm1,
                    c := c2.underlying.tagTerm,
                    d := c2.underlying.subterm2
                  )
                )

                val tagsEqual = have(c1.underlying.tagTerm === c2.underlying.tagTerm) by
                  Tautology.from(structuralEq, tagsFromStructuralEq)

                val tagsDifferent = have(!(c1.underlying.tagTerm === c2.underlying.tagTerm)) by
                  Tautology.from(constructorTagDisequalities((c1, c2)))

                have(thesis) by Tautology.from(tagsEqual, tagsDifferent)
            }

            val liftedAcrossAlternate = c2.variables2.reverse.foldLeft((directCase, branchAtAlternate))((acc, v) =>
              val (fact, phi) = acc
              val nextPhi = ∃(v, phi)
              val nextFact = have((branchAtOutputWithVars1, nextPhi, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
                LeftExists.withParameters(phi, v)(fact)
              (nextFact, nextPhi)
            )._1

            have((branchAtOutputWithVars1, caseBranchAtAlternateOutput(c2), inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
              Restate.from(liftedAcrossAlternate)
          )

          val fromAlternateDisjunction =
            if branchByAlternateConstructor.size == 1 then
              have((branchAtOutputWithVars1, caseDisjunctionAtAlternateOutput, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
                Restate.from(branchByAlternateConstructor.head)
            else
              have((branchAtOutputWithVars1, caseDisjunctionAtAlternateOutput, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
                LeftOr(branchByAlternateConstructor*)

          val liftedAcrossOutput = c1.variables1.reverse.foldLeft((fromAlternateDisjunction, branchAtOutputWithVars1))((acc, v) =>
            val (fact, phi) = acc
            val nextPhi = ∃(v, phi)
            val nextFact = have((nextPhi, caseDisjunctionAtAlternateOutput, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
              LeftExists.withParameters(phi, v)(fact)
            (nextFact, nextPhi)
          )._1

          have((caseBranchAtOutputWithVars1(c1), caseDisjunctionAtAlternateOutput, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
            Restate.from(liftedAcrossOutput)
        )

        val fromBothDisjunctions =
          if branchByOutputConstructor.size == 1 then
            have((caseDisjunctionAtOutputWithVars1, caseDisjunctionAtAlternateOutput, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
              Restate.from(branchByOutputConstructor.head)
          else
            have((caseDisjunctionAtOutputWithVars1, caseDisjunctionAtAlternateOutput, inputTerm ∈ adt.term) |- (outputTerm === alternateOutputTerm)) by
              LeftOr(branchByOutputConstructor*)

        have(outputTerm === alternateOutputTerm) by Tautology.from(
          outputCase,
          alternateCase,
          inputInAdt,
          fromBothDisjunctions
        )
      }

      val pairMembershipConjunction =
        in(pairAtOutput, witness) /\ in(pairAtAlternateOutput, witness)

      have(
        (inputTerm ∈ adt.term) |- pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
      ) by Tautology.from(singleValuedAtInput)
      thenHave(
        (inputTerm ∈ adt.term) |- ∀(
          alternateOutputTerm,
          pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
        )
      ) by RightForall
      thenHave(
        (inputTerm ∈ adt.term) |- ∀(
          outputTerm,
          ∀(
            alternateOutputTerm,
            pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
          )
        )
      ) by RightForall
      thenHave((inputTerm ∈ adt.term) ==> ∀(
        outputTerm,
        ∀(
          alternateOutputTerm,
          pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
        )
      )) by RightImplies
      thenHave(
        ∀(
          inputTerm,
          (inputTerm ∈ adt.term) ==> ∀(
            outputTerm,
            ∀(
              alternateOutputTerm,
              pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
            )
          )
        )
      ) by RightForall
      thenHave(thesis) by Restate
    }


  private val witnessUniqueValue: THM = Lemma(
      ∀(
        inputTerm ∈ adt.term,
        existsOne(outputTerm, in(pair(inputTerm, outputTerm), witness))
      )
    ) {
      val pointwisePredicate = (out: Expr[Ind]) => in(pair(inputTerm, out), witness)

      val totalityAtInput = have(
        (inputTerm ∈ adt.term) ==> ∃(outputTerm, pointwisePredicate(outputTerm))
      ) by InstantiateForall(inputTerm)(witnessTotality)

      val singleValuedAtInput = have(
        (inputTerm ∈ adt.term) ==> ∀(
          outputTerm,
          ∀(
            alternateOutputTerm,
            (pointwisePredicate(outputTerm) /\
              pointwisePredicate(alternateOutputTerm)) ==> (outputTerm === alternateOutputTerm)
          )
        )
      ) by InstantiateForall(inputTerm)(witnessSingleValued)

      val pointwiseUnique = have(
        (inputTerm ∈ adt.term) |- existsOne(outputTerm, pointwisePredicate(outputTerm))
      ) subproof {
        assume(inputTerm ∈ adt.term)
        val existenceAtInput = have(∃(outputTerm, pointwisePredicate(outputTerm))) by
          Tautology.from(totalityAtInput)
        val functionalityAtInput = have(
          ∀(
            outputTerm,
            ∀(
              alternateOutputTerm,
              (pointwisePredicate(outputTerm) /\
                pointwisePredicate(alternateOutputTerm)) ==> (outputTerm === alternateOutputTerm)
            )
          )
        ) by Tautology.from(singleValuedAtInput)

        val candidateOutputTerm = variable[Ind]

        val witnessAndFunctionalityGiveUnique = have(
          (
            pointwisePredicate(outputTerm),
            ∀(
              outputTerm,
              ∀(
                alternateOutputTerm,
                (pointwisePredicate(outputTerm) /\
                  pointwisePredicate(alternateOutputTerm)) ==> (outputTerm === alternateOutputTerm)
              )
            )
          ) |- existsOne(outputTerm, pointwisePredicate(outputTerm))
        ) subproof {
          assume(pointwisePredicate(outputTerm))
          val pointWitness = have(pointwisePredicate(outputTerm)) by Hypothesis
          assume(
            ∀(
              outputTerm,
              ∀(
                alternateOutputTerm,
                (pointwisePredicate(outputTerm) /\
                  pointwisePredicate(alternateOutputTerm)) ==> (outputTerm === alternateOutputTerm)
              )
            )
          )

          thenHave(
            ∀(
              alternateOutputTerm,
              (pointwisePredicate(candidateOutputTerm) /\
                pointwisePredicate(alternateOutputTerm)) ==> (candidateOutputTerm === alternateOutputTerm)
            )
          ) by InstantiateForall(candidateOutputTerm)
          val uniquenessImpAtWitness = thenHave(
            (pointwisePredicate(candidateOutputTerm) /\
              pointwisePredicate(outputTerm)) ==> (candidateOutputTerm === outputTerm)
          ) by InstantiateForall(outputTerm)

          val pointwiseToEq = have(
            pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm)
          ) subproof {
            assume(pointwisePredicate(candidateOutputTerm))
            val pointWitness3 = have(pointwisePredicate(candidateOutputTerm)) by Hypothesis
            val bothWitnesses = have(
              pointwisePredicate(candidateOutputTerm) /\ pointwisePredicate(outputTerm)
            ) by RightAnd(pointWitness3, pointWitness)
            have(candidateOutputTerm === outputTerm) by Tautology.from(
              uniquenessImpAtWitness,
              bothWitnesses
            )
            thenHave(thesis) by Restate
          }

          val allEqToWitness = have(
            ∀(
              candidateOutputTerm,
              pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm)
            )
          ) by RightForall(pointwiseToEq)
          have(
            pointwisePredicate(outputTerm) /\
              ∀(
                candidateOutputTerm,
                pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm)
              )
          ) by Tautology.from(pointWitness, allEqToWitness)
          thenHave(
            ∃(
              outputTerm,
              pointwisePredicate(outputTerm) /\
                ∀(
                  candidateOutputTerm,
                  pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm)
                )
            )
          ) by RightExists
          thenHave(existsOne(outputTerm, pointwisePredicate(outputTerm))) by
            Substitute(
              ∃!.definition of (
                P := λ(outputTerm, pointwisePredicate(outputTerm))
              )
            )
          thenHave(thesis) by Restate
        }

        have(
          (
            ∃(outputTerm, pointwisePredicate(outputTerm)),
            ∀(
              outputTerm,
              ∀(
                alternateOutputTerm,
                (pointwisePredicate(outputTerm) /\
                  pointwisePredicate(alternateOutputTerm)) ==> (outputTerm === alternateOutputTerm)
              )
            )
          ) |- existsOne(outputTerm, pointwisePredicate(outputTerm))
        ) by LeftExists(witnessAndFunctionalityGiveUnique)

        have(existsOne(outputTerm, pointwisePredicate(outputTerm))) by
          Tautology.from(existenceAtInput, functionalityAtInput, lastStep)
        thenHave(thesis) by Restate
      }

      have((inputTerm ∈ adt.term) ==> existsOne(outputTerm, pointwisePredicate(outputTerm))) by
        Restate.from(pointwiseUnique)
      thenHave(
        ∀(
          inputTerm,
          (inputTerm ∈ adt.term) ==> existsOne(outputTerm, pointwisePredicate(outputTerm))
        )
      ) by RightForall
      thenHave(thesis) by Restate
    }


  val witnessHasType: THM = Lemma(witness :: typ) {
    val witnessFunctionBetween = have(
      Function.functionBetween(witness)(adt.term)(returnType)
    ) by Tautology.from(
        Function.functionBetween.definition of (
          f := witness,
          A := adt.term,
          B := returnType
        ),
        witnessRelationBetween,
        witnessUniqueValue
      )

    have(thesis) by Tautology.from(
      BasicTheorems.funcBetweenEqInFuncSpace of (
        f := witness,
        A := adt.term,
        B := returnType
      ),
      witnessFunctionBetween
    )
  }
}
