package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.{InstantiateForallSeq, QuantifiersIntro}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Base.{Comprehension, CartesianProduct, Pair}
import lisa.maths.SetTheory.Base.Symbols.{X, Y, φ}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.maths.SetTheory.Relations.Relation.{R, relationBetween}
import lisa.maths.Quantifiers.∃!
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

/**
 * Shared semantic witness construction for ADTv2 functions.
 *
 * A case-defined witness is a relation `W ⊆ A × T` described by semantic branches.
 * This class factors the common proof layer used by ordinary semantic
 * functions and recursive witness relations:
 *   - branch-wise witness membership
 *   - relation-betweenness
 *   - totality and single-valuedness
 *   - uniqueness of outputs
 *   - function typing
 *   - witness application equations on branch inputs
 *
 * Clients provide the ADT-specific ingredients:
 *   - the witness term and its `DEF` equation
 *   - the branch bodies and the `caseMembership` predicate
 *   - return-type checks for each branch body
 *   - optional ambient assumptions required to type the branch bodies
 *
 * When `contextPremises` is empty, exported theorems are plain formulas. When it is
 * non-empty, theorems are wrapped under the conjunction of these premises.
 */
final class CaseDefinedWitness[N <: Arity](
    adt: SemanticADT[N],
    argType: Expr[Ind],
    patternMatching: PatternSystem[N],
    returnType: Expr[Ind],
    typ: Expr[Ind],
    witness: Expr[Ind],
    witnessDef: JUSTIFICATION,
    witnessBound: Expr[Ind],
    pairWitness: Variable[Ind],
    caseMembership: Expr[Ind] => Expr[Prop],
    checkReturnType: Map[Pattern[N], JUSTIFICATION],
    constructorTagDisequalities: Map[(SemanticConstructor[N], SemanticConstructor[N]), THM],
    contextPremises: Seq[Expr[Prop]] = Seq.empty
) {

  private val inputTerm = variable[Ind]
  private val outputTerm = variable[Ind]
  private val alternateOutputTerm = variable[Ind]

  private val witnessBody = { pairWitness ∈ witnessBound | caseMembership(pairWitness) }
  private val contextPremise: Expr[Prop] = simplify(seqAnd(contextPremises))

  private def contextualize(formula: Expr[Prop]): Expr[Prop] =
    if contextPremises.isEmpty then formula else contextPremise ==> formula

  private def constructorHead(pattern: Pattern[N]): ConstructorHeadPattern[N] =
    ConstructorHeadPattern.require(pattern)

  val witnessMembershipByPattern: Map[Pattern[N], THM] =
    patternMatching.patterns.map(pattern =>
      val ch = constructorHead(pattern)
      val vars = pattern.binders
      val body = pattern.body
      pattern -> Lemma(contextualize(
        forallSeq(
          vars,
          pattern.branchPremiseAt(vars) ==> pair(pattern.inputTermAt(vars), body) ∈ witness
        )
      )) {
        val contextHyp =
          if contextPremises.isEmpty then None else Some(assume(contextPremise))
        val wellTypedArgs = pattern.branchPremiseAt(vars)
        val wellTypedPremises = pattern.typingPremisesAt(vars)
        val pairTerm = pair(pattern.inputTermAt(vars), body)

        def proveAvailablePremise(required: Expr[Prop]) =
          if required == wellTypedArgs then
            have(wellTypedArgs |- required) by Hypothesis
          else if wellTypedPremises.contains(required) then
            have(wellTypedArgs |- required) by Tautology.from(
              have(wellTypedArgs |- wellTypedArgs) by Hypothesis
            )
          else
            contextPremises.find(_ == required) match
              case Some(_) =>
                contextHyp match
                  case Some(hyp) =>
                    have(wellTypedArgs |- required) by Tautology.from(
                      hyp,
                      have(wellTypedArgs |- wellTypedArgs) by Hypothesis
                    )
                  case None =>
                    throw IllegalArgumentException(
                      s"Premise $required requires a non-empty contextual assumption."
                    )
              case None =>
                throw IllegalArgumentException(
                  s"Unsupported typing premise in CaseDefinedWitness: $required"
                )

        val inputTyping = have(wellTypedArgs |- pattern.inputTermAt(vars) :: argType) by
          Tautology.from(pattern.inputTypingAt(vars, argType))

        val outputTypingPremises =
          checkReturnType(pattern).statement.left.toSeq.map(_.asInstanceOf[Expr[Prop]])
        val outputTypingFacts = outputTypingPremises.map(proveAvailablePremise)
        val outputTyping = have(wellTypedArgs |- body :: returnType) by Tautology.from(
          (checkReturnType(pattern) +: outputTypingFacts)*
        )

        val pairInBound = have(wellTypedArgs |- pairTerm ∈ witnessBound) by Tautology.from(
          CartesianProduct.pairMembership of (
            A := argType,
            B := returnType,
            x := pattern.inputTermAt(vars),
            y := body
          ),
          inputTyping,
          outputTyping
        )

        val baseCaseBody =
          pattern.freshBranchPremise /\ (pairTerm === pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2))
        val ownCaseBranch = simplify(existsSeq(pattern.variables2, baseCaseBody))

        val fullyInstantiatedCaseBody = baseCaseBody
          .substitute(pattern.variables2.zip(vars).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Prop]]

        val ownBranchAtCurrentVars = have(
          wellTypedArgs |- fullyInstantiatedCaseBody
        ) by Tautology.from(
          have(wellTypedArgs |- wellTypedArgs) by Hypothesis,
          have(wellTypedArgs |- pairTerm === pair(pattern.inputTermAt(vars), body)) by RightRefl
        )

        val inOwnCaseBranchRaw =
          pattern.variables2.indices.reverse.foldLeft(ownBranchAtCurrentVars)((fact, idx) =>
            val quantifiedVar = pattern.variables2(idx)
            val witnessVar = vars(idx)
            val priorSubst =
              pattern.variables2.take(idx).zip(vars.take(idx)).map((from, to) => from := to)
            val phi = existsSeq(
              pattern.variables2.drop(idx + 1),
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
          wellTypedArgs |- pairTerm ∈ witness <=>
            (pairTerm ∈ witnessBound /\ caseMembership(pairTerm))
        ) by Congruence.from(witnessDef, lastStep)

        val pairInBoundAndCase =
          have(wellTypedArgs |- pairTerm ∈ witnessBound /\ caseMembership(pairTerm)) by
            Tautology.from(pairInBound, rawCaseMembership)

        have(wellTypedArgs |- pairTerm ∈ witness) by
          Tautology.from(witnessMembershipEq, pairInBoundAndCase)
        thenHave(wellTypedArgs ==> (pairTerm ∈ witness)) by RightImplies
        val core = thenHave(
          forallSeq(
            vars,
            pattern.branchPremiseAt(vars) ==> pair(pattern.inputTermAt(vars), body) ∈ witness
          )
        ) by QuantifiersIntro(vars)

        if contextPremises.isEmpty then have(thesis) by Restate.from(core)
        else have(thesis) by Tautology.from(contextHyp.get, core)
      }
    ).toMap

  def witnessMembership(pattern: Pattern[N]): THM =
    witnessMembershipByPattern(pattern)

  val witnessRelationBetween: THM =
    Lemma(relationBetween(witness)(argType)(returnType)) {
      have(witnessBody ⊆ witnessBound) by Tautology.from(
        Comprehension.subset of (
          y := witnessBound,
          φ := λ(pairWitness, caseMembership(pairWitness))
        )
      )
      val subsetBound = have(witness ⊆ witnessBound) by Congruence.from(lastStep, witnessDef)
      have(relationBetween(witness)(argType)(returnType)) by Tautology.from(
        subsetBound,
        relationBetween.definition of (
          R := witness,
          X := argType,
          Y := returnType
        )
      )
      have(thesis) by Restate.from(lastStep)
    }

  val witnessTotality: THM = Lemma(
    contextualize(
      ∀(inputTerm ∈ argType, ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
    )
  ) {
    // Branch-oriented totality.
    //
    // The intended generic proof is:
    // 1. eliminate `inputTerm` by constructor using `adt.elim`
    // 2. refine the constructor case with `patternMatching.branchSelectionFor`
    // 3. instantiate `witnessMembership(pattern)` on the selected branch
    //
    // This avoids assuming that one constructor corresponds to a unique branch.
    have(thesis) by Sorry
  }

  val witnessSingleValued: THM = Lemma(
    ∀(inputTerm ∈ argType,
      ∀(outputTerm,
        ∀(alternateOutputTerm,
          (pair(inputTerm, outputTerm) ∈ witness /\
            pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
            (outputTerm === alternateOutputTerm)
        )
      )
    )
  ) {
    // Branch-oriented single-valuedness.
    //
    // The generic proof should decompose each witness membership into a branch
    // witness, then reason pairwise on branches:
    // - same branch: use the branch-local equalities
    // - different branches: use `patternMatching.incompatible(pattern1, pattern2)`
    //
    // Constructor-specific proofs remain valid only as an internal helper for
    // the same-branch case.
    have(thesis) by Sorry
  }

  val witnessUniqueValue: THM = Lemma(
    contextualize(
      ∀(inputTerm ∈ argType, existsOne(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
    )
  ) {
    val contextHyp =
      if contextPremises.isEmpty then None else Some(assume(contextPremise))

    val pointwisePredicate = (out: Expr[Ind]) => pair(inputTerm, out) ∈ witness
    val totalityAtInput =
      if contextPremises.isEmpty then
        have((inputTerm ∈ argType) ==> ∃(outputTerm, pointwisePredicate(outputTerm))) by
          InstantiateForall(inputTerm)(witnessTotality)
      else
        witnessTotality.statement.right.head match
          case _ ==> consequent =>
            have(consequent) by Tautology.from(witnessTotality, contextHyp.get)
            thenHave((inputTerm ∈ argType) ==> ∃(outputTerm, pointwisePredicate(outputTerm))) by
              InstantiateForall(inputTerm)
          case _ => throw UnreachableException
    val singleValuedAtInput = have(
      (inputTerm ∈ argType) ==> ∀(
        outputTerm,
        ∀(
          alternateOutputTerm,
          (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
            (outputTerm === alternateOutputTerm)
        )
      )
    ) by InstantiateForall(inputTerm)(witnessSingleValued)

    val pointwiseUnique = have(
      (inputTerm ∈ argType) |- existsOne(outputTerm, pointwisePredicate(outputTerm))
    ) subproof {
      assume(inputTerm ∈ argType)
      val existenceAtInput = have(∃(outputTerm, pointwisePredicate(outputTerm))) by
        Tautology.from(totalityAtInput)
      val functionalityAtInput = have(
        ∀(
          outputTerm,
          ∀(
            alternateOutputTerm,
            (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
              (outputTerm === alternateOutputTerm)
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
              (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
                (outputTerm === alternateOutputTerm)
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
              (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
                (outputTerm === alternateOutputTerm)
            )
          )
        )
        thenHave(
          ∀(
            alternateOutputTerm,
            (pointwisePredicate(candidateOutputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
              (candidateOutputTerm === alternateOutputTerm)
          )
        ) by InstantiateForall(candidateOutputTerm)
        val uniquenessImpAtWitness = thenHave(
          (pointwisePredicate(candidateOutputTerm) /\ pointwisePredicate(outputTerm)) ==>
            (candidateOutputTerm === outputTerm)
        ) by InstantiateForall(outputTerm)
        val pointwiseToEq = have(
          pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm)
        ) subproof {
          assume(pointwisePredicate(candidateOutputTerm))
          val pointWitness3 = have(pointwisePredicate(candidateOutputTerm)) by Hypothesis
          val bothWitnesses = have(
            pointwisePredicate(candidateOutputTerm) /\ pointwisePredicate(outputTerm)
          ) by RightAnd(pointWitness3, pointWitness)
          have(candidateOutputTerm === outputTerm) by
            Tautology.from(uniquenessImpAtWitness, bothWitnesses)
          thenHave(thesis) by Restate
        }
        val allEqToWitness = have(
          ∀(candidateOutputTerm, pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm))
        ) by RightForall(pointwiseToEq)
        have(
          pointwisePredicate(outputTerm) /\
            ∀(candidateOutputTerm, pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm))
        ) by Tautology.from(pointWitness, allEqToWitness)
        thenHave(
          ∃(
            outputTerm,
            pointwisePredicate(outputTerm) /\
              ∀(candidateOutputTerm, pointwisePredicate(candidateOutputTerm) ==> (candidateOutputTerm === outputTerm))
          )
        ) by RightExists
        thenHave(existsOne(outputTerm, pointwisePredicate(outputTerm))) by
          Substitute(∃!.definition of (P := λ(outputTerm, pointwisePredicate(outputTerm))))
        thenHave(thesis) by Restate
      }

      have(
        (
          ∃(outputTerm, pointwisePredicate(outputTerm)),
          ∀(
            outputTerm,
            ∀(
              alternateOutputTerm,
              (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
                (outputTerm === alternateOutputTerm)
            )
          )
        ) |- existsOne(outputTerm, pointwisePredicate(outputTerm))
      ) by LeftExists(witnessAndFunctionalityGiveUnique)
      have(existsOne(outputTerm, pointwisePredicate(outputTerm))) by
        Tautology.from(existenceAtInput, functionalityAtInput, lastStep)
      thenHave(thesis) by Restate
    }

    val core = have(
      ∀(inputTerm, (inputTerm ∈ argType) ==> existsOne(outputTerm, pointwisePredicate(outputTerm)))
    ) subproof {
      have((inputTerm ∈ argType) ==> existsOne(outputTerm, pointwisePredicate(outputTerm))) by
        Restate.from(pointwiseUnique)
      thenHave(thesis) by RightForall
    }

    if contextPremises.isEmpty then have(thesis) by Restate.from(core)
    else have(thesis) by Tautology.from(contextHyp.get, core)
  }

  val witnessHasType: THM = Lemma(contextualize(witness :: typ)) {
    val contextHyp =
      if contextPremises.isEmpty then None else Some(assume(contextPremise))
    if contextPremises.isEmpty then
      have(
        ∀(inputTerm ∈ argType, existsOne(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
      ) by Tautology.from(witnessUniqueValue)
    else
      witnessUniqueValue.statement.right.head match
        case _ ==> consequent =>
          have(consequent) by Tautology.from(witnessUniqueValue, contextHyp.get)
        case _ => throw UnreachableException
    val witnessFunctionBetween = have(
      Function.functionBetween(witness)(argType)(returnType)
    ) by Tautology.from(
      Function.functionBetween.definition of (
        f := witness,
        A := argType,
        B := returnType
      ),
      witnessRelationBetween,
      lastStep
    )
    val core = have(witness :: typ) by Tautology.from(
      BasicTheorems.funcBetweenEqInFuncSpace of (
        f := witness,
        A := argType,
        B := returnType
      ),
      witnessFunctionBetween
    )
    if contextPremises.isEmpty then have(thesis) by Restate.from(core)
    else have(thesis) by Tautology.from(contextHyp.get, core)
  }

  val witnessCaseByPattern: Map[Pattern[N], THM] =
    patternMatching.patterns.map(pattern =>
      val ch = constructorHead(pattern)
      val vars = pattern.binders
      val body = pattern.body
      pattern -> Lemma(contextualize(
        forallSeq(
          vars,
          pattern.branchPremiseAt(vars) ==> (witness * pattern.inputTermAt(vars) === body)
        )
      )) {
        val contextHyp =
          if contextPremises.isEmpty then None else Some(assume(contextPremise))
        val wellTypedArgs = pattern.branchPremiseAt(vars)
        val pairTerm = pair(pattern.inputTermAt(vars), body)

        val membershipSchema =
          if contextPremises.isEmpty then
            have(witnessMembership(pattern).statement.right.head) by Tautology.from(witnessMembership(pattern))
            lastStep
          else
            witnessMembership(pattern).statement.right.head match
              case _ ==> consequent =>
                have(consequent) by Tautology.from(witnessMembership(pattern), contextHyp.get)
                lastStep
              case _ => throw UnreachableException
        val instantiatedMembership = have(
          wellTypedArgs ==> pairTerm ∈ witness
        ) by InstantiateForallSeq(vars)(membershipSchema)
        val pairInWitness = have(wellTypedArgs |- pairTerm ∈ witness) by Tautology.from(instantiatedMembership)

        val witnessBetween =
          if contextPremises.isEmpty then
            have(Function.functionBetween(witness)(argType)(returnType)) by Tautology.from(
              BasicTheorems.funcBetweenEqInFuncSpace of (
                f := witness,
                A := argType,
                B := returnType
              ),
              witnessHasType
            )
          else
            have(witness :: typ) by Tautology.from(witnessHasType, contextHyp.get)
            have(Function.functionBetween(witness)(argType)(returnType)) by Tautology.from(
              BasicTheorems.funcBetweenEqInFuncSpace of (
                f := witness,
                A := argType,
                B := returnType
              ),
              lastStep
            )
        val witnessIsFunction = have(Function.function(witness)) by Tautology.from(
          BasicTheorems.functionBetweenIsFunction of (
            f := witness,
            A := argType,
            B := returnType
          ),
          witnessBetween
        )
        val witnessDomain = have(Function.dom(witness) === argType) by Tautology.from(
          BasicTheorems.functionBetweenDomain of (
            f := witness,
            A := argType,
            B := returnType
          ),
          witnessBetween
        )

        val inputTyping = have(wellTypedArgs |- pattern.inputTermAt(vars) :: argType) by
          Tautology.from(pattern.inputTypingAt(vars, argType))
        val inputInDomain = have(wellTypedArgs |- pattern.inputTermAt(vars) ∈ Function.dom(witness)) by
          Congruence.from(inputTyping, witnessDomain)

        val appEq = have(
          wellTypedArgs |- (witness * pattern.inputTermAt(vars) === body) <=> (pairTerm ∈ witness)
        ) by Tautology.from(
          BasicTheorems.appDefinition of (
            f := witness,
            x := pattern.inputTermAt(vars),
            y := body
          ),
          witnessIsFunction,
          inputInDomain
        )

        have(wellTypedArgs |- (witness * pattern.inputTermAt(vars) === body)) by
          Tautology.from(appEq, pairInWitness)
        thenHave(wellTypedArgs ==> (witness * pattern.inputTermAt(vars) === body)) by RightImplies
        val core = thenHave(
          forallSeq(
            vars,
            pattern.branchPremiseAt(vars) ==> (witness * pattern.inputTermAt(vars) === body)
          )
        ) by QuantifiersIntro(vars)

        if contextPremises.isEmpty then have(thesis) by Restate.from(core)
        else have(thesis) by Tautology.from(contextHyp.get, core)
      }
    ).toMap

  def witnessCase(pattern: Pattern[N]): THM =
    witnessCaseByPattern(pattern)
}
