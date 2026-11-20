package lisa.maths.SetTheory.Types.ADT.PatternMatching.proofs

import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Comprehension
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Base.Symbols.X
import lisa.maths.SetTheory.Base.Symbols.Y
import lisa.maths.SetTheory.Base.Symbols.φ
import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function
import lisa.maths.SetTheory.Relations.Relation.R
import lisa.maths.SetTheory.Relations.Relation.relationBetween
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStep.LeftExists
import lisa.utils.prooflib.BasicStep.Restate
import lisa.utils.prooflib.BasicStep.RightForall
import lisa.utils.prooflib.InstantiateForall
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.prooflib.QuantifiersIntro

private[proofs] trait WitnessFunctionProofs extends WitnessBranchMembership {

  private val witnessMembershipByCases: Theorem = {
    val witnessInPattern = pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
    Lemma.generated(
      ∀(inputTerm ∈ argType, ∀(outputTerm, witnessInPattern))
    ) {
      val expandedAtInput = have(
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness <=>
            (pair(inputTerm, outputTerm) ∈ witnessBound /\ caseMembership(pair(inputTerm, outputTerm)))
        )
      ) by InstantiateForall(inputTerm)(witnessMembershipExpanded)

      val pointwise = have(
        (inputTerm ∈ argType) |- ∀(outputTerm, witnessInPattern)
      ) subproof {
        assume(inputTerm ∈ argType)
        val witnessExpanded = have(
          pair(inputTerm, outputTerm) ∈ witness <=>
            (pair(inputTerm, outputTerm) ∈ witnessBound /\ caseMembership(pair(inputTerm, outputTerm)))
        ) by InstantiateForall(outputTerm)(expandedAtInput)

        val caseMembershipInvariant = have(∀(pairWitness, caseMembership(pairWitness) <=> patternCaseMembership(pairWitness))) by Restate
        val invariantAtPair = have(
          caseMembership(pair(inputTerm, outputTerm)) <=> patternCaseMembership(pair(inputTerm, outputTerm))
        ) by InstantiateForall(pair(inputTerm, outputTerm))(caseMembershipInvariant)

        have(witnessInPattern) by Tautology.from(witnessExpanded, invariantAtPair)
        thenHave(thesis) by RightForall
      }

      have(
        (inputTerm ∈ argType) ==> ∀(outputTerm, witnessInPattern)
      ) by RightImplies(pointwise)
      thenHave(thesis) by Generalize
    }
  }

  private val witnessTotality: Theorem = {
    Lemma.generated(
      contextualize(
        ∀(inputTerm ∈ argType, ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
      )
    ) {
      if contextPremises.nonEmpty then assume(contextPremise)

      val branchExistenceFacts = patternMatching.clauses.map(pattern =>
        val membershipSchema =
          if contextPremises.isEmpty then have(witnessMembership(pattern).statement.right.head) by Tautology.from(witnessMembership(pattern))
          else
            witnessMembership(pattern).statement.right.head match
              case _ ==> consequent =>
                have(consequent) by Tautology.from(witnessMembership(pattern))
              case _ => throw UnreachableException
        val freshMembership = have(
          pattern.freshBranchPremise ==> pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2) ∈ witness
        ) by InstantiateForallSeq(pattern.variables2)(membershipSchema)

        val freshPairInWitness = have(
          pattern.freshBranchPremise |- pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2) ∈ witness
        ) by Restate.from(freshMembership)

        have(
          (pattern.freshBranchPremise, (inputTerm === pattern.freshInputTerm)) |- pair(inputTerm, pattern.bodyAtFreshVars2) ∈ witness
        ) by Congruence.from(freshPairInWitness)
        have(
          (pattern.freshBranchPremise /\ (inputTerm === pattern.freshInputTerm)) |- pair(inputTerm, pattern.bodyAtFreshVars2) ∈ witness
        ) by Restate.from(lastStep)

        val directBranch = thenHave(
          (pattern.freshBranchPremise /\ (inputTerm === pattern.freshInputTerm)) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
        ) by RightExists

        val liftedBranch =
          pattern.variables2.reverse.foldLeft(directBranch)((fact, v) => have(∃(v, fact.statement.left.head) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by LeftExists(fact))
        have(
          existsSeq(
            pattern.variables2,
            pattern.freshBranchPremise /\ (inputTerm === pattern.freshInputTerm)
          ) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
        ) by Restate.from(liftedBranch)
      )

      val coverageToWitness =
        have(simplify(patternMatching.caseCoverage(inputTerm)) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by
          Tautology.from(branchExistenceFacts*)

      have(
        (inputTerm ∈ argType) ==> simplify(patternMatching.caseCoverage(inputTerm))
      ) by InstantiateForall(inputTerm)(patternMatching.coverage)
      val coveredInput = thenHave(
        (inputTerm ∈ argType) |- simplify(patternMatching.caseCoverage(inputTerm))
      ) by Restate

      have((inputTerm ∈ argType) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by
        Cut(coveredInput, coverageToWitness)
      val pointwise = thenHave(
        (inputTerm ∈ argType) ==> ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
      ) by RightImplies

      have(∀(inputTerm ∈ argType, ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness))) by RightForall(pointwise)
      thenHave(thesis) by Restate
    }
  }

  /**
   * One clause at an independent tuple of graph witnesses.
   */
  private final case class GraphBranch(clause: Clause[Expr[Ind]], variables: Seq[Variable[Ind]]) {
    val premise: Expr[Prop] = clause.branchPremiseAt(variables)
    val input: Expr[Ind] = clause.inputTermAt(variables)
    val body: Expr[Ind] = clause.bodyAt(variables)
    def member(result: Expr[Ind]): Expr[Prop] =
      premise /\ (pair(inputTerm, result) === pair(input, body))
    // Keep theorem boundaries identical to the graph's canonical branch formulas.
    def quantified(result: Expr[Ind]): Expr[Prop] = clause.caseMembership(pair(inputTerm, result))

    // These small facts are reused across all comparisons involving this branch.
    lazy val conditions: Theorem = Lemma.generated(member(outputTerm) |- premise) {
      have(thesis) by Tautology
    }
    lazy val inputEquality: Theorem = Lemma.generated(member(outputTerm) |- inputTerm === input) {
      have(thesis) by Tautology.from(Pair.extensionality.of(a := inputTerm, b := outputTerm, c := input, d := body))
    }
    lazy val outputEquality: Theorem = Lemma.generated(member(outputTerm) |- outputTerm === body) {
      have(thesis) by Tautology.from(Pair.extensionality.of(a := inputTerm, b := outputTerm, c := input, d := body))
    }
  }

  private val graphFunctionality: Theorem = {
    val clauses = patternMatching.clauses
    val forbidden: Seq[Expr[?]] = clauses.flatMap(clause =>
      clause.binders ++ clause.variables1 ++ clause.variables2 ++
        Seq(clause.body, clause.branchPremise, clause.specializedAdtTerm)
    ) ++ Seq(inputTerm, outputTerm, alternateOutputTerm)
    val allocated = collection.mutable.ArrayBuffer.empty[Variable[Ind]]
    val arity = clauses.map(_.binders.size).maxOption.getOrElse(0)
    def freshTuple(): Seq[Variable[Ind]] =
      (0 until arity).map { _ =>
        val variable = Variable[Ind](freshId(forbidden ++ allocated, "graphArgument" + allocated.size))
        allocated += variable
        variable
      }
    // Branch witnesses are bound independently; only the two compared tuples must differ.
    val firstTuple = freshTuple()
    val secondTuple = freshTuple()
    val first = clauses.map(clause => GraphBranch(clause, firstTuple.take(clause.binders.size)))
    val second = clauses.map(clause => GraphBranch(clause, secondTuple.take(clause.binders.size)))
    val equality = outputTerm === alternateOutputTerm

    def compare(left: GraphBranch, right: GraphBranch, sameClause: Boolean): Theorem =
      Lemma.generated((left.quantified(outputTerm), right.quantified(alternateOutputTerm)) |- equality) {
        val direct = have((left.member(outputTerm), right.member(alternateOutputTerm)) |- equality) subproof {
          assume(left.member(outputTerm))
          assume(right.member(alternateOutputTerm))
          if left.body == right.body then
            val leftOutput = have(outputTerm === left.body) by Weakening(left.outputEquality)
            val rightOutput = have(alternateOutputTerm === right.body) by Weakening(right.outputEquality.of(outputTerm := alternateOutputTerm))
            have(equality) by Congruence.from(leftOutput, rightOutput)
          else
            val leftTyped = have(left.premise) by Weakening(left.conditions)
            val rightTyped = have(right.premise) by Weakening(right.conditions.of(outputTerm := alternateOutputTerm))
            val leftInput = have(inputTerm === left.input) by Weakening(left.inputEquality)
            val rightInput = have(inputTerm === right.input) by Weakening(right.inputEquality.of(outputTerm := alternateOutputTerm))
            val inputsEqual = have(left.input === right.input) by Congruence.from(leftInput, rightInput)

            if sameClause then
              val source = have(left.clause.injectivity.statement.right.head) by Tautology.from(left.clause.injectivity)
              val injectivity = have(
                (left.premise /\ right.premise) ==>
                  simplify((left.input === right.input) <=> (left.variables === right.variables))
              ) by InstantiateForallSeq(left.variables ++ right.variables)(source)
              val pairs = left.variables.zip(right.variables)
              val equations = pairs.map((from, to) => from === to)
              val argumentsEqual = equations.map(equation => have(equation) by Tautology.from(injectivity, leftTyped, rightTyped, inputsEqual))
              val reflexive = have(left.body === left.body) by RightRefl
              // The known substitution also works when the body contains lambdas.
              val transported = have(equations.toSet |- left.body === right.body) by
                RightSubst(pairs, (right.variables, left.body === right.body))(reflexive)
              val bodiesEqual = have(left.body === right.body) by Tautology.from((transported +: argumentsEqual)*)
              val leftOutput = have(outputTerm === left.body) by Weakening(left.outputEquality)
              val rightOutput = have(alternateOutputTerm === right.body) by Weakening(right.outputEquality.of(outputTerm := alternateOutputTerm))
              have(equality) by Congruence.from(leftOutput, bodiesEqual, rightOutput)
            else
              val renaming =
                left.clause.variables1.zip(left.variables).map((from, to) => from := to) ++
                  right.clause.variables2.zip(right.variables).map((from, to) => from := to)
              val incompatible = patternMatching.incompatible(left.clause.pattern, right.clause.pattern)
              have(equality) by Tautology.from(incompatible.of(renaming*), leftTyped, rightTyped, inputsEqual)
        }
        val leftClosed = existsSeq(left.variables, left.member(outputTerm))
        val rightClosed = existsSeq(right.variables, right.member(alternateOutputTerm))
        val leftLifted = have((leftClosed, right.member(alternateOutputTerm)) |- equality) by
          QuantifiersIntro(left.variables)(direct)
        val bothLifted = have((leftClosed, rightClosed) |- equality) by QuantifiersIntro(right.variables)(leftLifted)
        have(thesis) by Restate.from(bothLifted)
      }

    val agreements = (for
      i <- clauses.indices
      j <- i until clauses.size
    yield (i, j) -> compare(first(i), second(j), i == j)).toMap

    val firstCases = patternMatching.caseMembership(pair(inputTerm, outputTerm))
    val secondCases = patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
    Lemma.generated((firstCases, secondCases) |- equality) {
      val rows = clauses.indices.map { i =>
        val facts = clauses.indices.map[Thm] { j =>
          if i <= j then agreements((i, j))
          else agreements((j, i)).of(outputTerm := alternateOutputTerm, alternateOutputTerm := outputTerm)
        }
        have((first(i).quantified(outputTerm), secondCases) |- equality) by Tautology.from(facts*)
      }
      have(thesis) by Tautology.from(rows*)
    }
  }

  private val witnessSingleValued: Theorem = {
    val bothOutputs = pair(inputTerm, outputTerm) ∈ witness /\ pair(inputTerm, alternateOutputTerm) ∈ witness
    val equality = outputTerm === alternateOutputTerm
    val allOutputs = ∀(outputTerm, ∀(alternateOutputTerm, bothOutputs ==> equality))

    Lemma.generated(∀(inputTerm ∈ argType, allOutputs)) {
      have(inputTerm ∈ argType ==> allOutputs) subproof {
        assume(inputTerm ∈ argType)
        val atInput = have(
          inputTerm ∈ argType ==> ∀(outputTerm, pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm)))
        ) by InstantiateForall(inputTerm)(witnessMembershipByCases)
        val graphMembership = have(∀(outputTerm, pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm)))) by Tautology.from(atInput)

        have(bothOutputs ==> equality) subproof {
          assume(bothOutputs)
          val first = have(
            pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
          ) by InstantiateForall(outputTerm)(graphMembership)
          val second = have(
            pair(inputTerm, alternateOutputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
          ) by InstantiateForall(alternateOutputTerm)(graphMembership)
          have(equality) by Tautology.from(first, second, graphFunctionality)
        }
        thenHave(allOutputs) by QuantifiersIntro(Seq(outputTerm, alternateOutputTerm))
      }
      thenHave(thesis) by RightForall
    }
  }

  private val witnessUniqueValue: Theorem = {
    Lemma.generated(
      contextualize(
        ∀(inputTerm ∈ argType, ∃!(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
      )
    ) {

      val pointwisePredicate = (out: Expr[Ind]) => pair(inputTerm, out) ∈ witness
      val totalityAtInput =
        if contextPremises.isEmpty then
          have((inputTerm ∈ argType) ==> ∃(outputTerm, pointwisePredicate(outputTerm))) by
            InstantiateForall(inputTerm)(witnessTotality)
        else
          assume(contextPremise)
          witnessTotality.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Restate.from(witnessTotality)
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
        (inputTerm ∈ argType) ==> ∃!(outputTerm, pointwisePredicate(outputTerm))
      ) by Tautology.from(
        existsOneAlternativeDefinition of (P := λ(outputTerm, pointwisePredicate(outputTerm))),
        totalityAtInput,
        singleValuedAtInput
      )

      val core = have(
        ∀(inputTerm, (inputTerm ∈ argType) ==> ∃!(outputTerm, pointwisePredicate(outputTerm)))
      ) by RightForall(pointwiseUnique)

      have(thesis) by Restate.from(core)
    }
  }

  val witnessHasType: Theorem = {
    Lemma.generated(contextualize(witness :: typ)) {
      if !contextPremises.isEmpty then assume(contextPremise)

      have(witnessBody ⊆ witnessBound) by Tautology.from(
        Comprehension.subset of (
          y := witnessBound,
          φ := λ(pairWitness, caseMembership(pairWitness))
        )
      )
      val subsetBound = have(witness ⊆ witnessBound) by Congruence.from(lastStep, witnessDef)

      have(thesis) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := witness,
          A := argType,
          B := returnType
        ),
        Function.functionBetween.definition of (
          f := witness,
          A := argType,
          B := returnType
        ),
        relationBetween.definition of (
          R := witness,
          X := argType,
          Y := returnType
        ),
        subsetBound,
        witnessUniqueValue
      )
    }
  }
}
