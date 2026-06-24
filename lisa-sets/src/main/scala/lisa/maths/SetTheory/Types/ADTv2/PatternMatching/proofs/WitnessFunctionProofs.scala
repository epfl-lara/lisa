package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs

import lisa.automation.Substitution
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
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.prooflib.QuantifiersIntro
import lisa.utils.debug.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.BasicStepTactic.RightRefl
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

private[proofs] trait WitnessFunctionProofs[N <: Arity] extends WitnessBranchMembership[N] {

  private def branchWitnessAt(
      pattern: Pattern[N],
      vars: Seq[Variable[Ind]],
      ambientInput: Expr[Ind],
      ambientOutput: Expr[Ind]
  ): Expr[Prop] = {
    pattern.branchPremiseAt(vars) /\ (
      pair(ambientInput, ambientOutput) ===
        pair(pattern.inputTermAt(vars), pattern.bodyAt(vars))
    )
  }

  val witnessMembership: Expr[Prop] =
    seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))


  private val witnessMembershipByCases: THM = Time.measure("witness/MembershipByCases") {
    val witnessInPattern = pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
    Lemma(
      ∀(inputTerm ∈ argType, ∀(outputTerm, witnessInPattern))
    ) {
      val expandedAtInput = have(
        ∀(outputTerm,
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

  private val witnessMembershipByNamedCases: THM = Time.measure("witness/MembershipByNamedCases") {
    Lemma(
      ∀(inputTerm ∈ argType,
        ∀(outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
        )
      )
    ) {
      val pointwise = have(
        (inputTerm ∈ argType) |- ∀(outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
        )
      ) subproof {
        assume(inputTerm ∈ argType)
        val rawCasesAtInput = have(
          ∀(outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
          )
        ) by Restate.from(
          have(
            (inputTerm ∈ argType) ==> ∀(outputTerm,
              pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
            )
          ) by InstantiateForall(inputTerm)(witnessMembershipByCases)
        )

        val witnessToCases = have(
          pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
        ) by InstantiateForall(outputTerm)(rawCasesAtInput)

        val rawCaseToNamedCases = patternMatching.patterns.map(pattern =>
          val rawBranch = existsSeq(
            pattern.variables2,
            branchWitnessAt(pattern, pattern.variables2, inputTerm, outputTerm)
          )
          val namedBranch = existsSeq(
            pattern.binders,
            branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm)
          )

          have(rawBranch |- namedBranch) subproof {
            assume(rawBranch)
            val directBranch = have(
              branchWitnessAt(pattern, pattern.variables2, inputTerm, outputTerm) |- namedBranch
            ) subproof {
              assume(branchWitnessAt(pattern, pattern.variables2, inputTerm, outputTerm))
              val namedAtVars2 = have(
                branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm)
                  .substitute(pattern.binders.zip(pattern.variables2).map((from, to) => from := to)*)
                  .asInstanceOf[Expr[Prop]]
              ) by Restate.from(lastStep)
              val raw = pattern.binders.indices.foldRight(namedAtVars2)((idx, fact) =>
                val namedVar = pattern.binders(idx)
                val witnessVar = pattern.variables2(idx)
                val priorSubst =
                  pattern.binders.take(idx).zip(pattern.variables2.take(idx)).map((from, to) => from := to)
                val phi = existsSeq(
                  pattern.binders.drop(idx + 1),
                  branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm)
                    .substitute(priorSubst*)
                    .asInstanceOf[Expr[Prop]]
                )
                have(∃(namedVar, phi)) by RightExists.withParameters(phi, namedVar, witnessVar)(fact)
              )
              have(namedBranch) by Restate.from(raw)
              thenHave(thesis) by Restate
            }

            val liftedBranch = pattern.variables2.reverse.foldLeft(directBranch)((fact, v) => thenHave(∃(v, fact.statement.left.head) |- namedBranch) by LeftExists)
            have(thesis) by Restate.from(liftedBranch)
          }
        )

        val rawCaseToNamedDisjunction = rawCaseToNamedCases.map(fact => have(fact.statement.left.head |- witnessMembership) by Restate.from(fact))

        val casesToNamed =
          if rawCaseToNamedDisjunction.size == 1 then
            have(patternMatching.caseMembership(pair(inputTerm, outputTerm)) |- witnessMembership) by
              Restate.from(rawCaseToNamedDisjunction.head)
          else
            have(patternMatching.caseMembership(pair(inputTerm, outputTerm)) |- witnessMembership) by
              LeftOr(rawCaseToNamedDisjunction*)

        val witnessToCasesSequent = have(
          (pair(inputTerm, outputTerm) ∈ witness, inputTerm ∈ argType) |- patternMatching.caseMembership(pair(inputTerm, outputTerm))
        ) by Restate.from(witnessToCases)
        have(
          (pair(inputTerm, outputTerm) ∈ witness, inputTerm ∈ argType) |- witnessMembership
        ) by Cut(witnessToCasesSequent, casesToNamed)
        thenHave(
          inputTerm ∈ argType |- pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
        ) by RightImplies

        thenHave(
          ∀(outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
          )
        ) by RightForall
        thenHave(thesis) by Restate
      }

      val quantified = have(
        ∀(inputTerm,
          (inputTerm ∈ argType) ==> ∀(outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
          )
        )
      ) subproof {
        have(
          (inputTerm ∈ argType) ==> ∀(outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
          )
        ) by Restate.from(pointwise)
        thenHave(thesis) by RightForall
      }

      have(thesis) by Restate.from(quantified)
    }
  }

  private val samePatternBodyEquality: Map[Pattern[N], THM] =
    patternMatching.patterns
      .map(pattern =>
        Time.measure("witness/SamePatternBody") {
          val ch = constructorHead(pattern)
          // The *statement* of this lemma is the bare implication over the pattern's
          // own `binders` / `variables2`, because that is exactly the shape
          // `branchAgreement` consumes (propositionally, via `Tautology.from`).
          val canon1 = pattern.binders
          val canon2 = pattern.variables2
          // For the *proof*, we work over genuinely fresh variables.  `binders` and
          // `variables2` are reused by `ch.injectivity` as bound variables (`k`,
          // `k2`); importing a fact whose bound variables clash with names that are
          // free in the ambient proof context makes Restate fail.  Proving a
          // fresh-quantified version first and instantiating it once — at the clean
          // lemma top level — keeps every import capture-free.
          val vars1 = pattern.binders.indices.map(i => variable[Ind](s"${pattern.name}/sbe1_$i"))
          val vars2 = pattern.variables2.indices.map(i => variable[Ind](s"${pattern.name}/sbe2_$i"))
          pattern -> (Lemma(
            (pattern.branchPremiseAt(canon1) /\ pattern.branchPremiseAt(canon2) /\
              (pattern.inputTermAt(canon1) === pattern.inputTermAt(canon2))) |-
              (pattern.bodyAt(canon1) === pattern.bodyAt(canon2))
          ) {
            // Injectivity instantiated at the fresh variables.  Done before any
            // assumption so that the fresh quantifier names are still bound in the
            // goal and cannot clash with `ch.injectivity`'s bound variables.
            val injectivityAtVars = have(
              (pattern.branchPremiseAt(vars1) /\ pattern.branchPremiseAt(vars2)) ==>
                simplify((pattern.inputTermAt(vars1) === pattern.inputTermAt(vars2)) <=> (vars1 === vars2))
            ) by InstantiateForallSeq(vars1 ++ vars2)(ch.injectivity)

            val bodyEquality = have(
              (pattern.branchPremiseAt(vars1) /\ pattern.branchPremiseAt(vars2) /\
                (pattern.inputTermAt(vars1) === pattern.inputTermAt(vars2))) ==>
                (pattern.bodyAt(vars1) === pattern.bodyAt(vars2))
            ) subproof {
              assume(
                pattern.branchPremiseAt(vars1) /\ pattern.branchPremiseAt(vars2) /\
                  (pattern.inputTermAt(vars1) === pattern.inputTermAt(vars2))
              )
              val branch1Premise = have(pattern.branchPremiseAt(vars1)) by Restate.from(lastStep)
              val branch2Premise = have(pattern.branchPremiseAt(vars2)) by Restate.from(lastStep)
              val inputsEqual = have(pattern.inputTermAt(vars1) === pattern.inputTermAt(vars2)) by Restate.from(lastStep)

              val varsEqual = have(vars1 === vars2) by Tautology.from(injectivityAtVars, branch1Premise, branch2Premise, inputsEqual)
              // For multi-argument constructors `vars1 === vars2` is a *conjunction*
              // of pointwise equalities.  Congruence does not split conjunctions, so
              // expose each equality as its own fact before invoking it.
              val componentEqualities = vars1.zip(vars2).map((v1, v2) => have(v1 === v2) by Tautology.from(varsEqual))
              // The body may be a λ-abstraction (when the function returns a
              // function type, e.g. `add : recFun(nat, nat ->: nat)`), and the
              // `Congruence` tactic does not rewrite under binders.  Rewrite
              // `vars1 -> vars2` starting from reflexivity instead: the substitution
              // tactic is capture-avoiding and descends into λ.
              have(pattern.bodyAt(vars1) === pattern.bodyAt(vars1)) by RightRefl
              thenHave(pattern.bodyAt(vars1) === pattern.bodyAt(vars2)) by Substitution.Apply(componentEqualities*)
            }

            have(thesis) by Restate.from(
              bodyEquality.of(
                (vars1 ++ vars2).zip(canon1 ++ canon2).map((from, to) => from := to)*
              )
            )
          })
        }
      )
      .toMap

  // Branch-witness decomposition, pre-split into its three conjuncts so each pair lemma in
  // `branchAgreement` cites exactly the (small) implication it needs, instead of
  // materialising the full conjunction and weakening it apart N² times.
  private case class BranchParts(premise: THM, inputEq: THM, outputEq: THM)

  private def branchDecomposition(
      vars: Pattern[N] => Seq[Variable[Ind]],
      ambientOutput: Expr[Ind]
  ): Map[Pattern[N], BranchParts] =
    patternMatching.patterns
      .map(pattern =>
        val branchVars = vars(pattern)
        val bw = branchWitnessAt(pattern, branchVars, inputTerm, ambientOutput)
        val premise = pattern.branchPremiseAt(branchVars)
        val inputEq = inputTerm === pattern.inputTermAt(branchVars)
        val outputEq = ambientOutput === pattern.bodyAt(branchVars)
        val combined = Lemma(
          bw ==> (premise /\ inputEq /\ outputEq)
        ) {
          have(thesis) by Tautology.from(
            Pair.extensionality of (
              a := inputTerm,
              b := ambientOutput,
              c := pattern.inputTermAt(branchVars),
              d := pattern.bodyAt(branchVars)
            )
          )
        }
        pattern -> BranchParts(
          Lemma(bw ==> premise) { have(thesis) by Weakening(combined) },
          Lemma(bw ==> inputEq) { have(thesis) by Weakening(combined) },
          Lemma(bw ==> outputEq) { have(thesis) by Weakening(combined) }
        )
      )
      .toMap

  private val namedBranchDecomposition: Map[Pattern[N], BranchParts] =
    branchDecomposition(_.binders, outputTerm)

  private val freshBranchDecomposition: Map[Pattern[N], BranchParts] =
    branchDecomposition(_.variables2, alternateOutputTerm)

  private val branchAgreement: Map[(Pattern[N], Pattern[N]), THM] = Time.measure("BranchAgreement") {
    val patterns = patternMatching.patterns
    val builder = scala.collection.mutable.LinkedHashMap.empty[(Pattern[N], Pattern[N]), THM]

    // Full construction of the agreement lemma for `(pattern1, pattern2)`.
    def buildDirect(pattern1: Pattern[N], pattern2: Pattern[N]): THM =
      Time.measure("BranchAgreement inner") {
        val namedBranch = existsSeq(
          pattern1.binders,
          branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm)
        )
        val freshBranch = existsSeq(
          pattern2.variables2,
          branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm)
        )

        var t0 = Time.get()
        val l = Lemma(
          (namedBranch, freshBranch) |- (outputTerm === alternateOutputTerm)
        ) {
          val hyp = assume(namedBranch /\ freshBranch)
          val namedBranchFact = have(namedBranch) by Weakening(hyp)
          val freshBranchFact = have(freshBranch) by Weakening(hyp)

          val namedToGoal = Time.measure("namedToGoal") {
            have(namedBranch |- (outputTerm === alternateOutputTerm)) subproof {
              // As with `freshToGoal` below, do not `assume(namedBranch)` here, so
              // that `namedBranch` is introduced by QuantifiersIntro rather than
              // pre-seeded into `namedDirect`'s context.
              val namedDirect = have(
                branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm) |- (outputTerm === alternateOutputTerm)
              ) subproof {
                assume(branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm))
                val branch1Premise = have(pattern1.branchPremiseAt(pattern1.binders)) by Weakening(namedBranchDecomposition(pattern1).premise)
                val inputEq1 = have(inputTerm === pattern1.inputTermAt(pattern1.binders)) by Weakening(namedBranchDecomposition(pattern1).inputEq)
                val outputEq1 = have(outputTerm === pattern1.bodyAt(pattern1.binders)) by Weakening(namedBranchDecomposition(pattern1).outputEq)

                val freshToGoal = Time.measure("freshToGoal") {
                  val freshDirect = have(
                    branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm) |- (outputTerm === alternateOutputTerm)
                  ) subproof {
                    assume(branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm))
                    val branch2Premise = have(pattern2.branchPremiseAt(pattern2.variables2)) by Weakening(freshBranchDecomposition(pattern2).premise)
                    val inputEq2 = have(inputTerm === pattern2.inputTermAt(pattern2.variables2)) by Weakening(freshBranchDecomposition(pattern2).inputEq)

                    val branchInputsEqual = have(
                      pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2)
                    ) by Congruence.from(inputEq1, inputEq2)

                    if pattern1 == pattern2 then
                      val altEq2 = have(alternateOutputTerm === pattern2.bodyAt(pattern2.variables2)) by 
                        Weakening(freshBranchDecomposition(pattern2).outputEq)
                      val branchConditions = have(branch1Premise.statement.right.head /\ branch2Premise.statement.right.head /\ branchInputsEqual.statement.right.head) by 
                        RightAnd(branch1Premise, branch2Premise, branchInputsEqual)
                      val sameBody = have(
                        pattern1.bodyAt(pattern1.binders) === pattern2.bodyAt(pattern2.variables2)
                      ) by Cut(
                        branchConditions,
                        samePatternBodyEquality(pattern1)
                      )
                      have(outputTerm === alternateOutputTerm) by Congruence.from(outputEq1, sameBody, altEq2)
                    else
                      Time.measure("freshToGoal/inner") {
                        val pattern1Rename =
                          constructorHead(pattern1).variables1.zip(pattern1.binders).map((from, to) => from := to)
                        val incompatibleLemma = patternMatching.incompatible(pattern1, pattern2)

                        val negEq = have(
                          (pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2)) |- ()
                        ) by Tautology.from(incompatibleLemma.of(pattern1Rename*), branch1Premise, branch2Premise)
                        have(outputTerm === alternateOutputTerm) by Cut(branchInputsEqual, negEq)
                      }
                  }
                  have(freshBranch |- (outputTerm === alternateOutputTerm)) by 
                    QuantifiersIntro(pattern2.variables2)(freshDirect)
                }

                have(outputTerm === alternateOutputTerm) by Cut(freshBranchFact, freshToGoal)
                thenHave(thesis) by Restate
              }

              have(thesis) by QuantifiersIntro(pattern1.binders)(namedDirect)
            }
          }

          have(outputTerm === alternateOutputTerm) by Cut(namedBranchFact, namedToGoal)
          thenHave(thesis) by Restate
          t0 = Time.get()
        }
        Time.register("witness/BranchAgreement verification", Time.get() - t0)
        l
      }

    // Derive `(pattern1, pattern2)` from the already-built mirror `(pattern2, pattern1)`.
    // Swapping `outputTerm` and `alternateOutputTerm` turns the mirror statement into this
    // one up to: `/\` commutativity (handled by `Tautology`), α-equivalence of a pattern's
    // `binders` / `variables2` bound names (kernel-level), and `===` symmetry (the final
    // `Congruence` step, since `Tautology`/`Restate` treat `===` as opaque).
    def buildByMirror(pattern1: Pattern[N], pattern2: Pattern[N], mirror: THM): THM =
      Time.measure("witness/BranchAgreement mirror") {
        val namedBranch = existsSeq(
          pattern1.binders,
          branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm)
        )
        val freshBranch = existsSeq(
          pattern2.variables2,
          branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm)
        )
        Lemma(
          (namedBranch, freshBranch) |- (outputTerm === alternateOutputTerm)
        ) {
          have(thesis) by Restate.from(
            mirror of (outputTerm := alternateOutputTerm, alternateOutputTerm := outputTerm)
          )
        }
      }

    for
      i <- patterns.indices
      j <- patterns.indices
    do
      val pattern1 = patterns(i)
      val pattern2 = patterns(j)
      builder((pattern1, pattern2)) =
        if i <= j then buildDirect(pattern1, pattern2)
        else buildByMirror(pattern1, pattern2, builder((pattern2, pattern1)))

    builder.toMap
  }

  private val witnessTotality: THM = Time.measure("witness/Totality") {
    Lemma(
      contextualize(
        ∀(inputTerm ∈ argType, ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
      )
    ) {

      val branchExistenceFacts = patternMatching.patterns.map(pattern =>

        val membershipSchema =
          if contextPremises.isEmpty then
            have(witnessMembership(pattern).statement.right.head) by Tautology.from(witnessMembership(pattern))
          else
            assume(contextPremise)
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
          pattern.variables2.reverse.foldLeft(directBranch)((fact, v) => 
            have(∃(v, fact.statement.left.head) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by LeftExists(fact)
          )
        have(
          existsSeq(
            pattern.variables2,
            pattern.freshBranchPremise /\ (inputTerm === pattern.freshInputTerm)
          ) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
        ) by Restate.from(liftedBranch)
      )

      val coverageToWitness =
        have(simplify(patternMatching.caseCoverage(inputTerm)) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by (
          if branchExistenceFacts.size == 1 then Restate.from(branchExistenceFacts.head)
          else LeftOr(branchExistenceFacts*)
        )

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

  private val witnessSingleValued: THM = Time.measure("witness/SingleValued") {
    Lemma(
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

      val altImp = have(
        (inputTerm ∈ argType) |- (pair(inputTerm, outputTerm) ∈ witness /\
          pair(inputTerm, alternateOutputTerm) ∈ witness) ==> (outputTerm === alternateOutputTerm)
      ) subproof {
        assume(pair(inputTerm, outputTerm) ∈ witness)
        assume(pair(inputTerm, alternateOutputTerm) ∈ witness)
        assume(inputTerm ∈ argType)

        val namedCasesAtInput = have(
          ∀(outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
          )
        ) by InstantiateForall(inputTerm)(witnessMembershipByNamedCases)

        have(
          ∀(alternateOutputTerm,
            pair(inputTerm, alternateOutputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
          )
        ) by InstantiateForall(inputTerm)(witnessMembershipByCases)
        val freshCases = thenHave(
          patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
        ) by InstantiateForall(alternateOutputTerm)

        val namedBranchToGoal = patternMatching.patterns.map(pattern1 =>
          val namedBranch = existsSeq(
            pattern1.binders,
            branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm)
          )

          val freshBranchToGoal = patternMatching.patterns.map(pattern2 => branchAgreement((pattern1, pattern2)))

          val freshDisjunctionToGoal =
            have(
              (namedBranch, patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))) 
              |- (outputTerm === alternateOutputTerm)
            ) by (
              if freshBranchToGoal.size == 1 then Tautology.from(freshBranchToGoal.head)
              else LeftOr(freshBranchToGoal*)
            )

          have(namedBranch |- (outputTerm === alternateOutputTerm)) by Cut(freshCases, freshDisjunctionToGoal)
        )

        val namedDisjunctionToGoal =
          have(witnessMembership |- (outputTerm === alternateOutputTerm)) by (
            if namedBranchToGoal.size == 1 then Restate.from(namedBranchToGoal.head)
            else LeftOr(namedBranchToGoal*)
          )

        have(
          pair(inputTerm, outputTerm) ∈ witness ==> witnessMembership
        ) by InstantiateForall(outputTerm)(namedCasesAtInput)
        val namedCases = 
          thenHave(((inputTerm ∈ argType), pair(inputTerm, outputTerm) ∈ witness) |- witnessMembership) by Restate

        have(((inputTerm ∈ argType), pair(inputTerm, outputTerm) ∈ witness) |- (outputTerm === alternateOutputTerm)) by 
          Cut(namedCases, namedDisjunctionToGoal)
        have(thesis) by Restate.from(lastStep)
      }
      
      val pointwise = have(
        (inputTerm ∈ argType) |- ∀(outputTerm,
          ∀(alternateOutputTerm,
            (pair(inputTerm, outputTerm) ∈ witness /\
              pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
              (outputTerm === alternateOutputTerm)
          )
        )
      ) by Generalize(altImp)

      have(
        (inputTerm ∈ argType) ==> ∀(outputTerm,
          ∀(alternateOutputTerm,
            (pair(inputTerm, outputTerm) ∈ witness /\
              pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
              (outputTerm === alternateOutputTerm)
          )
        )
      ) by Restate.from(pointwise)
      val core = thenHave(
        ∀(inputTerm,
          (inputTerm ∈ argType) ==> ∀(outputTerm,
            ∀(alternateOutputTerm,
              (pair(inputTerm, outputTerm) ∈ witness /\
                pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
                (outputTerm === alternateOutputTerm)
            )
          )
        )
      ) by RightForall

      have(thesis) by Restate.from(core)
    }
  }

  private val witnessUniqueValue: THM = Time.measure("witness/UniqueValue") {
    Lemma(
      contextualize(
        ∀(inputTerm ∈ argType, existsOne(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
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
        (inputTerm ∈ argType) ==> ∀(outputTerm,
          ∀(alternateOutputTerm,
            (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
              (outputTerm === alternateOutputTerm)
          )
        )
      ) by InstantiateForall(inputTerm)(witnessSingleValued)

      val pointwiseUnique = have(
        (inputTerm ∈ argType) ==> existsOne(outputTerm, pointwisePredicate(outputTerm))
      ) by Tautology.from(
        existsOneAlternativeDefinition of (P := λ(outputTerm, pointwisePredicate(outputTerm))),
        totalityAtInput,
        singleValuedAtInput
      )
      
      val core = have(
        ∀(inputTerm, (inputTerm ∈ argType) ==> existsOne(outputTerm, pointwisePredicate(outputTerm)))
      ) by RightForall(pointwiseUnique)

      have(thesis) by Restate.from(core)
    }
  }

  val witnessHasType: THM = Time.measure("witness/HasType") {
    Lemma(contextualize(witness :: typ)) {
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
