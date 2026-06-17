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
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
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

  private val caseMembershipInvariant: THM = Lemma(
    ∀(pairWitness, caseMembership(pairWitness) <=> patternCaseMembership(pairWitness))
  ) {
    have(thesis) by Restate
  }

  private val witnessMembershipByCases: THM = Time.measure("witness/MembershipByCases") {
    Lemma(
      ∀(
        inputTerm ∈ argType,
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
        )
      )
    ) {
      val expandedAtInput = have(
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness <=>
            (pair(inputTerm, outputTerm) ∈ witnessBound /\ caseMembership(pair(inputTerm, outputTerm)))
        )
      ) by InstantiateForall(inputTerm)(witnessMembershipExpanded)

      val pointwise = have(
        (inputTerm ∈ argType) |- ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
        )
      ) subproof {
        assume(inputTerm ∈ argType)
        have(
          pair(inputTerm, outputTerm) ∈ witness <=>
            (pair(inputTerm, outputTerm) ∈ witnessBound /\ caseMembership(pair(inputTerm, outputTerm)))
        ) by InstantiateForall(outputTerm)(expandedAtInput)
        val witnessImpliesRawCase = have(
          pair(inputTerm, outputTerm) ∈ witness ==> caseMembership(pair(inputTerm, outputTerm))
        ) by Tautology.from(lastStep)
        val invariantAtPair = have(
          caseMembership(pair(inputTerm, outputTerm)) <=> patternCaseMembership(pair(inputTerm, outputTerm))
        ) by InstantiateForall(pair(inputTerm, outputTerm))(caseMembershipInvariant)
        val rawToPatternCases = have(
          caseMembership(pair(inputTerm, outputTerm)) ==> patternCaseMembership(pair(inputTerm, outputTerm))
        ) by Restate.from(invariantAtPair)
        have(
          pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
        ) by Tautology.from(witnessImpliesRawCase, rawToPatternCases)
        thenHave(
          ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
          )
        ) by RightForall
        thenHave(thesis) by Restate
      }

      val quantified = have(
        ∀(
          inputTerm,
          (inputTerm ∈ argType) ==> ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
          )
        )
      ) subproof {
        have(
          (inputTerm ∈ argType) ==> ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
          )
        ) by Restate.from(pointwise)
        thenHave(thesis) by RightForall
      }

      have(thesis) by Restate.from(quantified)
    }
  }

  private val witnessMembershipByNamedCases: THM = Time.measure("witness/MembershipByNamedCases") {
    Lemma(
      ∀(
        inputTerm ∈ argType,
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
        )
      )
    ) {
      val pointwise = have(
        (inputTerm ∈ argType) |- ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
        )
      ) subproof {
        assume(inputTerm ∈ argType)
        val rawCasesAtInput = have(
          ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
          )
        ) by Restate.from(
          have(
            (inputTerm ∈ argType) ==> ∀(
              outputTerm,
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

        val namedCaseDisjunction =
          seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))

        val rawCaseToNamedDisjunction = rawCaseToNamedCases.map(fact => have(fact.statement.left.head |- namedCaseDisjunction) by Restate.from(fact))

        val casesToNamed =
          if rawCaseToNamedDisjunction.size == 1 then
            have(patternMatching.caseMembership(pair(inputTerm, outputTerm)) |- namedCaseDisjunction) by
              Restate.from(rawCaseToNamedDisjunction.head)
          else
            have(patternMatching.caseMembership(pair(inputTerm, outputTerm)) |- namedCaseDisjunction) by
              LeftOr(rawCaseToNamedDisjunction*)

        val witnessToCasesSequent = have(
          (pair(inputTerm, outputTerm) ∈ witness, inputTerm ∈ argType) |- patternMatching.caseMembership(pair(inputTerm, outputTerm))
        ) by Restate.from(witnessToCases)
        have(
          (pair(inputTerm, outputTerm) ∈ witness, inputTerm ∈ argType) |- namedCaseDisjunction
        ) by Cut(witnessToCasesSequent, casesToNamed)
        thenHave(
          inputTerm ∈ argType |- pair(inputTerm, outputTerm) ∈ witness ==> namedCaseDisjunction
        ) by RightImplies

        thenHave(
          ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
          )
        ) by RightForall
        thenHave(thesis) by Restate
      }

      val quantified = have(
        ∀(
          inputTerm,
          (inputTerm ∈ argType) ==> ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
          )
        )
      ) subproof {
        have(
          (inputTerm ∈ argType) ==> ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
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
              (pattern.inputTermAt(canon1) === pattern.inputTermAt(canon2))) ==>
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
          assume(bw)
          val pairEq = have(
            pair(inputTerm, ambientOutput) === pair(pattern.inputTermAt(branchVars), pattern.bodyAt(branchVars))
          ) by Restate.from(lastStep)
          val pairSplit = have(
            inputEq /\ outputEq
          ) by Tautology.from(
            pairEq,
            Pair.extensionality of (
              a := inputTerm,
              b := ambientOutput,
              c := pattern.inputTermAt(branchVars),
              d := pattern.bodyAt(branchVars)
            )
          )
          have(thesis) by Tautology.from(pairSplit)
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
          (namedBranch /\ freshBranch) ==> (outputTerm === alternateOutputTerm)
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
                  have(freshBranch |- (outputTerm === alternateOutputTerm)) subproof {
                    // Do NOT `assume(freshBranch)` here: that would seed `freshBranch`
                    // (= ∃(variables2, branchWitnessAt)) into the context, so it would
                    // already sit on `freshDirect`'s left.  QuantifiersIntro then sees
                    // an empty diff and degenerates into a Restate that must drop a
                    // hypothesis (impossible).  Instead let QuantifiersIntro introduce
                    // the existential from the bare `freshDirect`.
                    val freshDirect = have(
                      branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm) |- (outputTerm === alternateOutputTerm)
                    ) subproof {
                      assume(branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm))
                      val branch2Premise = have(pattern2.branchPremiseAt(pattern2.variables2)) by Weakening(freshBranchDecomposition(pattern2).premise)
                      val inputEq2 = have(inputTerm === pattern2.inputTermAt(pattern2.variables2)) by Weakening(freshBranchDecomposition(pattern2).inputEq)
                      val altEq2 = have(alternateOutputTerm === pattern2.bodyAt(pattern2.variables2)) by Weakening(freshBranchDecomposition(pattern2).outputEq)

                      // `inputTerm = p1.input` and `inputTerm = p2.input` give `p1.input = p2.input`
                      // directly by congruence (no explicit transitivity lemma / symmetry step).
                      val branchInputsEqual = have(
                        pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2)
                      ) by Congruence.from(inputEq1, inputEq2)

                      if pattern1 == pattern2 then
                        val sameBody = have(
                          pattern1.bodyAt(pattern1.binders) === pattern2.bodyAt(pattern2.variables2)
                        ) by Tautology.from(
                          samePatternBodyEquality(pattern1),
                          branch1Premise,
                          branch2Premise,
                          branchInputsEqual
                        )
                        // output = p1.body = p2.body = alt, chained in one congruence step.
                        have(outputTerm === alternateOutputTerm) by Congruence.from(outputEq1, sameBody, altEq2)
                      else
                        // `incompatible` states its pattern1 side over `variables1`
                        // (the constructor's canonical variables), whereas here
                        // pattern1 appears over its `binders`.  Rename
                        // `variables1 -> binders` before using it.
                        Time.measure("freshToGoal/inner") {
                          val pattern1Rename =
                            Time.measure("renaming")(constructorHead(pattern1).variables1.zip(pattern1.binders).map((from, to) => from := to))
                          val incompatibleLemma = patternMatching.incompatible(pattern1, pattern2)
                          val incompatibleAtBranches = Time.measure("incompatible at branches") {
                            have(
                              (pattern1.branchPremiseAt(pattern1.binders) /\ pattern2.branchPremiseAt(pattern2.variables2)) ==>
                                !(pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2))
                            ) by Tautology.from(incompatibleLemma.of(pattern1Rename*))
                          }

                          val branchInputsDifferent = have(
                            pattern1.inputTermAt(pattern1.binders) =/= pattern2.inputTermAt(pattern2.variables2)
                          ) by Tautology.from(incompatibleAtBranches, branch1Premise, branch2Premise)

                          val negEq = have(
                            (pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2)) |- ()
                          ) by Restate.from(branchInputsDifferent)
                          have(outputTerm === alternateOutputTerm) by Cut(branchInputsEqual, negEq)
                        }
                    }

                    have(thesis) by QuantifiersIntro(pattern2.variables2)(freshDirect)
                  }
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
          (namedBranch /\ freshBranch) ==> (outputTerm === alternateOutputTerm)
        ) {
          assume(namedBranch /\ freshBranch)
          val reversed = have(alternateOutputTerm === outputTerm) by Tautology.from(
            mirror of (outputTerm := alternateOutputTerm, alternateOutputTerm := outputTerm)
          )
          have(outputTerm === alternateOutputTerm) by Congruence.from(reversed)
          thenHave(thesis) by Restate
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

  private val witnessRelationBetween: THM =
    Time.measure("witness/RelationBetween") {
      Lemma(relationBetween(witness)(argType)(returnType)) {
        have(witnessBody ⊆ witnessBound) by Restate.from(
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
    }

  private val witnessTotality: THM = Time.measure("witness/Totality") {
    Lemma(
      contextualize(
        ∀(inputTerm ∈ argType, ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
      )
    ) {
      val contextHyp =
        if contextPremises.isEmpty then None else Some(assume(contextPremise))

      val coverageAtInput = have(
        (inputTerm ∈ argType) ==> simplify(patternMatching.caseCoverage(inputTerm))
      ) by InstantiateForall(inputTerm)(patternMatching.coverage)

      val pointwise = have(
        (inputTerm ∈ argType) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
      ) subproof {
        assume(inputTerm ∈ argType)
        val coveredInput = have(simplify(patternMatching.caseCoverage(inputTerm))) by
          Restate.from(coverageAtInput)

        val branchExistenceFacts = patternMatching.patterns.map(pattern =>
          val branchCase = existsSeq(
            pattern.variables2,
            pattern.freshBranchPremise /\ (inputTerm === pattern.freshInputTerm)
          )

          have(branchCase |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) subproof {
            assume(branchCase)
            val directBranch = have(
              pattern.freshBranchPremise /\ (inputTerm === pattern.freshInputTerm) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
            ) subproof {
              assume(pattern.freshBranchPremise /\ (inputTerm === pattern.freshInputTerm))
              val freshPremise = have(pattern.freshBranchPremise) by Restate.from(lastStep)
              val inputEqFresh = have(inputTerm === pattern.freshInputTerm) by Restate.from(lastStep)

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

              val freshMembership = have(
                pattern.freshBranchPremise ==> pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2) ∈ witness
              ) by InstantiateForallSeq(pattern.variables2)(membershipSchema)

              val freshPairInWitness = have(
                pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2) ∈ witness
              ) by Tautology.from(freshMembership, freshPremise)

              have(
                pair(inputTerm, pattern.bodyAtFreshVars2) ∈ witness
              ) by Congruence.from(inputEqFresh, freshPairInWitness)

              thenHave(∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by RightExists
            }

            val liftedBranch =
              pattern.variables2.reverse.foldLeft(directBranch)((fact, v) => thenHave(∃(v, fact.statement.left.head) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by LeftExists)

            have(thesis) by Restate.from(liftedBranch)
          }
        )

        val coverageToWitness =
          if branchExistenceFacts.size == 1 then
            have(simplify(patternMatching.caseCoverage(inputTerm)) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by
              Restate.from(branchExistenceFacts.head)
          else
            have(simplify(patternMatching.caseCoverage(inputTerm)) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by
              LeftOr(branchExistenceFacts*)

        have(∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by
          Cut(coveredInput, coverageToWitness)
        thenHave(thesis) by Restate
      }

      val core = have(
        ∀(inputTerm, (inputTerm ∈ argType) ==> ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
      ) subproof {
        have((inputTerm ∈ argType) ==> ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by
          Restate.from(pointwise)
        thenHave(thesis) by RightForall
      }

      have(thesis) by Restate.from(core)
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
      val pointwise = have(
        (inputTerm ∈ argType) |- ∀(
          outputTerm,
          ∀(
            alternateOutputTerm,
            (pair(inputTerm, outputTerm) ∈ witness /\
              pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
              (outputTerm === alternateOutputTerm)
          )
        )
      ) subproof {
        assume(inputTerm ∈ argType)
        val namedCasesAtInput = have(
          ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
          )
        ) by Restate.from(
          have(
            (inputTerm ∈ argType) ==> ∀(
              outputTerm,
              pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
            )
          ) by InstantiateForall(inputTerm)(witnessMembershipByNamedCases)
        )

        val freshCasesAtInput = have(
          ∀(
            alternateOutputTerm,
            pair(inputTerm, alternateOutputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
          )
        ) by Restate.from(
          have(
            (inputTerm ∈ argType) ==> ∀(
              alternateOutputTerm,
              pair(inputTerm, alternateOutputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
            )
          ) by InstantiateForall(inputTerm)(witnessMembershipByCases)
        )

        val outputLevel = have(
          pair(inputTerm, outputTerm) ∈ witness |- ∀(
            alternateOutputTerm,
            (pair(inputTerm, outputTerm) ∈ witness /\
              pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
              (outputTerm === alternateOutputTerm)
          )
        ) subproof {
          assume(pair(inputTerm, outputTerm) ∈ witness)

          val namedCases = have(
            seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
          ) by Restate.from(
            have(
              pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))))
            ) by InstantiateForall(outputTerm)(namedCasesAtInput)
          )

          val altLevel = have(
            ∀(
              alternateOutputTerm,
              (pair(inputTerm, outputTerm) ∈ witness /\
                pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
                (outputTerm === alternateOutputTerm)
            )
          ) subproof {
            val altImp = have(
              (pair(inputTerm, outputTerm) ∈ witness /\
                pair(inputTerm, alternateOutputTerm) ∈ witness) ==> (outputTerm === alternateOutputTerm)
            ) subproof {
              assume(
                pair(inputTerm, outputTerm) ∈ witness /\
                  pair(inputTerm, alternateOutputTerm) ∈ witness
              )
              val altWitness = have(pair(inputTerm, alternateOutputTerm) ∈ witness) by Restate.from(lastStep)
              val freshCases = have(
                patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
              ) by Tautology.from(
                have(
                  pair(inputTerm, alternateOutputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
                ) by InstantiateForall(alternateOutputTerm)(freshCasesAtInput),
                altWitness
              )

              val namedBranchToGoal = patternMatching.patterns.map(pattern1 =>
                val namedBranch = existsSeq(
                  pattern1.binders,
                  branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm)
                )

                have(namedBranch |- (outputTerm === alternateOutputTerm)) subproof {
                  assume(namedBranch)

                  val freshBranchToGoal = patternMatching.patterns.map(pattern2 =>
                    val freshBranch = existsSeq(
                      pattern2.variables2,
                      branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm)
                    )

                    have(freshBranch |- (outputTerm === alternateOutputTerm)) by Tautology.from(
                      branchAgreement((pattern1, pattern2)),
                      have(namedBranch) by Hypothesis
                    )
                  )

                  val freshDisjunctionToGoal =
                    if freshBranchToGoal.size == 1 then
                      have(patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm)) |- (outputTerm === alternateOutputTerm)) by
                        Restate.from(freshBranchToGoal.head)
                    else
                      have(patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm)) |- (outputTerm === alternateOutputTerm)) by
                        LeftOr(freshBranchToGoal*)

                  have(outputTerm === alternateOutputTerm) by Cut(freshCases, freshDisjunctionToGoal)
                  thenHave(thesis) by Restate
                }
              )

              val namedDisjunctionToGoal =
                if namedBranchToGoal.size == 1 then
                  have(
                    seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm)))) |- (outputTerm === alternateOutputTerm)
                  ) by Restate.from(namedBranchToGoal.head)
                else
                  have(
                    seqOr(patternMatching.patterns.map(pattern => existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm)))) |- (outputTerm === alternateOutputTerm)
                  ) by LeftOr(namedBranchToGoal*)

              have(outputTerm === alternateOutputTerm) by Cut(namedCases, namedDisjunctionToGoal)
              have(thesis) by Restate.from(lastStep)
            }
            have(thesis) by RightForall(altImp)
          }

          have(
            pair(inputTerm, outputTerm) ∈ witness ==> ∀(
              alternateOutputTerm,
              (pair(inputTerm, outputTerm) ∈ witness /\
                pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
                (outputTerm === alternateOutputTerm)
            )
          ) subproof {
            have(
              ∀(
                alternateOutputTerm,
                (pair(inputTerm, outputTerm) ∈ witness /\
                  pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
                  (outputTerm === alternateOutputTerm)
              )
            ) by Restate.from(altLevel)
            have(thesis) by Restate.from(lastStep)
          }
          thenHave(thesis) by Restate
        }

        have(
          pair(inputTerm, outputTerm) ∈ witness |-
            (pair(inputTerm, outputTerm) ∈ witness /\
              pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
            (outputTerm === alternateOutputTerm)
        ) by InstantiateForall(alternateOutputTerm)(outputLevel)
        thenHave(
          (pair(inputTerm, outputTerm) ∈ witness /\
            pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
            (outputTerm === alternateOutputTerm)
        ) by Restate
        thenHave(
          ∀(
            alternateOutputTerm,
            (pair(inputTerm, outputTerm) ∈ witness /\
              pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
              (outputTerm === alternateOutputTerm)
          )
        ) by RightForall
        thenHave(thesis) by RightForall
      }

      val core = have(
        ∀(
          inputTerm,
          (inputTerm ∈ argType) ==> ∀(
            outputTerm,
            ∀(
              alternateOutputTerm,
              (pair(inputTerm, outputTerm) ∈ witness /\
                pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
                (outputTerm === alternateOutputTerm)
            )
          )
        )
      ) subproof {
        have(
          (inputTerm ∈ argType) ==> ∀(
            outputTerm,
            ∀(
              alternateOutputTerm,
              (pair(inputTerm, outputTerm) ∈ witness /\
                pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
                (outputTerm === alternateOutputTerm)
            )
          )
        ) by Restate.from(pointwise)
        thenHave(thesis) by RightForall
      }

      have(thesis) by Restate.from(core)
    }
  }

  private val witnessUniqueValue: THM = Time.measure("witness/UniqueValue") {
    Lemma(
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
          Restate.from(totalityAtInput)
        val functionalityAtInput = have(
          ∀(
            outputTerm,
            ∀(
              alternateOutputTerm,
              (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
                (outputTerm === alternateOutputTerm)
            )
          )
        ) by Restate.from(singleValuedAtInput)
        // `existsOne ⟺ existence ∧ uniqueness` is a generic fact about `∃!`; cite it
        // instead of re-deriving the introduction by hand.
        have(existsOne(outputTerm, pointwisePredicate(outputTerm))) by Tautology.from(
          existsOneAlternativeDefinition of (P := λ(outputTerm, pointwisePredicate(outputTerm))),
          existenceAtInput,
          functionalityAtInput
        )
        thenHave(thesis) by Restate
      }

      val core = have(
        ∀(inputTerm, (inputTerm ∈ argType) ==> existsOne(outputTerm, pointwisePredicate(outputTerm)))
      ) subproof {
        have((inputTerm ∈ argType) ==> existsOne(outputTerm, pointwisePredicate(outputTerm))) by
          Restate.from(pointwiseUnique)
        thenHave(thesis) by RightForall
      }

      have(thesis) by Restate.from(core)
    }
  }

  val witnessHasType: THM = Time.measure("witness/HasType") {
    Lemma(contextualize(witness :: typ)) {
      val contextHyp =
        if contextPremises.isEmpty then None else Some(assume(contextPremise))
      if contextPremises.isEmpty then
        have(
          ∀(inputTerm ∈ argType, existsOne(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
        ) by Restate.from(witnessUniqueValue)
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
  }
}
