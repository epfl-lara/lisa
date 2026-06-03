package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.{InstantiateForallSeq, QuantifiersIntro}
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.{Comprehension, Pair}
import lisa.maths.SetTheory.Base.Symbols.{X, Y, φ}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.maths.SetTheory.Relations.Relation.{R, relationBetween}
import lisa.maths.Quantifiers.∃!
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.BasicStepTactic.RightRefl
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.automation.Substitution
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall
private[proofs] trait WitnessFunctionProofs[N <: Arity] extends WitnessBranchMembership[N] {

  private def branchWitnessAt(
      pattern: Pattern[N],
      vars: Seq[Variable[Ind]],
      ambientInput: Expr[Ind],
      ambientOutput: Expr[Ind]
  ): Expr[Prop] =
    pattern.branchPremiseAt(vars) /\
      (pair(ambientInput, ambientOutput) === pair(pattern.inputTermAt(vars), pattern.bodyAt(vars)))

  val caseMembershipInvariant: THM = Lemma(
    ∀(pairWitness, caseMembership(pairWitness) <=> patternCaseMembership(pairWitness))
  ) {
    have(thesis) by Tautology
  }

  val witnessMembershipExpanded: THM = Lemma(
    ∀(
      inputTerm,
      ∀(
        outputTerm,
        pair(inputTerm, outputTerm) ∈ witness <=>
          (pair(inputTerm, outputTerm) ∈ witnessBound /\ caseMembership(pair(inputTerm, outputTerm)))
      )
    )
  ) {
    val pairTerm = pair(inputTerm, outputTerm)

    have(
      pairTerm ∈ witnessBody <=> (pairTerm ∈ witnessBound /\ caseMembership(pairTerm))
    ) by Tautology.from(
      Comprehension.membership of (
        x := pairTerm,
        y := witnessBound,
        φ := λ(pairWitness, caseMembership(pairWitness))
      )
    )

    val pointwise = have(
      pairTerm ∈ witness <=>
        (pairTerm ∈ witnessBound /\ caseMembership(pairTerm))
    ) by Congruence.from(witnessDef, lastStep)

    val quantified = have(
      ∀(
        inputTerm,
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness <=>
            (pair(inputTerm, outputTerm) ∈ witnessBound /\ caseMembership(pair(inputTerm, outputTerm)))
        )
      )
    ) subproof {
      have(
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness <=>
            (pair(inputTerm, outputTerm) ∈ witnessBound /\ caseMembership(pair(inputTerm, outputTerm)))
        )
      ) by RightForall(pointwise)
      thenHave(thesis) by RightForall
    }

    have(thesis) by Restate.from(quantified)
  }

  val witnessMembershipByCases: THM = Lemma(
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
      ) by Tautology.from(invariantAtPair)
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

  val witnessMembershipByNamedCases: THM = Lemma(
    ∀(
      inputTerm ∈ argType,
      ∀(
        outputTerm,
        pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
          existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
        ))
      )
    )
  ) {
    val pointwise = have(
      (inputTerm ∈ argType) |- ∀(
        outputTerm,
        pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
          existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
        ))
      )
    ) subproof {
      assume(inputTerm ∈ argType)
      val rawCasesAtInput = have(
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, outputTerm))
        )
      ) by Tautology.from(
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
            ) by Tautology.from(lastStep)
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
            have(namedBranch) by Tautology.from(raw)
            thenHave(thesis) by Restate
          }

          val liftedBranch = pattern.variables2.reverse.foldLeft(directBranch)((fact, v) =>
            thenHave(∃(v, fact.statement.left.head) |- namedBranch) by LeftExists
          )
          have(thesis) by Tautology.from(liftedBranch)
        }
      )

      val namedCaseDisjunction =
        seqOr(patternMatching.patterns.map(pattern =>
          existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
        ))

      val rawCaseToNamedDisjunction = rawCaseToNamedCases.map(fact =>
        have(fact.statement.left.head |- namedCaseDisjunction) by Tautology.from(fact)
      )

      val casesToNamed =
        if rawCaseToNamedDisjunction.size == 1 then
          have(patternMatching.caseMembership(pair(inputTerm, outputTerm)) |- namedCaseDisjunction) by
            Restate.from(rawCaseToNamedDisjunction.head)
        else
          have(patternMatching.caseMembership(pair(inputTerm, outputTerm)) |- namedCaseDisjunction) by
            LeftOr(rawCaseToNamedDisjunction*)

      val witnessToCasesSequent = have(
        (pair(inputTerm, outputTerm) ∈ witness, inputTerm ∈ argType) |- patternMatching.caseMembership(pair(inputTerm, outputTerm))
      ) by Tautology.from(witnessToCases)
      have(
        (pair(inputTerm, outputTerm) ∈ witness, inputTerm ∈ argType) |- namedCaseDisjunction
      ) by Cut(witnessToCasesSequent, casesToNamed)
      thenHave(
        inputTerm ∈ argType |- pair(inputTerm, outputTerm) ∈ witness ==> namedCaseDisjunction
      ) by RightImplies

      thenHave(
        ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
            existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
          ))
        )
      ) by RightForall
      thenHave(thesis) by Restate
    }

    val quantified = have(
      ∀(
        inputTerm,
        (inputTerm ∈ argType) ==> ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
            existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
          ))
        )
      )
    ) subproof {
      have(
        (inputTerm ∈ argType) ==> ∀(
          outputTerm,
          pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
            existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
          ))
        )
      ) by Restate.from(pointwise)
      thenHave(thesis) by RightForall
    }

    have(thesis) by Restate.from(quantified)
  }

  val samePatternBodyEquality: Map[Pattern[N], THM] =
    patternMatching.patterns.map(pattern =>
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
          val branch1Premise = have(pattern.branchPremiseAt(vars1)) by Tautology.from(lastStep)
          val branch2Premise = have(pattern.branchPremiseAt(vars2)) by Tautology.from(lastStep)
          val inputsEqual = have(pattern.inputTermAt(vars1) === pattern.inputTermAt(vars2)) by Tautology.from(lastStep)

          val varsEqual = have(vars1 === vars2) by Tautology.from(injectivityAtVars, branch1Premise, branch2Premise, inputsEqual)
          // For multi-argument constructors `vars1 === vars2` is a *conjunction*
          // of pointwise equalities.  Congruence does not split conjunctions, so
          // expose each equality as its own fact before invoking it.
          val componentEqualities = vars1.zip(vars2).map((v1, v2) =>
            have(v1 === v2) by Tautology.from(varsEqual)
          )
          // The body may be a λ-abstraction (when the function returns a
          // function type, e.g. `add : recFun(nat, nat ->: nat)`), and the
          // `Congruence` tactic does not rewrite under binders.  Rewrite
          // `vars1 -> vars2` starting from reflexivity instead: the substitution
          // tactic is capture-avoiding and descends into λ.
          have(pattern.bodyAt(vars1) === pattern.bodyAt(vars1)) by RightRefl
          thenHave(pattern.bodyAt(vars1) === pattern.bodyAt(vars2)) by Substitution.Apply(componentEqualities*)
        }

        // Generalise over the fresh variables, then instantiate at the pattern's
        // canonical `binders` / `variables2` to obtain the lemma statement.
        val quantified = have(
          forallSeq(
            vars1 ++ vars2,
            (pattern.branchPremiseAt(vars1) /\ pattern.branchPremiseAt(vars2) /\
              (pattern.inputTermAt(vars1) === pattern.inputTermAt(vars2))) ==>
              (pattern.bodyAt(vars1) === pattern.bodyAt(vars2))
          )
        ) by QuantifiersIntro(vars1 ++ vars2)(bodyEquality)

        have(thesis) by InstantiateForallSeq(canon1 ++ canon2)(quantified)
      })
    ).toMap

  val branchAgreement: Map[(Pattern[N], Pattern[N]), THM] =
    (for
      pattern1 <- patternMatching.patterns
      pattern2 <- patternMatching.patterns
    yield (pattern1, pattern2) -> {
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
        val namedBranchFact = have(namedBranch) by Tautology.from(lastStep)
        val freshBranchFact = have(freshBranch) by Tautology.from(lastStep)

        val namedToGoal = have(namedBranch |- (outputTerm === alternateOutputTerm)) subproof {
          // As with `freshToGoal` below, do not `assume(namedBranch)` here, so
          // that `namedBranch` is introduced by QuantifiersIntro rather than
          // pre-seeded into `namedDirect`'s context.
          val namedDirect = have(
            branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm) |- (outputTerm === alternateOutputTerm)
          ) subproof {
            assume(branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm))
            val branch1 = have(branchWitnessAt(pattern1, pattern1.binders, inputTerm, outputTerm)) by Hypothesis
            val branch1Premise = have(pattern1.branchPremiseAt(pattern1.binders)) by Tautology.from(branch1)
            val pairEq1 = have(
              pair(inputTerm, outputTerm) === pair(pattern1.inputTermAt(pattern1.binders), pattern1.bodyAt(pattern1.binders))
            ) by Tautology.from(branch1)
            val pairSplit1 = have(
              (inputTerm === pattern1.inputTermAt(pattern1.binders)) /\
                (outputTerm === pattern1.bodyAt(pattern1.binders))
            ) by Tautology.from(
              pairEq1,
              Pair.extensionality of (
                a := inputTerm,
                b := outputTerm,
                c := pattern1.inputTermAt(pattern1.binders),
                d := pattern1.bodyAt(pattern1.binders)
              )
            )
            val inputEq1 = have(inputTerm === pattern1.inputTermAt(pattern1.binders)) by Tautology.from(pairSplit1)
            val outputEq1 = have(outputTerm === pattern1.bodyAt(pattern1.binders)) by Tautology.from(pairSplit1)

            val freshToGoal = have(freshBranch |- (outputTerm === alternateOutputTerm)) subproof {
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
                val branch2 = have(branchWitnessAt(pattern2, pattern2.variables2, inputTerm, alternateOutputTerm)) by Hypothesis
                val branch2Premise = have(pattern2.branchPremiseAt(pattern2.variables2)) by Tautology.from(branch2)
                val pairEq2 = have(
                  pair(inputTerm, alternateOutputTerm) === pair(pattern2.inputTermAt(pattern2.variables2), pattern2.bodyAt(pattern2.variables2))
                ) by Tautology.from(branch2)
                val pairSplit2 = have(
                  (inputTerm === pattern2.inputTermAt(pattern2.variables2)) /\
                    (alternateOutputTerm === pattern2.bodyAt(pattern2.variables2))
                ) by Tautology.from(
                  pairEq2,
                  Pair.extensionality of (
                    a := inputTerm,
                    b := alternateOutputTerm,
                    c := pattern2.inputTermAt(pattern2.variables2),
                    d := pattern2.bodyAt(pattern2.variables2)
                  )
                )
                val inputEq2 = have(inputTerm === pattern2.inputTermAt(pattern2.variables2)) by Tautology.from(pairSplit2)
                val altEq2 = have(alternateOutputTerm === pattern2.bodyAt(pattern2.variables2)) by Tautology.from(pairSplit2)

                if pattern1 == pattern2 then
                  val inputEq1Rev = have(pattern1.inputTermAt(pattern1.binders) === inputTerm) by Congruence.from(inputEq1)
                  val branchInputsEqual = have(
                    pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2)
                  ) by Tautology.from(
                    altEqualityTransitivity of (
                      x := pattern1.inputTermAt(pattern1.binders),
                      y := inputTerm,
                      z := pattern2.inputTermAt(pattern2.variables2)
                    ),
                    inputEq1Rev,
                    inputEq2
                  )

                  val sameBody = have(
                    pattern1.bodyAt(pattern1.binders) === pattern2.bodyAt(pattern2.variables2)
                  ) by Tautology.from(
                    samePatternBodyEquality(pattern1),
                    branch1Premise,
                    branch2Premise,
                    branchInputsEqual
                  )

                  val bodyToAlt = have(
                    pattern1.bodyAt(pattern1.binders) === alternateOutputTerm
                  ) by Tautology.from(
                    altEqualityTransitivity of (
                      x := pattern1.bodyAt(pattern1.binders),
                      y := pattern2.bodyAt(pattern2.variables2),
                      z := alternateOutputTerm
                    ),
                    sameBody,
                    have(pattern2.bodyAt(pattern2.variables2) === alternateOutputTerm) by Congruence.from(altEq2)
                  )

                  have(outputTerm === alternateOutputTerm) by Tautology.from(
                    altEqualityTransitivity of (
                      x := outputTerm,
                      y := pattern1.bodyAt(pattern1.binders),
                      z := alternateOutputTerm
                    ),
                    outputEq1,
                    bodyToAlt
                  )
                else
                  val inputEq1Rev = have(pattern1.inputTermAt(pattern1.binders) === inputTerm) by Congruence.from(inputEq1)
                  val branchInputsEqual = have(
                    pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2)
                  ) by Tautology.from(
                    altEqualityTransitivity of (
                      x := pattern1.inputTermAt(pattern1.binders),
                      y := inputTerm,
                      z := pattern2.inputTermAt(pattern2.variables2)
                    ),
                    inputEq1Rev,
                    inputEq2
                  )

                  // `incompatible` states its pattern1 side over `variables1`
                  // (the constructor's canonical variables), whereas here
                  // pattern1 appears over its `binders`.  Rename
                  // `variables1 -> binders` before using it.
                  val pattern1Rename =
                    constructorHead(pattern1).variables1.zip(pattern1.binders).map((from, to) => from := to)
                  val incompatibleAtBranches = have(
                    (pattern1.branchPremiseAt(pattern1.binders) /\ pattern2.branchPremiseAt(pattern2.variables2)) ==>
                      !(pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2))
                  ) by Tautology.from(patternMatching.incompatible(pattern1, pattern2).of(pattern1Rename*))

                  val branchInputsDifferent = have(
                    !(pattern1.inputTermAt(pattern1.binders) === pattern2.inputTermAt(pattern2.variables2))
                  ) by Tautology.from(incompatibleAtBranches, branch1Premise, branch2Premise)

                  have(outputTerm === alternateOutputTerm) by Tautology.from(branchInputsEqual, branchInputsDifferent)
              }

              have(thesis) by QuantifiersIntro(pattern2.variables2)(freshDirect)
            }

            have(outputTerm === alternateOutputTerm) by Cut(freshBranchFact, freshToGoal)
            thenHave(thesis) by Restate
          }

          have(thesis) by QuantifiersIntro(pattern1.binders)(namedDirect)
        }

        have(outputTerm === alternateOutputTerm) by Cut(namedBranchFact, namedToGoal)
        have(thesis) by Tautology.from(lastStep)
      }
    }).toMap

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
    val contextHyp =
      if contextPremises.isEmpty then None else Some(assume(contextPremise))

    val coverageAtInput = have(
      (inputTerm ∈ argType) ==> simplify(patternMatching.caseCoverage(inputTerm))
    ) by InstantiateForall(inputTerm)(patternMatching.coverage(adt))

    val pointwise = have(
      (inputTerm ∈ argType) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
    ) subproof {
      assume(inputTerm ∈ argType)
      val coveredInput = have(simplify(patternMatching.caseCoverage(inputTerm))) by
        Tautology.from(coverageAtInput)

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
            val freshPremise = have(pattern.freshBranchPremise) by Tautology.from(lastStep)
            val inputEqFresh = have(inputTerm === pattern.freshInputTerm) by Tautology.from(lastStep)

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

            val selectedPairInWitness = have(
              pair(inputTerm, pattern.bodyAtFreshVars2) ∈ witness
            ) by Congruence.from(inputEqFresh, freshPairInWitness)

            thenHave(∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by RightExists
          }

          val liftedBranch = pattern.variables2.reverse.foldLeft(directBranch)((fact, v) =>
            thenHave(∃(v, fact.statement.left.head) |- ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by LeftExists
          )

          have(thesis) by Tautology.from(liftedBranch)
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
        Tautology.from(coveredInput, coverageToWitness)
      thenHave(thesis) by Restate
    }

    val core = have(
      ∀(inputTerm, (inputTerm ∈ argType) ==> ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
    ) subproof {
      have((inputTerm ∈ argType) ==> ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)) by
        Restate.from(pointwise)
      thenHave(thesis) by RightForall
    }

    if contextPremises.isEmpty then have(thesis) by Restate.from(core)
    else have(thesis) by Tautology.from(contextHyp.get, core)
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
          pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
            existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
          ))
        )
      ) by Tautology.from(
        have(
          (inputTerm ∈ argType) ==> ∀(
            outputTerm,
            pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
              existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
            ))
          )
        ) by InstantiateForall(inputTerm)(witnessMembershipByNamedCases)
      )

      val freshCasesAtInput = have(
        ∀(
          alternateOutputTerm,
          pair(inputTerm, alternateOutputTerm) ∈ witness ==> patternMatching.caseMembership(pair(inputTerm, alternateOutputTerm))
        )
      ) by Tautology.from(
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
          seqOr(patternMatching.patterns.map(pattern =>
            existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
          ))
        ) by Tautology.from(
          have(
            pair(inputTerm, outputTerm) ∈ witness ==> seqOr(patternMatching.patterns.map(pattern =>
              existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
            ))
          ) by InstantiateForall(outputTerm)(namedCasesAtInput),
          have(pair(inputTerm, outputTerm) ∈ witness) by Hypothesis
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
            val altWitness = have(pair(inputTerm, alternateOutputTerm) ∈ witness) by Tautology.from(lastStep)
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
                  seqOr(patternMatching.patterns.map(pattern =>
                    existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
                  )) |- (outputTerm === alternateOutputTerm)
                ) by Restate.from(namedBranchToGoal.head)
              else
                have(
                  seqOr(patternMatching.patterns.map(pattern =>
                    existsSeq(pattern.binders, branchWitnessAt(pattern, pattern.binders, inputTerm, outputTerm))
                  )) |- (outputTerm === alternateOutputTerm)
                ) by LeftOr(namedBranchToGoal*)

            have(outputTerm === alternateOutputTerm) by Cut(namedCases, namedDisjunctionToGoal)
            have(thesis) by Tautology.from(lastStep)
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
          ) by Tautology.from(altLevel)
          have(thesis) by Tautology.from(lastStep)
        }
        thenHave(thesis) by Tautology
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
      ∀(inputTerm, (inputTerm ∈ argType) ==> ∀(
        outputTerm,
        ∀(
          alternateOutputTerm,
          (pair(inputTerm, outputTerm) ∈ witness /\
            pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
            (outputTerm === alternateOutputTerm)
        )
      ))
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
}
