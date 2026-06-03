package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{specializeFormula, specializeTerm}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity, equivalenceApply}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.{Zero, Succ}
import lisa.maths.SetTheory.Types.ADTv2.support.Time

import lisa.maths.SetTheory.Base.{Comprehension,FoundationAxiom}
import lisa.maths.SetTheory.Base.Comprehension.{|}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.ConstructorCaseAssembly
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.CaseBodySubstitution.substitutedCaseBody
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.LambdaBodyEquality
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.utils.prooflib.BasicStepTactic.{LeftExists, Cut}
import lisa.utils.prooflib.ProofTacticLib.Arity

import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.{constructorBranchesAtHeight, constructorDisjunctionAtHeight, specializedConstructors}
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.WitnessCaseExtensionality

/**
 * Approximant stabilization.
 *
 * Proves stabilization of the approximant sequence:
 *
 *   stabilization : ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
 *
 * Exports:
 *   - [[heightFun]], [[heightFunValid]]
 *   - [[stabilization]]
 */
private[recursion] final class ApproxProp[N <: Arity](
  val spec: FunSpec[N],
  val recWitness: Witness[N],
  val approx: Approx[N]
) {

  val nVar = variable[Ind]
  val mVar = variable[Ind]
  val kVar = variable[Ind]
  import approx.G

  // ─────────────────────────────────────────────────────────────────────────
  // Height function — ε-chosen concrete height function
  // ─────────────────────────────────────────────────────────────────────────

  def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    specializeFormula(spec.adt.height.predicate(hh), spec.typeSubstitutions)

  val heightFun: Expr[Ind] =
    specializeTerm(spec.adt.height.function, spec.typeSubstitutions)

  val heightFunValid: THM = spec.adt.height.validAt(spec.typeSubstitutions)

  private val heightZero       = spec.adt.height.zeroAt(spec.typeSubstitutions)
  private val heightSuccStrong = spec.adt.height.successorStrongAt(spec.typeSubstitutions)
  private val heightMembershipMonotonic = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions)
  private val constructorsAt = specializedConstructors(spec.adt.constructors, spec.typeSubstitutions)

  // ─────────────────────────────────────────────────────────────────────────
  // Private helper — witness case instantiation
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * Instantiates a witness case equation at a concrete self-reference.
   *
   * Given `recWitness.witnessCase(pattern)`:
   *   `selfPlaceholder :: typ ⊢ ∀x̄. branchPremise(x̄) ⊢ W(self)(c(x̄)) = body[self]`
   *
   * returns the fact `W(selfTerm)(c(x̄)) = body[selfTerm]` under `patternPremise`.
   * This is function-specific (uses `recWitness` and `spec`); the generic
   * transitivity reasoning that follows belongs to [[WitnessCaseExtensionality]].
   */
  private def instantiateWitnessAtPattern(using proof: lisa.SetTheoryLibrary.Proof)(
      pattern: Pattern[N],
      selfTerm: Expr[Ind],
      selfTyped: proof.Fact,
      patternPremise: proof.Fact,
      body: Expr[Ind]
  ): proof.Fact = {
    val witnessSchema = recWitness.witnessCase(pattern).of(spec.selfPlaceholder := selfTerm)
    val witnessBase = witnessSchema.statement.right.head match
      case _ ==> consequent =>
        have(consequent) by Tautology.from(witnessSchema, selfTyped)
      case _ => throw UnreachableException

    val witnessAtVars = have(
      pattern.freshBranchPremise ==> (recWitness(selfTerm) * pattern.freshInputTerm === body)
    ) by InstantiateForallSeq(pattern.variables2)(witnessBase)

    witnessAtVars.statement.right.head match
      case _ ==> consequent =>
        have(consequent) by Tautology.from(witnessAtVars, patternPremise)
      case _ => throw UnreachableException
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma D — stabilization
  // ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
  // ─────────────────────────────────────────────────────────────────────────

  private[recursion] val stabilization: THM = Time.measure(s"AP/stabilization")(Time.measure(s"AP/stabilization ${spec.functionName}")(Lemma(
    ∀(nVar ∈ N, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(Succ(nVar)))(a)))
  ) {
    val Pred = variable[Ind >>: Prop]
    val P = λ(nVar, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(Succ(nVar)))(a)))

    val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)

    val zeroDef = have(Zero === ∅) by Restate.from(Zero.definition)
    val noElemAtEmpty = have(!in(a, app(heightFun)(∅))) by Cut(
      hValid,
      heightZero of (h := heightFun, x := a)
    )
    val noElemAtZero = have(!in(a, app(heightFun)(Zero))) by Congruence.from(noElemAtEmpty, zeroDef)

    val base = Time.measure(s"AP/stab ${spec.functionName}/base") { have(P(Zero)) subproof {
      have(a ∈ app(heightFun)(Zero) |- app(G(Zero))(a) === app(G(Succ(Zero)))(a)) by
        Tautology.from(noElemAtZero)
      thenHave(
        (a ∈ app(heightFun)(Zero)) ==> (app(G(Zero))(a) === app(G(Succ(Zero)))(a))
      ) by RightImplies
      thenHave(
        ∀(a, (a ∈ app(heightFun)(Zero)) ==> (app(G(Zero))(a) === app(G(Succ(Zero)))(a)))
      ) by RightForall
      thenHave(thesis) by Restate
    } }

    val step = have(∀(nVar, (nVar ∈ N) ==> (P(nVar) ==> P(Succ(nVar))))) subproof {
      have((nVar ∈ N) ==> (P(nVar) ==> P(Succ(nVar)))) subproof {
        val nInN = assume(nVar ∈ N)
        val ih     = assume(P(nVar))

        val succEq = have(Succ(nVar) === successor(nVar)) by
          Tautology.from(Succ.definition of (x := nVar))

        val pointwiseAtSucc = have(
          (a ∈ app(heightFun)(Succ(nVar))) ==> (app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) subproof {
          val goalAtA = app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a)
          val aInHeightSucc = assume(a ∈ app(heightFun)(Succ(nVar)))

          val aInHeightOrd = have(a ∈ app(heightFun)(successor(nVar))) by
            Congruence.from(aInHeightSucc, succEq)

          val constructorBranch =
            constructorBranchesAtHeight(constructorsAt, app(heightFun)(nVar), a)

          val constructorDisjunction =
            constructorDisjunctionAtHeight(constructorsAt, app(heightFun)(nVar), a)

          val decomposeAtA = have(constructorDisjunction) by Tautology.from(
            hValid,
            nInN,
            aInHeightOrd,
            heightSuccStrong of (h := heightFun, n := nVar, x := a),
            equivalenceApply of (
              p1 := in(a, app(heightFun)(successor(nVar))),
              p2 := constructorDisjunction
            )
          )

          val succInN = have(Succ(nVar) ∈ N) by
            Tautology.from(nInN, NatFacts.succIntro.of(n := nVar))

          val approxSuccAtN = have(nVar ∈ N ==> (G(Succ(nVar)) === recWitness(G(nVar)))) by
            InstantiateForall(nVar)(approx.approxSucc)
          val gSuccEq = have(G(Succ(nVar)) === recWitness(G(nVar))) by
            Tautology.from(nInN, approxSuccAtN)
          val gSuccAtAIsWitness = have(app(G(Succ(nVar)))(a) === app(recWitness(G(nVar)))(a)) by
            Congruence.from(gSuccEq)

          val approxSuccAtSuccN = have(
            Succ(nVar) ∈ N ==> (G(Succ(Succ(nVar))) === recWitness(G(Succ(nVar))))
          ) by InstantiateForall(Succ(nVar))(approx.approxSucc)
          val gSuccSuccEq = have(G(Succ(Succ(nVar))) === recWitness(G(Succ(nVar)))) by
            Tautology.from(succInN, approxSuccAtSuccN)
          val witnessSuccAtARev = have(
            app(recWitness(G(Succ(nVar))))(a) === app(G(Succ(Succ(nVar))))(a)
          ) by Congruence.from(gSuccSuccEq)

          val approxTypeAtN = have(nVar ∈ N ==> (G(nVar) :: spec.typ)) by
            InstantiateForall(nVar)(approx.approxHasType)
          val gNHasType = have(G(nVar) :: spec.typ) by Tautology.from(nInN, approxTypeAtN)
          val approxTypeAtSuccN = have(Succ(nVar) ∈ N ==> (G(Succ(nVar)) :: spec.typ)) by
            InstantiateForall(Succ(nVar))(approx.approxHasType)
          val gSuccHasType = have(G(Succ(nVar)) :: spec.typ) by Tautology.from(
            succInN,
            approxTypeAtSuccN
          )

          val branchEqualities = constructorsAt.map(sc =>
            val c = sc.underlying
            val constructorPatterns = spec.patternMatching.patternsFor(c)

            val directBranch = Time.measure(s"AP/stab ${spec.functionName}/ctor-${c.name}") { have(
              sc.branchPremiseAtHeight(app(heightFun)(nVar), a) |- goalAtA
            ) subproof {
              assume(sc.branchPremiseAtHeight(app(heightFun)(nVar), a))
              
              val argsTypedSemantic = have(wellTypedFormula(sc.semanticSignature2)) by
                Tautology.from(
                  hValid,
                  nInN,
                  sc.semanticTypingFromHeight(heightFun, nVar)
                )
              val aEqApplied = have(a === sc.appliedTerm2) by
                Tautology.from(
                  hValid,
                  nInN,
                  sc.appliedEqualityFromStructural(heightFun, nVar, a)
                )

              val ihAtN = have(
                ∀(a, (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Succ(nVar)))(a)))
              ) by Restate.from(ih)
              val selfArgEqualities = sc.selfRefVariables2.map(v =>
                val ihAtV = have(
                  (v ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(v) === app(G(Succ(nVar)))(v))
                ) by InstantiateForall(v)(ihAtN)
                have(app(G(nVar))(v) === app(G(Succ(nVar)))(v)) by
                  Restate.from(ihAtV)
              )

              val selectionSchema = spec.patternMatching.branchSelectionFor(c, a)
              val selectionSchemaInContext = have(selectionSchema.statement.right.head) by
                Tautology.from(selectionSchema)
              val selectionAtCtorVars = have(
                (wellTypedFormula(sc.semanticSignature2) /\ (a === sc.appliedTerm2)) |-
                  seqOr(constructorPatterns.map(pattern =>
                    pattern.freshBranchCondition /\ (a === pattern.freshInputTerm)
                  ))
              ) by InstantiateForallSeq(c.variables2)(selectionSchemaInContext)
              val selectedBranch = have(
                seqOr(constructorPatterns.map(pattern =>
                  pattern.freshBranchCondition /\ (a === pattern.freshInputTerm)
                ))
              ) by Tautology.from(selectionAtCtorVars, argsTypedSemantic, aEqApplied)

              val patternEqualities = constructorPatterns.map(pattern =>
                Time.measure(s"AP/stab ${spec.functionName}/pat-${c.name}-${pattern.branchCondition}") { have(
                  (pattern.freshBranchCondition /\ (a === pattern.freshInputTerm)) |- goalAtA
                ) subproof {
                  val selectedPattern = assume(pattern.freshBranchCondition /\ (a === pattern.freshInputTerm))
                  val aEqPattern = have(a === pattern.freshInputTerm) by Restate.from(selectedPattern)
                  val patternPremise = have(pattern.freshBranchPremise) by Tautology.from(argsTypedSemantic)

                  val bodyLeft  = substitutedCaseBody(pattern, spec.selfPlaceholder, G(nVar),        pattern.variables2)
                  val bodyRight = substitutedCaseBody(pattern, spec.selfPlaceholder, G(Succ(nVar)), pattern.variables2)
                  val bodyEq = LambdaBodyEquality.prove(bodyLeft, bodyRight, selfArgEqualities)
                  val witnessAtLeft  = instantiateWitnessAtPattern(pattern, G(nVar),        gNHasType,    patternPremise, bodyLeft)
                  val witnessAtRight = instantiateWitnessAtPattern(pattern, G(Succ(nVar)), gSuccHasType, patternPremise, bodyRight)
                  val witnessesAgreeAtA = Time.measure(s"AP/stab ${spec.functionName}/witnessExt-${c.name}-${pattern.branchCondition}") {
                    have(app(recWitness(G(nVar)))(a) === app(recWitness(G(Succ(nVar))))(a)) by Tautology.from(
                      WitnessCaseExtensionality.extensionalityAt(
                        leftWitness = recWitness(G(nVar)),
                        rightWitness = recWitness(G(Succ(nVar))),
                        ambientTerm = a,
                        inputTerm = pattern.freshInputTerm,
                        leftBody = bodyLeft,
                        rightBody = bodyRight
                      ),
                      aEqPattern, witnessAtLeft, witnessAtRight, bodyEq
                    )
                  }
                  val gSuccAtAIsWitness = have(app(G(Succ(nVar)))(a) === app(recWitness(G(nVar)))(a)) by
                    Congruence.from(gSuccEq)
                  val witnessSuccAtARev = have(
                    app(recWitness(G(Succ(nVar))))(a) === app(G(Succ(Succ(nVar))))(a)
                  ) by Congruence.from(gSuccSuccEq)

                  have(goalAtA) by Tautology.from(
                    altEqualityTransitivity of (
                      x := app(G(Succ(nVar)))(a),
                      y := app(recWitness(G(nVar)))(a),
                      z := app(G(Succ(Succ(nVar))))(a)
                    ),
                    altEqualityTransitivity of (
                      x := app(recWitness(G(nVar)))(a),
                      y := app(recWitness(G(Succ(nVar))))(a),
                      z := app(G(Succ(Succ(nVar))))(a)
                    ),
                    gSuccAtAIsWitness,
                    witnessesAgreeAtA,
                    witnessSuccAtARev
                  )
                } }
              )

              val branchesToGoal =
                if patternEqualities.size == 1 then
                  have(selectedBranch.statement.right.head |- goalAtA) by Restate.from(patternEqualities.head)
                else
                  have(selectedBranch.statement.right.head |- goalAtA) by LeftOr(patternEqualities*)

              have(goalAtA) by Cut(selectedBranch, branchesToGoal)
            } }
            ConstructorCaseAssembly.liftConstructorCase(
              sc = sc,
              heightSet = app(heightFun)(nVar),
              ambientTerm = a,
              goal = goalAtA,
              directBranch = directBranch
            )
          )

          ConstructorCaseAssembly.assemblePointwiseFromConstructors(
            constructorDisjunction = constructorDisjunction,
            decomposeFact = decomposeAtA,
            constructorFacts = branchEqualities,
            antecedent = a ∈ app(heightFun)(Succ(nVar)),
            goal = goalAtA
          )
        }
        have(
          a ∈ app(heightFun)(Succ(nVar)) ==> (app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) by Restate.from(pointwiseAtSucc)
        thenHave(
          ∀(a ∈ app(heightFun)(Succ(nVar)), app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) by RightForall
      }
      thenHave(thesis) by RightForall
    }

    have(∀(nVar, (nVar ∈ N) ==> P(nVar))) by
      Tautology.from(NatFacts.induction of (Pred := P), base, step)
    thenHave(thesis) by Restate
  }))

}
