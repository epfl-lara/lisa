package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{specializeFormula, specializeTerm}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.equivalenceApply
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Succ
import lisa.maths.SetTheory.Types.ADTv2.support.Time

import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.utils.prooflib.BasicStepTactic.{Cut, LeftOr, RightForall}
import lisa.utils.prooflib.ProofTacticLib.Arity

import lisa.maths.SetTheory.Types.ADTv2.recursion.{FunSpec, Witness}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.CaseBodySubstitution.substitutedCaseBody
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.{constructorDisjunctionAtHeight, specializedConstructors}
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.WitnessCaseExtensionality

private[recursion] final class WitnessAgreement[N <: Arity](
    val spec: FunSpec[N],
    val recWitness: Witness[N]
) {

  val leftFun  = variable[Ind]
  val rightFun = variable[Ind]
  val nVar     = variable[Ind]
  private val vVar = variable[Ind]

  private def isHeightPred(hh: Expr[Ind]): Expr[Prop] =
    specializeFormula(spec.adt.height.predicate(hh), spec.typeSubstitutions)

  private val heightFun: Expr[Ind] = specializeTerm(spec.adt.height.function, spec.typeSubstitutions)
  private val heightFunValid: THM  = spec.adt.height.validAt(spec.typeSubstitutions)
  private val heightSuccStrong     = spec.adt.height.successorStrongAt(spec.typeSubstitutions)
  private val constructorsAt       = specializedConstructors(spec.adt.constructors, spec.typeSubstitutions)

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

  private val agreeOnSlice = ∀(vVar ∈ app(heightFun)(nVar), app(leftFun)(vVar) === app(rightFun)(vVar))

  val witnessAgreementAtSucc: THM = Time.measure(s"WA/witnessAgreementAtSucc")(Lemma(
    (
      leftFun :: spec.typ,
      rightFun :: spec.typ,
      nVar ∈ N,
      agreeOnSlice
    ) |- ∀(a ∈ app(heightFun)(Succ(nVar)), app(recWitness(leftFun))(a) === app(recWitness(rightFun))(a))
  ) {
   have(thesis) subproof {
    val leftTyped  = assume(leftFun :: spec.typ)
    val rightTyped = assume(rightFun :: spec.typ)
    val nInN       = assume(nVar ∈ N)
    val agreeHyp   = assume(agreeOnSlice)

    val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)
    val succEq = have(Succ(nVar) === successor(nVar)) by
      Tautology.from(Succ.definition of (x := nVar))

    val goalW = app(recWitness(leftFun))(a) === app(recWitness(rightFun))(a)

    val pointwiseAtSucc = have((a ∈ app(heightFun)(Succ(nVar))) ==> goalW) subproof {
      val aInHeightSucc = assume(a ∈ app(heightFun)(Succ(nVar)))
      val aInHeightOrd  = have(a ∈ app(heightFun)(successor(nVar))) by
        Congruence.from(aInHeightSucc, succEq)

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

      val agreeForall = have(
        ∀(vVar, (vVar ∈ app(heightFun)(nVar)) ==> (app(leftFun)(vVar) === app(rightFun)(vVar)))
      ) by Restate.from(agreeHyp)

      val branchEqualities = constructorsAt.map { sc =>
        val c = sc.underlying
        val constructorPatterns = spec.patternMatching.patternsFor(c)
        val branchPremise = sc.branchPremiseAtHeight(app(heightFun)(nVar), a)

        val directBranch = have(
          branchPremise |- goalW
        ) subproof {
          assume(branchPremise)

          val argsTypedAtHeight = have(sc.heightTypingFormula(app(heightFun)(nVar))) by Tautology
          val argsTypedSemantic = have(wellTypedFormula(sc.semanticSignature2)) by
            Tautology.from(hValid, nInN, sc.semanticTypingFromHeight(heightFun, nVar))
          val aEqApplied = have(a === sc.appliedTerm2) by
            Tautology.from(hValid, nInN, sc.appliedEqualityFromStructural(heightFun, nVar, a))

          val selfArgEqualities = sc.selfRefVariables2.map(v =>
            val vInHeight = have(v ∈ app(heightFun)(nVar)) by Tautology.from(argsTypedAtHeight)
            RecursiveAgreement.selfAgreementFromForall(
              heightFun = heightFun,
              currentIndex = nVar,
              leftFun = leftFun,
              rightFun = rightFun,
              agreeForall = agreeForall,
              point = v,
              pointInHeight = vInHeight
            )
          )

          val selectionSchema = spec.patternMatching.branchSelectionFor(c, a)
          val selectionSchemaInContext = have(selectionSchema.statement.right.head) by
            Tautology.from(selectionSchema)
          val selectionAtCtorVars = have(
            (wellTypedFormula(sc.semanticSignature2) /\ (a === sc.appliedTerm2)) |-
              seqOr(constructorPatterns.map(pattern => pattern.branchSelectionDisjunct(a)))
          ) by InstantiateForallSeq(c.variables2)(selectionSchemaInContext)
          val selectedBranch = have(
            seqOr(constructorPatterns.map(pattern => pattern.branchSelectionDisjunct(a)))
          ) by Tautology.from(selectionAtCtorVars, argsTypedSemantic, aEqApplied)

          val patternEqualities = constructorPatterns.map(pattern =>
            val rawEq = have(
              pattern.branchSelectionBody(a) |- goalW
            ) subproof {
              val selectedPattern = assume(pattern.branchSelectionBody(a))
              val patternGuard = have(pattern.freshBranchCondition) by Tautology.from(selectedPattern)
              val aEqPattern = have(a === pattern.freshInputTerm) by Tautology.from(selectedPattern)
              val patternPremise = have(pattern.freshBranchPremise) by Tautology.from(argsTypedSemantic, selectedPattern)
              val innerAgreementContext = RecursiveAgreement.innerAgreementContext(
                heightFun = heightFun,
                hValid = hValid,
                currentIndex = nVar,
                currentIndexInN = nInN
              )
              val innerAgreements = RecursiveAgreement.innerAgreementsFor(
                pattern = pattern,
                recursiveType = spec.argType,
                heightMembershipMonotonic = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions),
                argsTypedAtHeight = argsTypedAtHeight,
                leafTyping = patternPremise,
                patternGuard = patternGuard,
                context = innerAgreementContext
              )(
                RecursiveAgreement.selfAgreementFromForallAt(
                  leftFun = leftFun,
                  rightFun = rightFun,
                  agreeForall = agreeForall
                )
              )

              val bodyLeft  = substitutedCaseBody(pattern, spec.selfPlaceholder, leftFun,  pattern.variables2)
              val bodyRight = substitutedCaseBody(pattern, spec.selfPlaceholder, rightFun, pattern.variables2)
              val bodyEq = LambdaBodyEquality.prove(bodyLeft, bodyRight, selfArgEqualities ++ innerAgreements)
              val witnessAtLeft  = instantiateWitnessAtPattern(pattern, leftFun,  leftTyped,  patternPremise, bodyLeft)
              val witnessAtRight = instantiateWitnessAtPattern(pattern, rightFun, rightTyped, patternPremise, bodyRight)

              have(goalW) by Tautology.from(
                WitnessCaseExtensionality.extensionalityAt(
                  leftWitness = recWitness(leftFun),
                  rightWitness = recWitness(rightFun),
                  ambientTerm = a,
                  inputTerm = pattern.freshInputTerm,
                  leftBody = bodyLeft,
                  rightBody = bodyRight
                ),
                aEqPattern, witnessAtLeft, witnessAtRight, bodyEq
              )
            }
            pattern.variables2.drop(pattern.arity).reverse.foldLeft(
              (pattern.branchSelectionBody(a), rawEq)
            ) { case ((body, _), v) =>
              val quantified = ∃(v, body)
              (quantified, thenHave(quantified |- goalW) by LeftExists)
            }._2
          )

          val branchesToGoal =
            if patternEqualities.size == 1 then
              have(selectedBranch.statement.right.head |- goalW) by Restate.from(patternEqualities.head)
            else
              have(selectedBranch.statement.right.head |- goalW) by LeftOr(patternEqualities*)

          have(goalW) by Cut(selectedBranch, branchesToGoal)
        }

        val liftedBranch = ConstructorCaseAssembly.liftConstructorCase(
          sc = sc,
          heightSet = app(heightFun)(nVar),
          ambientTerm = a,
          branchPremise = branchPremise,
          goal = goalW,
          directBranch = directBranch
        )
        liftedBranch
      }

      ConstructorCaseAssembly.assemblePointwiseFromConstructors(
        constructorDisjunction = constructorDisjunction,
        decomposeFact = decomposeAtA,
        constructorFacts = branchEqualities,
        antecedent = a ∈ app(heightFun)(Succ(nVar)),
        goal = goalW
      )
    }

    have(
      a ∈ app(heightFun)(Succ(nVar)) ==> (app(recWitness(leftFun))(a) === app(recWitness(rightFun))(a))
    ) by Restate.from(pointwiseAtSucc)
    thenHave(thesis) by RightForall
   }
  })

  def initialize(): Unit = {
    val _ = witnessAgreementAtSucc
  }
}
