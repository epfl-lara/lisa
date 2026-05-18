package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.recursion.FunSpec
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.CartesianProduct.×
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Base.{Comprehension, CartesianProduct, Pair}
import lisa.maths.SetTheory.Base.Symbols.{φ, X, Y}
import lisa.maths.SetTheory.Functions.Pi.{->:}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.maths.SetTheory.Relations.Relation.{relationBetween, R}
import lisa.maths.Quantifiers.∃!
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

/**
 * Layer 2 — Witness construction.
 *
 * Defines the witness set
 *   W(g) = { p ∈ A×T | caseMembership_g(p) }
 * where `g` = [[spec.selfPlaceholder]] stands for the recursive self-reference
 * (a free FOL variable, NOT yet instantiated to a concrete function term).
 *
 * The [[witnessClass]] DEF abstracts over [[spec.typeVariablesSeq]] and
 * [[spec.selfPlaceholder]], so that [[witness]] has [[spec.selfPlaceholder]] free
 * and can later be instantiated by [[Existence]].
 *
 * Exported:
 *   - [[witness]]                     — the set W(selfPlaceholder)
 *   - [[witnessHasType]]              — selfPlaceholder::A→T ⊢ W(selfPlaceholder)::A→T
 *   - [[witnessCaseByConstructor]]    — W(selfPlaceholder)(c(x̄)) = body_c[selfPlaceholder]
 */
private[recursion] final class Witness[N <: Arity](spec: FunSpec[N]) {

  private val typeVariablesSeq: Seq[Variable[Ind]] = spec.typeVariablesSeq
  private val selfPlaceholder: Variable[Ind] = spec.selfPlaceholder

  private val pairWitness: Variable[Ind] = variable[Ind]
  private val inputTerm: Variable[Ind] = variable[Ind]
  private val outputTerm: Variable[Ind] = variable[Ind]
  private val alternateOutputTerm: Variable[Ind] = variable[Ind]

  /** typingPremise = selfPlaceholder :: A→T (the induction hypothesis on the self-reference). */
  val typingPremise: Expr[Prop] = selfPlaceholder :: spec.typ

  // ─────────────────────────────────────────────────────────────────────────
  // caseMembership: the defining predicate of W.
  // Uses rawCases with selfPlaceholder still free.
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * caseMembership(p) ≡ ∨_c ∃x̄. WT(c(x̄)) ∧ p = (c(x̄), body_c[selfPlaceholder]).
   *
   * selfPlaceholder is free — W is parametric in the self-reference.
   */
  private val caseMembership: Expr[Ind] => Expr[Prop] = (p: Expr[Ind]) =>
    seqOr(spec.rawCases.map((c, caseDef) =>
      val (vars, body) = caseDef
      val bodyWithSelf = body.substitute(selfPlaceholder := selfPlaceholder)
      val freshVars = c.variables2
      val freshBody = bodyWithSelf
        .substitute(vars.zip(freshVars).map((from, to) => from := to)*)
        .asInstanceOf[Expr[Ind]]
      existsSeq(
        freshVars,
        wellTypedFormula(c.semanticSignature2) /\ (p === pair(c.appliedTerm2, freshBody))
      )
    ))

  // ─────────────────────────────────────────────────────────────────────────
  // Witness DEF — abstracts over typeVariablesSeq AND selfPlaceholder
  // ─────────────────────────────────────────────────────────────────────────

  private val witnessClass: Constant[?] = {
    val witnessExpr: Expr[?] = lisa.utils.fol.FOL.Abs.apply(
      xs = typeVariablesSeq :+ selfPlaceholder,
      t = { pairWitness ∈ (spec.adt.term × spec.returnType) | caseMembership(pairWitness) }
    )
    type S
    given lisa.utils.fol.FOL.IsSort[S] =
      lisa.utils.fol.FOL.unsafeSortEvidence(witnessExpr.sort)
    DEF(using name = s"${spec.functionName}/witness")(witnessExpr.asInstanceOf[Expr[S]])
  }

  /** The witness set W(selfPlaceholder) — has selfPlaceholder free. */
  val witness: Expr[Ind] =
    (witnessClass #@@ (typeVariablesSeq :+ selfPlaceholder)).asInstanceOf[Expr[Ind]]

  private val witnessBound: Expr[Ind] = spec.adt.term × spec.returnType
  private val witnessBody: Expr[Ind] =
    { pairWitness ∈ witnessBound | caseMembership(pairWitness) }

  /** Definitional equation for the witness: W(selfPlaceholder) = witnessBody. */
  val witnessDef: JUSTIFICATION = witnessClass.definition

  def apply(g: Expr[Ind]): Expr[Ind] = 
    witness.substitute(spec.selfPlaceholder := g)

  // ─────────────────────────────────────────────────────────────────────────
  // Helpers shared across the witness proofs
  // ─────────────────────────────────────────────────────────────────────────

  private def constructorTagDisequality(
      c1: SemanticConstructor[N],
      c2: SemanticConstructor[N]
  ): THM = {
    require(c1 != c2, "constructorTagDisequality requires two distinct constructors.")
    val minTag: Int = Math.min(c1.underlying.tag, c2.underlying.tag)
    val maxTag: Int = Math.max(c1.underlying.tag, c2.underlying.tag)
    lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.constructorTagDisequality(
      c1.underlying.tagTerm,
      c2.underlying.tagTerm,
      minTag,
      maxTag
    )
  }

  private val constructorTagDisequalities
      : Map[(SemanticConstructor[N], SemanticConstructor[N]), THM] =
    (for
      c1 <- spec.adt.constructors
      c2 <- spec.adt.constructors
      if c1 != c2
    yield (c1, c2) -> constructorTagDisequality(c1, c2)).toMap

  private def constructorApplicationTyping(
      c: SemanticConstructor[N],
      args: Seq[Variable[Ind]]
  ): THM = Lemma(
    wellTypedFormula(c.semanticSignature(args)) |- (c.appliedTerm(args) :: spec.adt.term)
  ) {
    have(c.term(typeVariablesSeq) :: c.typ) by Restate.from(c.intro)
    val introAtTypeVars = lastStep
    val argsWellTyped = assume(wellTypedFormula(c.semanticSignature(args)))
    val finalTyping = args.foldLeft(
      (introAtTypeVars, c.term(typeVariablesSeq): Expr[Ind], c.typ: Expr[Ind])
    ) { case ((accFact, accTerm, accType), argument) =>
      accType match
        case domainTy ->: codomainTy =>
          val argumentTyping = have(
            wellTypedFormula(c.semanticSignature(args)) |- argument :: domainTy
          ) by Tautology.from(argsWellTyped)
          val nextTyping = have(
            wellTypedFormula(c.semanticSignature(args)) |- (accTerm * argument) :: codomainTy
          ) by Tautology.from(
            accFact,
            funEqDef of (f := accTerm, a := domainTy, b := codomainTy, x := argument),
            argumentTyping
          )
          (nextTyping, accTerm * argument, codomainTy)
        case _ => throw UnreachableException
    }._1
    have(thesis) by Restate.from(finalTyping)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // checkReturnType: body_c[selfPlaceholder] :: returnType
  // ─────────────────────────────────────────────────────────────────────────

  private val checkReturnType: Map[SemanticConstructor[N], JUSTIFICATION] =
    spec.rawCases.map((c, caseDef) =>
      val (vars, body) = caseDef
      val bodyWithSelf = body.substitute(selfPlaceholder := selfPlaceholder)
      val witnessAssumptions =
        wellTypedSet(c.semanticSignature(vars)) + typingPremise

      c -> (Lemma(witnessAssumptions |- (bodyWithSelf :: spec.returnType)) {
        have(thesis) by Typecheck.prove
      })
    )

  // ─────────────────────────────────────────────────────────────────────────
  // witnessMembershipByConstructor
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * typingPremise ⊢ ∀x̄. WT(c(x̄)) ⟹ (c(x̄), body_c[selfPlaceholder]) ∈ W
   */
  private val witnessMembershipByConstructor: Map[SemanticConstructor[N], THM] =
    (for c <- spec.rawCases.keys yield
      val (vars, rawBody) = spec.rawCases(c)
      val body = rawBody.substitute(selfPlaceholder := selfPlaceholder)
      c -> Lemma(
        typingPremise ==> forallSeq(
          vars,
          wellTypedFormula(c.semanticSignature(vars)) ==>
            pair(c.appliedTerm(vars), body) ∈ witness
        )
      ) {
        assume(typingPremise)

        val wellTypedArgs = wellTypedFormula(c.semanticSignature(vars))
        val wellTypedPremises = wellTypedSet(c.semanticSignature(vars))
        val wellTypedHyp = have(wellTypedArgs |- wellTypedArgs) by Hypothesis
        val pairTerm = pair(c.appliedTerm(vars), body)

        val inputTyping = have(wellTypedArgs |- c.appliedTerm(vars) :: spec.adt.term) by
          Tautology.from(constructorApplicationTyping(c, vars))

        def proveTypingPremise(premise: Expr[Prop]) =
          if premise == wellTypedArgs then
            have(wellTypedArgs |- premise) by Restate.from(wellTypedHyp)
          else if wellTypedPremises.contains(premise) then
            have(wellTypedArgs |- premise) by Tautology.from(wellTypedHyp)
          else if premise == typingPremise then
            have(wellTypedArgs |- premise) by Tautology
          else
            throw IllegalArgumentException(
              s"Unsupported typing premise in witnessMembershipByConstructor for ${c.name}: $premise"
            )

        val outputTypingPremises =
          checkReturnType(c).statement.left.toSeq.map(_.asInstanceOf[Expr[Prop]])
        val outputTypingFacts = outputTypingPremises.map(proveTypingPremise)
        val outputTyping = have(wellTypedArgs |- body :: spec.returnType) by Tautology.from(
          (checkReturnType(c) +: outputTypingFacts)*
        )

        val pairInBound = have(wellTypedArgs |- pairTerm ∈ witnessBound) by Tautology.from(
          CartesianProduct.pairMembership of (
            A := spec.adt.term,
            B := spec.returnType,
            x := c.appliedTerm(vars),
            y := body
          ),
          inputTyping,
          outputTyping
        )

        val ownBranchBody = body
          .substitute(vars.zip(c.variables2).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]
        val baseCaseBody =
          wellTypedFormula(c.semanticSignature2) /\ (pairTerm === pair(c.appliedTerm2, ownBranchBody))
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

        val inOwnCaseBranchRaw =
          c.variables2.indices.reverse.foldLeft(ownBranchAtCurrentVars)((fact, idx) =>
            val quantifiedVar = c.variables2(idx)
            val witnessVar = vars(idx)
            val priorSubst =
              c.variables2.take(idx).zip(vars.take(idx)).map((from, to) => from := to)
            val phi = existsSeq(
              c.variables2.drop(idx + 1),
              baseCaseBody.substitute(priorSubst*).asInstanceOf[Expr[Prop]]
            )
            have(wellTypedArgs |- ∃(quantifiedVar, phi)) by
              RightExists.withParameters(phi, quantifiedVar, witnessVar)(fact)
          )

        val inOwnCaseBranch = have(wellTypedArgs |- ownCaseBranch) by Tautology.from(inOwnCaseBranchRaw)
        val rawCaseMembership = have(wellTypedArgs |- caseMembership(pairTerm)) by
          Tautology.from(inOwnCaseBranch)

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
        thenHave(
          forallSeq(
            vars,
            wellTypedFormula(c.semanticSignature(vars)) ==>
              pair(c.appliedTerm(vars), body) ∈ witness
          )
        ) by QuantifiersIntro(vars)
        thenHave(thesis) by Tautology
      }
    ).toMap

  // ─────────────────────────────────────────────────────────────────────────
  // Relation / totality / single-valued — basis of witnessHasType
  // ─────────────────────────────────────────────────────────────────────────

  private val witnessRelationBetween: THM =
    Lemma(relationBetween(witness)(spec.adt.term)(spec.returnType)) {
      have(witnessBody ⊆ witnessBound) by Tautology.from(
        Comprehension.subset of (
          y := witnessBound,
          φ := λ(pairWitness, caseMembership(pairWitness))
        )
      )
      val subsetBound = have(witness ⊆ witnessBound) by Congruence.from(lastStep, witnessDef)
      have(
        relationBetween(witness)(spec.adt.term)(spec.returnType)
      ) by Tautology.from(
        subsetBound,
        relationBetween.definition of (
          R := witness,
          X := spec.adt.term,
          Y := spec.returnType
        )
      )
      have(thesis) by Restate.from(lastStep)
    }

  private val witnessTotality: THM = Lemma(
    typingPremise ==> ∀(inputTerm ∈ spec.adt.term, 
      ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
    )
  ) {
    assume(typingPremise)

    val totalityAtInput = ∃(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
    val constructorBranch = spec.adt.constructors.map(c =>
      c -> simplify(
        existsSeq(
          c.variables2,
          wellTypedFormula(c.semanticSignature2) /\ (inputTerm === c.appliedTerm2)
        )
      )
    ).toMap
    val constructorDisjunction =
      simplify(seqOr(spec.adt.constructors.map(c => constructorBranch(c))))

    have(spec.adt.elim.statement.right.head) by Tautology.from(spec.adt.elim)
    thenHave(inputTerm ∈ spec.adt.term ==> constructorDisjunction) by
      InstantiateForall(inputTerm)
    val decompositionAtInput = thenHave(inputTerm ∈ spec.adt.term |- constructorDisjunction) by
      Restate

    val branchToWitness = spec.adt.constructors.map(c =>
      val (caseVars, rawCaseBody) = spec.rawCases(c)
      val caseBody = rawCaseBody.substitute(selfPlaceholder := selfPlaceholder)

      val directBranch = have(
        wellTypedFormula(c.semanticSignature2) /\ (inputTerm === c.appliedTerm2) |- totalityAtInput
      ) subproof {
        assume(wellTypedFormula(c.semanticSignature2) /\ (inputTerm === c.appliedTerm2))
        val argsTyped = have(wellTypedFormula(c.semanticSignature2)) by Tautology
        val inputEqCtor = have(inputTerm === c.appliedTerm2) by Tautology

        have(
          forallSeq(
            caseVars,
            wellTypedFormula(c.semanticSignature(caseVars)) ==>
              pair(c.appliedTerm(caseVars), caseBody) ∈ witness
          )
        ) by Tautology.from(witnessMembershipByConstructor(c))

        val instantiatedMembership =
          caseVars.zip(c.variables2).foldLeft(lastStep)((fact, varsPair) =>
            fact.statement.right.head match
              case forall(v, phi) =>
                thenHave(phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]) by
                  InstantiateForall(varsPair._2)
              case _ => throw UnreachableException
          )

        val pairInWitnessAtCtor = instantiatedMembership.statement.right.head match
          case _ ==> consequent =>
            have(consequent) by Tautology.from(instantiatedMembership, argsTyped)
          case _ => throw UnreachableException

        val existsAtCtorInput =
          have(∃(outputTerm, pair(c.appliedTerm2, outputTerm) ∈ witness)) by
            RightExists(pairInWitnessAtCtor)

        val transferAtWitness = have(
          (inputTerm === c.appliedTerm2, pair(c.appliedTerm2, outputTerm) ∈ witness) |- totalityAtInput
        ) subproof {
          assume(inputTerm === c.appliedTerm2)
          val eqInput = have(inputTerm === c.appliedTerm2) by Hypothesis
          assume(pair(c.appliedTerm2, outputTerm) ∈ witness)
          val pairAtCtorInput = have(pair(c.appliedTerm2, outputTerm) ∈ witness) by Hypothesis
          val pairAtInput =
            have(pair(inputTerm, outputTerm) ∈ witness) by Congruence.from(pairAtCtorInput, eqInput)
          have(totalityAtInput) by RightExists(pairAtInput)
        }

        val transferExistential = have(
          (
            inputTerm === c.appliedTerm2,
            ∃(outputTerm, pair(c.appliedTerm2, outputTerm) ∈ witness)
          ) |- totalityAtInput
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

    have(inputTerm ∈ spec.adt.term |- totalityAtInput) by Cut(decompositionAtInput, totalityFromCases)
    thenHave((inputTerm ∈ spec.adt.term) ==> totalityAtInput) by RightImplies
    thenHave(
      ∀(inputTerm, (inputTerm ∈ spec.adt.term) ==> totalityAtInput)
    ) by RightForall
    thenHave(
      typingPremise ==>
        ∀(inputTerm, (inputTerm ∈ spec.adt.term) ==> totalityAtInput)
    ) by Tautology
    thenHave(thesis) by Restate
  }

  private val witnessSingleValued: THM = Lemma(
    ∀(inputTerm ∈ spec.adt.term, 
      ∀(outputTerm,
        ∀(alternateOutputTerm,
          (pair(inputTerm, outputTerm) ∈ witness /\
            pair(inputTerm, alternateOutputTerm) ∈ witness) ==>
            (outputTerm === alternateOutputTerm)
        )
      )
    )
  ) {
    val pairAtOutput = pair(inputTerm, outputTerm)
    val pairAtAlternateOutput = pair(inputTerm, alternateOutputTerm)

    def caseBranchAtOutputWithVars1(c: SemanticConstructor[N]): Expr[Prop] = {
      val (caseVars, rawCaseBody) = spec.rawCases(c)
      val caseBody = rawCaseBody.substitute(selfPlaceholder := selfPlaceholder)
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
      val (caseVars, rawCaseBody) = spec.rawCases(c)
      val caseBody = rawCaseBody.substitute(selfPlaceholder := selfPlaceholder)
      val bodyAtVars2 = caseBody
        .substitute(caseVars.zip(c.variables2).map((from, to) => from := to)*)
        .asInstanceOf[Expr[Ind]]
      existsSeq(
        c.variables2,
        wellTypedFormula(c.semanticSignature2) /\
          (pairAtAlternateOutput === pair(c.appliedTerm2, bodyAtVars2))
      )
    }

    val caseDisjunctionAtOutputWithVars1 =
      seqOr(spec.adt.constructors.map(c => caseBranchAtOutputWithVars1(c)))
    val caseDisjunctionAtAlternateOutput =
      seqOr(spec.adt.constructors.map(c => caseBranchAtAlternateOutput(c)))

    val outputCaseRenaming =
      have(caseMembership(pairAtOutput) |- caseDisjunctionAtOutputWithVars1) by Tableau

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
      (
        inputTerm ∈ spec.adt.term,
        pairAtOutput ∈ witness,
        pairAtAlternateOutput ∈ witness
      ) |- (outputTerm === alternateOutputTerm)
    ) subproof {
      assume(inputTerm ∈ spec.adt.term)
      val inputInAdt = have(inputTerm ∈ spec.adt.term) by Hypothesis
      assume(pairAtOutput ∈ witness)
      val pairOutputInWitness = have(pairAtOutput ∈ witness) by Hypothesis
      assume(pairAtAlternateOutput ∈ witness)
      val pairAlternateInWitness = have(pairAtAlternateOutput ∈ witness) by Hypothesis

      val outputCaseRaw = have(caseMembership(pairAtOutput)) by
        Tautology.from(pairOutputInWitness, outputMembershipEq)
      val outputCase = have(caseDisjunctionAtOutputWithVars1) by
        Tautology.from(outputCaseRaw, outputCaseRenaming)
      val alternateCaseRaw = have(caseMembership(pairAtAlternateOutput)) by
        Tautology.from(pairAlternateInWitness, alternateMembershipEq)
      val alternateCase = have(caseDisjunctionAtAlternateOutput) by Restate.from(alternateCaseRaw)

      val branchByOutputConstructor = spec.adt.constructors.map(c1 =>
        val (caseVars1, rawCaseBody1) = spec.rawCases(c1)
        val caseBody1 = rawCaseBody1.substitute(selfPlaceholder := selfPlaceholder)
        val bodyAtVars1 = caseBody1
          .substitute(caseVars1.zip(c1.variables1).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]
        val branchAtOutputWithVars1 =
          wellTypedFormula(c1.semanticSignature1) /\
            (pairAtOutput === pair(c1.appliedTerm1, bodyAtVars1))

        val branchByAlternateConstructor = spec.adt.constructors.map(c2 =>
          val (caseVars2, rawCaseBody2) = spec.rawCases(c2)
          val caseBody2 = rawCaseBody2.substitute(selfPlaceholder := selfPlaceholder)
          val bodyAtVars2 = caseBody2
            .substitute(caseVars2.zip(c2.variables2).map((from, to) => from := to)*)
            .asInstanceOf[Expr[Ind]]
          val branchAtAlternate =
            wellTypedFormula(c2.semanticSignature2) /\
              (pairAtAlternateOutput === pair(c2.appliedTerm2, bodyAtVars2))

          val directCase = have(
            (
              branchAtOutputWithVars1,
              branchAtAlternate,
              inputTerm ∈ spec.adt.term
            ) |- (outputTerm === alternateOutputTerm)
          ) subproof {
            assume(branchAtOutputWithVars1)
            val branchOutputTyped = have(wellTypedFormula(c1.semanticSignature1)) by Tautology
            val branchOutputPairEq =
              have(pairAtOutput === pair(c1.appliedTerm1, bodyAtVars1)) by Tautology
            assume(branchAtAlternate)
            val branchAlternateTyped = have(wellTypedFormula(c2.semanticSignature2)) by Tautology
            val branchAlternatePairEq =
              have(pairAtAlternateOutput === pair(c2.appliedTerm2, bodyAtVars2)) by Tautology
            assume(inputTerm ∈ spec.adt.term)

            val outputPairDecomposition = have(
              pairAtOutput === pair(c1.appliedTerm1, bodyAtVars1) |-
                (inputTerm === c1.appliedTerm1) /\ (outputTerm === bodyAtVars1)
            ) by Tautology.from(
              Pair.extensionality of (
                a := inputTerm,
                b := outputTerm,
                c := c1.appliedTerm1,
                d := bodyAtVars1
              )
            )
            val outputComponents =
              have((inputTerm === c1.appliedTerm1) /\ (outputTerm === bodyAtVars1)) by
                Tautology.from(branchOutputPairEq, outputPairDecomposition)
            val inputEqFromOutput = have(inputTerm === c1.appliedTerm1) by
              Tautology.from(outputComponents)
            val outputEqToBody = have(outputTerm === bodyAtVars1) by Tautology.from(outputComponents)

            val alternatePairDecomposition = have(
              pairAtAlternateOutput === pair(c2.appliedTerm2, bodyAtVars2) |-
                (inputTerm === c2.appliedTerm2) /\ (alternateOutputTerm === bodyAtVars2)
            ) by Tautology.from(
              Pair.extensionality of (
                a := inputTerm,
                b := alternateOutputTerm,
                c := c2.appliedTerm2,
                d := bodyAtVars2
              )
            )
            val alternateComponents =
              have((inputTerm === c2.appliedTerm2) /\ (alternateOutputTerm === bodyAtVars2)) by
                Tautology.from(branchAlternatePairEq, alternatePairDecomposition)
            val inputEqFromAlternate = have(inputTerm === c2.appliedTerm2) by
              Tautology.from(alternateComponents)
            val alternateEqToBody = have(alternateOutputTerm === bodyAtVars2) by
              Tautology.from(alternateComponents)

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
                if c1.arity == 0 then have(bodyAtVars1 === bodyAtVars2) by RightRefl
                else
                  val injectivityBase =
                    have(c1.injectivity.statement.right.head) by Tautology.from(c1.injectivity)
                  val injectivityAtVars =
                    (c1.variables1 ++ c1.variables2).foldLeft(injectivityBase)((_, v) =>
                      lastStep.statement.right.head match
                        case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
                        case _ => throw UnreachableException
                    )
                  val argsEqEquivalence = have(
                    simplify((c1.appliedTerm1 === c1.appliedTerm2) <=> (c1.variables1 === c1.variables2))
                  ) by Tautology.from(
                    injectivityAtVars,
                    branchOutputTyped,
                    branchAlternateTyped
                  )
                  val argsEqConjunction = have(c1.variables1 === c1.variables2) by Tautology.from(
                    argsEqEquivalence,
                    c1EqC2
                  )
                  val argumentEqualities = c1.variables1.zip(c1.variables2).map((u, v) =>
                    have(u === v) by Tautology.from(argsEqConjunction)
                  )
                  val bodyTemplateVars = caseVars1.map(_ => variable[Ind])
                  val bodyAtTemplateVars = caseBody1
                    .substitute(caseVars1.zip(bodyTemplateVars).map((from, to) => from := to)*)
                    .asInstanceOf[Expr[Ind]]
                  val bodyRefl = have(bodyAtVars1 === bodyAtVars1) by
                    RightRefl.withParameters(bodyAtVars1 === bodyAtVars1)
                  val bodyEqWithEqualities = have(
                    (bodyRefl.bot.left ++ argumentEqualities.map(_.statement.right.head)) |- (bodyAtVars1 === bodyAtVars2)
                  ) by RightSubstEq.withParameters(
                    c1.variables1.zip(c1.variables2).toList,
                    (bodyTemplateVars, bodyAtVars1 === bodyAtTemplateVars)
                  )(bodyRefl)
                  argumentEqualities.foreach { equalityFact =>
                    have(
                      if equalityFact.bot.left.contains(equalityFact.statement.right.head) then lastStep.bot
                      else lastStep.bot -<< equalityFact.statement.right.head
                    ) by Cut(equalityFact, lastStep)
                  }
                  have(bodyAtVars1 === bodyAtVars2) by Restate.from(lastStep)

              val body2EqAlternate = have(bodyAtVars2 === alternateOutputTerm) by
                Congruence.from(alternateEqToBody)
              have(outputTerm === alternateOutputTerm) by Tautology.from(
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
              have(thesis) by Restate.from(lastStep)
            else
              val c1ShortBase =
                have(c1.shortDefinition.statement.right.head) by Tautology.from(c1.shortDefinition)
              val c1ShortAtVars1 = c1.variables1.foldLeft(c1ShortBase)((_, v1) =>
                lastStep.statement.right.head match
                  case forall(v, phi) =>
                    thenHave(phi.substituteUnsafe(Map(v -> v1)).asInstanceOf[Expr[Prop]]) by
                      InstantiateForall(v1)
                  case _ => throw UnreachableException
              )
              val c1StructuralEq = c1ShortAtVars1.statement.right.head match
                case _ ==> consequent =>
                  have(consequent) by Tautology.from(c1ShortAtVars1, branchOutputTyped)
                case _ => throw UnreachableException

              val c2ShortBase =
                have(c2.shortDefinition.statement.right.head) by Tautology.from(c2.shortDefinition)
              val c2ShortAtVars2 = c2.variables2.foldLeft(c2ShortBase)((_, v2) =>
                lastStep.statement.right.head match
                  case forall(v, phi) =>
                    thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by
                      InstantiateForall(v2)
                  case _ => throw UnreachableException
              )
              val c2StructuralEq = c2ShortAtVars2.statement.right.head match
                case _ ==> consequent =>
                  have(consequent) by Tautology.from(c2ShortAtVars2, branchAlternateTyped)
                case _ => throw UnreachableException

              val c1StructuralToApplied = have(c1.structuralTerm1 === c1.appliedTerm1) by
                Congruence.from(c1StructuralEq)
              val c1StructuralEqC2Applied = have(c1.structuralTerm1 === c2.appliedTerm2) by
                Tautology.from(
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

          val liftedAcrossAlternate =
            c2.variables2.reverse.foldLeft((directCase, branchAtAlternate))((acc, v) =>
              val (fact, phi) = acc
              val nextPhi = ∃(v, phi)
              val nextFact = have(
                (branchAtOutputWithVars1, nextPhi, inputTerm ∈ spec.adt.term) |-
                  (outputTerm === alternateOutputTerm)
              ) by LeftExists.withParameters(phi, v)(fact)
              (nextFact, nextPhi)
            )._1
          have(
            (
              branchAtOutputWithVars1,
              caseBranchAtAlternateOutput(c2),
              inputTerm ∈ spec.adt.term
            ) |- (outputTerm === alternateOutputTerm)
          ) by Restate.from(liftedAcrossAlternate)
        )

        val fromAlternateDisjunction =
          if branchByAlternateConstructor.size == 1 then
            have(
              (
                branchAtOutputWithVars1,
                caseDisjunctionAtAlternateOutput,
                inputTerm ∈ spec.adt.term
              ) |- (outputTerm === alternateOutputTerm)
            ) by Restate.from(branchByAlternateConstructor.head)
          else
            have(
              (
                branchAtOutputWithVars1,
                caseDisjunctionAtAlternateOutput,
                inputTerm ∈ spec.adt.term
              ) |- (outputTerm === alternateOutputTerm)
            ) by LeftOr(branchByAlternateConstructor*)

        val liftedAcrossOutput =
          c1.variables1.reverse.foldLeft((fromAlternateDisjunction, branchAtOutputWithVars1))((acc, v) =>
            val (fact, phi) = acc
            val nextPhi = ∃(v, phi)
            val nextFact = have(
              (nextPhi, caseDisjunctionAtAlternateOutput, inputTerm ∈ spec.adt.term) |-
                (outputTerm === alternateOutputTerm)
            ) by LeftExists.withParameters(phi, v)(fact)
            (nextFact, nextPhi)
          )._1
        have(
          (
            caseBranchAtOutputWithVars1(c1),
            caseDisjunctionAtAlternateOutput,
            inputTerm ∈ spec.adt.term
          ) |- (outputTerm === alternateOutputTerm)
        ) by Restate.from(liftedAcrossOutput)
      )

      val fromBothDisjunctions =
        if branchByOutputConstructor.size == 1 then
          have(
            (
              caseDisjunctionAtOutputWithVars1,
              caseDisjunctionAtAlternateOutput,
              inputTerm ∈ spec.adt.term
            ) |- (outputTerm === alternateOutputTerm)
          ) by Restate.from(branchByOutputConstructor.head)
        else
          have(
            (
              caseDisjunctionAtOutputWithVars1,
              caseDisjunctionAtAlternateOutput,
              inputTerm ∈ spec.adt.term
            ) |- (outputTerm === alternateOutputTerm)
          ) by LeftOr(branchByOutputConstructor*)

      have(outputTerm === alternateOutputTerm) by Tautology.from(
        outputCase,
        alternateCase,
        inputInAdt,
        fromBothDisjunctions
      )
    }

    val pairMembershipConjunction =
      pairAtOutput ∈ witness /\ pairAtAlternateOutput ∈ witness
    have(
      (inputTerm ∈ spec.adt.term) |- pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
    ) by Tautology.from(singleValuedAtInput)
    thenHave(
      (inputTerm ∈ spec.adt.term) |- ∀(
        alternateOutputTerm,
        pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
      )
    ) by RightForall
    thenHave(
      (inputTerm ∈ spec.adt.term) |- ∀(
        outputTerm,
        ∀(
          alternateOutputTerm,
          pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
        )
      )
    ) by RightForall
    thenHave(
      (inputTerm ∈ spec.adt.term) ==> ∀(
        outputTerm,
        ∀(
          alternateOutputTerm,
          pairMembershipConjunction ==> (outputTerm === alternateOutputTerm)
        )
      )
    ) by RightImplies
    thenHave(
      ∀(
        inputTerm,
        (inputTerm ∈ spec.adt.term) ==> ∀(
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
    typingPremise ==> ∀(inputTerm ∈ spec.adt.term,
      existsOne(outputTerm, pair(inputTerm, outputTerm) ∈ witness)
    )
  ) {
    assume(typingPremise)
    val pointwisePredicate = (out: Expr[Ind]) => pair(inputTerm, out) ∈ witness
    have(
      ∀(inputTerm, (inputTerm ∈ spec.adt.term) ==> ∃(outputTerm, pointwisePredicate(outputTerm)))
    ) by Tautology.from(witnessTotality)
    val totalityAtInput =
      thenHave((inputTerm ∈ spec.adt.term) ==> ∃(outputTerm, pointwisePredicate(outputTerm))) by
        InstantiateForall(inputTerm)
    val singleValuedAtInput = have(
      (inputTerm ∈ spec.adt.term) ==> ∀(
        outputTerm,
        ∀(
          alternateOutputTerm,
          (pointwisePredicate(outputTerm) /\ pointwisePredicate(alternateOutputTerm)) ==>
            (outputTerm === alternateOutputTerm)
        )
      )
    ) by InstantiateForall(inputTerm)(witnessSingleValued)

    val pointwiseUnique = have(
      (inputTerm ∈ spec.adt.term) |- existsOne(outputTerm, pointwisePredicate(outputTerm))
    ) subproof {
      assume(inputTerm ∈ spec.adt.term)
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

    have((inputTerm ∈ spec.adt.term) ==> existsOne(outputTerm, pointwisePredicate(outputTerm))) by
      Restate.from(pointwiseUnique)
    thenHave(
      ∀(inputTerm, (inputTerm ∈ spec.adt.term) ==> existsOne(outputTerm, pointwisePredicate(outputTerm)))
    ) by RightForall
    thenHave(
      typingPremise ==>
        ∀(inputTerm, (inputTerm ∈ spec.adt.term) ==> existsOne(outputTerm, pointwisePredicate(outputTerm)))
    ) by Tautology
    thenHave(thesis) by Restate
  }

  /** selfPlaceholder :: A→T ⊢ W(selfPlaceholder) :: A→T */
  val witnessHasType: THM = Lemma(typingPremise ==> (witness :: spec.typ)) {
    assume(typingPremise)
    have(
      ∀(inputTerm ∈ spec.adt.term, existsOne(outputTerm, pair(inputTerm, outputTerm) ∈ witness))
    ) by Tautology.from(witnessUniqueValue)
    val witnessFunctionBetween = have(
      Function.functionBetween(witness)(spec.adt.term)(spec.returnType)
    ) by Tautology.from(
      Function.functionBetween.definition of (
        f := witness,
        A := spec.adt.term,
        B := spec.returnType
      ),
      witnessRelationBetween,
      lastStep
    )
    have(witness :: spec.typ) by Tautology.from(
      BasicTheorems.funcBetweenEqInFuncSpace of (
        f := witness,
        A := spec.adt.term,
        B := spec.returnType
      ),
      witnessFunctionBetween
    )
    thenHave(thesis) by Tautology
  }

  // ─────────────────────────────────────────────────────────────────────────
  // witnessCaseByConstructor
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * selfPlaceholder :: A→T ⊢ W(selfPlaceholder)(c(x̄)) = body_c[selfPlaceholder]
   */
  val witnessCaseByConstructor: Map[SemanticConstructor[N], THM] =
    (for c <- spec.rawCases.keys yield
      val (vars, rawBody) = spec.rawCases(c)
      val body = rawBody.substitute(selfPlaceholder := selfPlaceholder)
      c -> Lemma(
        typingPremise ==> forallSeq(
          vars,
          wellTypedFormula(c.semanticSignature(vars)) ==> (witness * c.appliedTerm(vars) === body)
        )
      ) {
        assume(typingPremise)
        val wellTypedArgs = wellTypedFormula(c.semanticSignature(vars))
        val pairTerm = pair(c.appliedTerm(vars), body)

        have(forallSeq(vars, wellTypedArgs ==> pairTerm ∈ witness)) by
          Restate.from(witnessMembershipByConstructor(c))
        vars.foldLeft(lastStep)((fact, v) =>
          fact.statement.right.head match
            case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        val pairInWitness = thenHave(wellTypedArgs |- pairTerm ∈ witness) by Restate

        val witnessBetween =
          have(Function.functionBetween(witness)(spec.adt.term)(spec.returnType)) by
            Tautology.from(
              BasicTheorems.funcBetweenEqInFuncSpace of (
                f := witness,
                A := spec.adt.term,
                B := spec.returnType
              ),
              witnessHasType
            )
        val witnessIsFunction = have(Function.function(witness)) by Tautology.from(
          BasicTheorems.functionBetweenIsFunction of (
            f := witness,
            A := spec.adt.term,
            B := spec.returnType
          ),
          witnessBetween
        )
        val witnessDomain = have(Function.dom(witness) === spec.adt.term) by Tautology.from(
          BasicTheorems.functionBetweenDomain of (
            f := witness,
            A := spec.adt.term,
            B := spec.returnType
          ),
          witnessBetween
        )

        val inputTyping = have(wellTypedArgs |- c.appliedTerm(vars) :: spec.adt.term) by
          Tautology.from(constructorApplicationTyping(c, vars))
        val inputInDomain = have(wellTypedArgs |- c.appliedTerm(vars) ∈ Function.dom(witness)) by
          Congruence.from(inputTyping, witnessDomain)

        val appEq = have(
          wellTypedArgs |- (witness * c.appliedTerm(vars) === body) <=> (pairTerm ∈ witness)
        ) by Tautology.from(
          BasicTheorems.appDefinition of (
            f := witness,
            x := c.appliedTerm(vars),
            y := body
          ),
          witnessIsFunction,
          inputInDomain
        )

        have(wellTypedArgs |- (witness * c.appliedTerm(vars) === body)) by
          Tautology.from(appEq, pairInWitness)
        thenHave(wellTypedArgs ==> (witness * c.appliedTerm(vars) === body)) by RightImplies
        thenHave(
          forallSeq(
            vars,
            wellTypedFormula(c.semanticSignature(vars)) ==> (witness * c.appliedTerm(vars) === body)
          )
        ) by QuantifiersIntro(vars)
        thenHave(thesis) by Tautology
      }
    ).toMap
}
