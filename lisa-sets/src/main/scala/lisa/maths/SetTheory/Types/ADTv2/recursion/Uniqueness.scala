package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.recursion.FunSpec
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.BasicTheorems.funcBetweenEqInFuncSpace
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.Quantifiers.{existsEpsilon, existsOneEpsilonUniqueness, existsOneAlternativeDefinition}
import lisa.utils.prooflib.BasicStepTactic.RightForall

/**
 * Layer 4 — Class term, uniqueness, and public case equations.
 *
 * Given [[Existence.witnessExists]] (∃f, Def(f)) and extensional uniqueness
 * (from [[ExtensionalUniqueness]]), this layer:
 *
 *   1. Proves ∃!f, Def(f)   ([[uniqueness]])
 *   2. Defines term := ε(f, Def(f))
 *   3. Proves Def(term)      ([[classDefinitionFact]])
 *   4. Proves ∀f, (term=f) ↔ Def(f)   ([[classFunctionCharacterization]])
 *   5. Derives case equations ([[shortDefinition]]) and typing ([[intro]])
 *
 * Exported:
 *   - [[term]]            — the class-level function constant
 *   - [[uniqueness]]      — ∃!f, Def(f)
 *   - [[intro]]           — term :: A→T
 *   - [[shortDefinition]] — WT(c(x̄)) ⊢ term(c(x̄)) = body_c[term]
 *   - [[caseDefinitions]] — raw (vars, body[term]) pairs for external use
 *   - [[id]]              — the Identifier of the class constant
 */
private[recursion] final class Uniqueness[N <: Arity](
    val spec: FunSpec[N],
    existence: Existence[N]
) {

  private val typeVariablesSeq: Seq[Variable[Ind]] = spec.typeVariablesSeq

  // ─────────────────────────────────────────────────────────────────────────
  // untypedDef — spec.untypedDefinition(f) with the canonical free variable f
  // ─────────────────────────────────────────────────────────────────────────

  private val untypedDef: Expr[Prop] = spec.untypedDefinition(f)

  // private def definitionFormula(v: Variable[Ind]): Expr[Prop] =
  private def definitionFormula(v: Expr[Ind]): Expr[Prop] =
    untypedDef.substitute(f := v)

  // ─────────────────────────────────────────────────────────────────────────
  // Extensional uniqueness: Def(x) ∧ Def(y) ⟹ x = y
  // ─────────────────────────────────────────────────────────────────────────

  private val extensionalUniqueness = new ExtensionalUniqueness[N](
    adt = spec.adt,
    cases = spec.rawCases,
    returnType = spec.returnType,
    typ = spec.typ,
    untypedDefinition = untypedDef
  )

  // ─────────────────────────────────────────────────────────────────────────
  // uniqueness: ∃!f, Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  val uniqueness: THM = Lemma(existsOne(f, untypedDef)) {

    val existencePart = have(∃(x, definitionFormula(x))) by
      Restate.from(existence.witnessExists of (f := x))

    have(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) by
      Restate.from(extensionalUniqueness.recursivePointwisePlan)
    thenHave(∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y))) by RightForall
    
    val uniquenessAll = thenHave(
      ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) by RightForall

    have(
      ∃(x, definitionFormula(x)) /\
        ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) by Tautology.from(existencePart, uniquenessAll)

    have(thesis) by Tautology.from(
      lastStep,
      existsOneAlternativeDefinition of (x := f, P := λ(f, untypedDef))
    )
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Class function DEF — term := ε(f, Def(f))
  // ─────────────────────────────────────────────────────────────────────────

  private val classFunction: Constant[?] = {
    val classFunctionExpr: Expr[?] = lisa.utils.fol.FOL.Abs.apply(
      xs = typeVariablesSeq,
      t = ε(f, untypedDef)
    )
    type S
    given lisa.utils.fol.FOL.IsSort[S] =
      lisa.utils.fol.FOL.unsafeSortEvidence(classFunctionExpr.sort)
    DEF(using name = spec.functionName)(classFunctionExpr.asInstanceOf[Expr[S]])
  }
  classFunction.printAs(args => renderAppliedSymbol(spec.functionName, typeVariablesSeq.size, args))

  val id: Identifier = classFunction.id

  /** The class-level function term. */
  val term: Expr[Ind] = (classFunction #@@ typeVariablesSeq).asInstanceOf[Expr[Ind]]

  private val classTermIsEpsilon: THM = Lemma(term === ε(f, untypedDef)) {
    have(thesis) by Congruence.from(classFunction.definition)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // classDefinitionFact: Def(term)
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * Def(term) — derived from uniqueness via epsilon.
   * In the new architecture this no longer requires a sorry: ∃!f,Def(f) is
   * proved first, so epsilon transport is cycle-free.
   */
  val classDefinitionFact: THM = Lemma(definitionFormula(term)) {
    val epsilonWitness = ε(f, untypedDef)

    val classDefinitionAtEpsilon = have(definitionFormula(epsilonWitness)) by Tautology.from(
      existence.witnessExists,
      existsEpsilon of (x := f, P := λ(f, untypedDef))
    )
    val epsilonEqClassTerm =
      have(epsilonWitness === term) by Congruence.from(classTermIsEpsilon)

    val definitionAtEpsilonWithEq =
      have((epsilonWitness === term) |- definitionFormula(epsilonWitness)) by
        Weakening(classDefinitionAtEpsilon)

    val replacementVar = variable[Ind]
    val definitionAtClassTerm =
      have((epsilonWitness === term) |- definitionFormula(term)) by
        RightSubstEq.withParameters(
          List((epsilonWitness, term)),
          (Seq(replacementVar), definitionFormula(replacementVar))
        )(definitionAtEpsilonWithEq)

    have(thesis) by Tautology.from(epsilonEqClassTerm, definitionAtClassTerm)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // classFunctionCharacterization: ∀f, (term = f) ↔ Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  private val classFunctionCharacterization: THM =
    Lemma(forall(f, (term === f) <=> untypedDef)) {
      val epsilonWitness = ε(f, untypedDef)

      val epsilonCharacterization = have(
        untypedDef <=> (f === epsilonWitness)
      ) by Tautology.from(
        uniqueness,
        existsOneEpsilonUniqueness of (
          x := f,
          y := f,
          P := λ(f, untypedDef)
        )
      )

      val classTermIsEps = have(term === epsilonWitness) by
        Congruence.from(classFunction.definition)

      val toRight = have((term === f) ==> (f === epsilonWitness)) subproof {
        assume(term === f)
        val termEqF = have(term === f) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEps)
        have(f === epsilonWitness) by Congruence.from(termEqF, termEqEpsilon)
        thenHave(thesis) by Restate
      }

      val toLeft = have((f === epsilonWitness) ==> (term === f)) subproof {
        assume(f === epsilonWitness)
        val fEqEpsilon = have(f === epsilonWitness) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEps)
        have(term === f) by Congruence.from(termEqEpsilon, fEqEpsilon)
        thenHave(thesis) by Restate
      }

      val equalityRewriting = have((term === f) <=> (f === epsilonWitness)) by
        Tautology.from(toRight, toLeft)

      have((term === f) <=> untypedDef) by
        Tautology.from(equalityRewriting, epsilonCharacterization)

      thenHave(thesis) by RightForall
    }

  // ─────────────────────────────────────────────────────────────────────────
  // caseDefinitions — bodies with selfPlaceholder := term
  // ─────────────────────────────────────────────────────────────────────────

  /** Case bodies with the recursive self-reference substituted by [[term]]. */
  val caseDefinitions: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])] =
    spec.rawCases.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (vars, body.substitute(spec.selfPlaceholder := term))
    )

  // ─────────────────────────────────────────────────────────────────────────
  // shortDefinition: WT(c(x̄)) ⊢ term(c(x̄)) = body_c[term]
  // ─────────────────────────────────────────────────────────────────────────

  val shortDefinition: Map[SemanticConstructor[N], THM] =
    caseDefinitions.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (Lemma(
        simplify(
          wellTypedFormula(c.semanticSignature(vars)) ==>
            (term * c.appliedTerm(vars) === body)
        )
      ) {
        have(forall(f, (term === f) <=> untypedDef)) by
          Restate.from(classFunctionCharacterization)

        thenHave(
          (term === term) <=>
            (term :: spec.typ) /\
            (seqAnd(caseDefinitions.map { (c2, caseDef2) =>
              val (vars2, body2) = caseDef2
              forallSeq(
                vars2,
                wellTypedFormula(c2.semanticSignature(vars2)) ==>
                  (term * c2.appliedTerm(vars2) === body2)
              )
            }))
        ) by InstantiateForall(term)

        thenHave(
          forallSeq(
            vars,
            wellTypedFormula(c.semanticSignature(vars)) ==>
              (term * c.appliedTerm(vars) === body)
          )
        ) by Weakening

        vars.foldLeft(lastStep)((_, _) =>
          lastStep.statement.right.head match
            case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        thenHave(thesis) by Tautology
      })
    )

  // ─────────────────────────────────────────────────────────────────────────
  // intro: term :: A→T
  // ─────────────────────────────────────────────────────────────────────────

  val intro: THM = Lemma(forallSeq(typeVariablesSeq, term :: spec.typ)) {

    have(forall(f, (term === f) <=> untypedDef)) by
      Restate.from(classFunctionCharacterization)

    thenHave(
      (term === term) <=>
        (term :: spec.typ) /\
        (seqAnd(caseDefinitions.map { (c, caseDef) =>
          val (vars, body) = caseDef
          forallSeq(
            vars,
            seqAnd(wellTyped(c.semanticSignature(vars))) ==>
              (term * c.appliedTerm(vars) === body)
          )
        }))
    ) by InstantiateForall(term)
    thenHave(term :: spec.typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
  }
}
