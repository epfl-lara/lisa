package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UniqueDefinedClassFunction
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.SetTheory.Types.ADTv2.support.**

/**
 * Semantic set-theoretic interpretation of a recursive function over an ADT.
 *
 * This class is the recursive-function analogue of [[SemanticADT]] and
 * [[SemanticConstructor]]. It owns the full semantic construction:
 *
 *   1. function specification ([[FunSpec]])
 *   2. witness construction ([[Witness]])
 *   3. existence proof ([[Existence]])
 *   4. extensional uniqueness ([[Uniqueness]])
 *   5. class term, typing, and case equations
 *
 * The public [[RecFunction]] wrapper is intentionally thin and only re-exports the
 * semantic facts with user-facing theorem names.
 */
final class RecFunSemantics[N <: Arity](
    val name: String,
    val adt: SemanticADT[N],
    selfPlaceholder: Variable[Ind],
    rawCases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    val returnType: Expr[Ind]
) {

  // ─────────────────────────────────────────────────────────────────────────
  // Layer 1: specification
  // ─────────────────────────────────────────────────────────────────────────

  private val spec = FunSpec[N](
    functionName = name,
    adt = adt,
    selfPlaceholder = selfPlaceholder,
    rawCases = rawCases,
    returnType = returnType
  )

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = spec.typeVariablesSeq
  val typeArity: N = spec.typeArity
  val argType: Expr[Ind] = spec.argType
  val typ: Expr[Ind] = spec.typ

  // ─────────────────────────────────────────────────────────────────────────
  // Layer 2: witness
  // ─────────────────────────────────────────────────────────────────────────

  private val witness: Witness[N] = new Witness[N](spec)

  // ─────────────────────────────────────────────────────────────────────────
  // Layer 3: existence
  // ─────────────────────────────────────────────────────────────────────────

  private val approx = new Approx[N](spec, witness)
  private val approxProp = new ApproxProp[N](spec, witness, approx)
  val existence: Existence[N] = new Existence[N](spec, witness, approx, approxProp)

  // ─────────────────────────────────────────────────────────────────────────
  // Layer 3b: extensional uniqueness
  // ─────────────────────────────────────────────────────────────────────────

  private val functionUniquenessProof = new Uniqueness[N](spec)

  // ─────────────────────────────────────────────────────────────────────────
  // untypedDef — spec.untypedDefinition(f) with the canonical free variable f
  // ─────────────────────────────────────────────────────────────────────────

  private val untypedDef: Expr[Prop] = spec.untypedDefinition(f)

  private def definitionFormula(v: Expr[Ind]): Expr[Prop] =
    spec.untypedDefinition(v)

  // ─────────────────────────────────────────────────────────────────────────
  // uniqueness: ∃!f, Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  val uniqueness: THM = Lemma(existsOne(f, untypedDef)) {

    val existencePart = have(∃(x, definitionFormula(x))) by
      Restate.from(existence.witnessExists of (f := x))

    have(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) by
      Restate.from(functionUniquenessProof.recursivePointwisePlan)
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

  private val definedClassFunction = UniqueDefinedClassFunction(
    name = name,
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = f,
    definitionAt = definitionFormula
  )(uniqueness)

  val id: Identifier = definedClassFunction.id

  /**
   * The class-level function term specialized to concrete type arguments.
   *
   * @param args instances of the recursive function's type variables
   */
  def term(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)

  /** The class-level function term with schematic type variables. */
  val term: Expr[Ind] = definedClassFunction.term

  // ─────────────────────────────────────────────────────────────────────────
  // classDefinitionFact: Def(term)
  // ─────────────────────────────────────────────────────────────────────────

  val classDefinitionFact: THM = definedClassFunction.definitionFact

  // ─────────────────────────────────────────────────────────────────────────
  // classFunctionCharacterization: ∀f, (term = f) ↔ Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  private val classFunctionCharacterization: THM = definedClassFunction.characterization

  // ─────────────────────────────────────────────────────────────────────────
  // caseDefinitions — bodies with selfPlaceholder := term
  // ─────────────────────────────────────────────────────────────────────────

  /** Case bodies with the recursive self-reference substituted by [[term]]. */
  private val caseDefinitions: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])] =
    spec.rawCases.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (vars, body.substitute(spec.selfPlaceholder := term))
    )

  // ─────────────────────────────────────────────────────────────────────────
  // shortDefinition: ∀x̄. WT(x̄) ==> term(c(x̄)) = body_c[term]
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

  val intro: THM = Lemma(term :: spec.typ) {

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
    thenHave(thesis) by Restate
  }
}
