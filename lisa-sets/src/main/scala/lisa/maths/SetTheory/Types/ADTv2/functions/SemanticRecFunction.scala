package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Minimal semantic representation of a recursive ADT function.
 *
 * Unlike [[SemanticFunction]], this class intentionally avoids generating proof obligations
 * (intro/elim/typing theorems). It only registers a symbol and stores user-provided cases.
 */
class SemanticRecFunction[N <: Arity](
    name: String,
    adt: SemanticADT[N],
    selfPlaceholder: Variable[Ind],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    val returnType: Expr[Ind]
)(using line: sourcecode.Line, file: sourcecode.File) {

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity

  val fullName = s"$name"
  var argType: Expr[Ind] = adt.term
  val typ = argType ->: returnType

  private val classFunctionConst: Constant[Ind] = Constant[Ind](fullName)
  registerConstant(classFunctionConst)
  classFunctionConst.printAs(args => renderAppliedSymbol(fullName, typeVariablesSeq.size, args))

  val id: Identifier = classFunctionConst.id
  val term: Expr[Ind] = appSeq(classFunctionConst)(typeVariablesSeq)

  val caseDefinitions: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])] =
    cases.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (vars, body.substitute(selfPlaceholder := term))
    )

  private val untypedDefinition = (f :: typ) /\ simplify(seqAnd(cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    forallSeq(
      vars,
      wellTypedFormula(c.semanticSignature(vars)) ==> (f * c.appliedTerm(vars) === body)
    )
  )))

  /** Lemma --- Uniqueness of this function. */
  private val uniqueness = Axiom(existsOne(f, untypedDefinition))

  private val classFunctionCharacterization =
    Lemma(forall(f, (term === f) <=> untypedDefinition)) {
      have((term === f) <=> untypedDefinition) by Sorry
      thenHave(thesis) by RightForall
    }

  /** Minimal typing obligations for recursive cases (placeholder proofs). */
  private val checkReturnType: Map[SemanticConstructor[N], THM] =
    caseDefinitions.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (Lemma(wellTyped(c.semanticSignature(vars)) |- (body :: returnType)) {
        // Proof idea: same shape as non-recursive typing check, but recursive occurrences
        // require a typing hypothesis for `term` itself. This introduces circularity in
        // the current pipeline, so we keep a placeholder.
        have(thesis) by Sorry
      })
    )

  /** Case equations as lemmas (placeholder proofs). */
  val shortDefinition: Map[SemanticConstructor[N], THM] =
    caseDefinitions.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (Lemma(
        simplify(wellTypedFormula(c.semanticSignature(vars))) ==>
          (term * c.appliedTerm(vars) === body)
      ) {
        // Proof idea: unlike the non-recursive case, deriving this equation from a
        // first-order function characterization needs a recursive/fixpoint principle.
        // We keep this as a placeholder until that principle is formalized.
        have(thesis) by Sorry
      })
    )

  /** Introduction rule for the recursive symbol (placeholder proof). */
  val intro: THM = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
    // Proof idea: would follow from a recursive function-definition axiom saying the
    // symbol is in the appropriate function space and satisfies all recursive equations.

    have(forall(f, (term === f) <=> untypedDefinition)) by
      Restate.from(classFunctionCharacterization)

    thenHave(
      (term === term) <=> (term :: typ) /\
        (seqAnd(cases.map { (c, caseDef) =>
          val (vars, body) = caseDef
          forallSeq(
            vars,
            seqAnd(wellTyped(c.semanticSignature(vars))) ==>
              (term * c.appliedTerm(vars) === body)
          )
        }))
    ) by InstantiateForall(term)
    thenHave(term :: typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
  }
}
