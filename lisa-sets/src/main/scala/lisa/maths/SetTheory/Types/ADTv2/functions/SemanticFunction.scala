package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{Pattern, PatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.UniqueCharacterizedSymbol
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Pi.{->:}
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.maths.SetTheory.Types.ADTv2.support.core.`**`

class SemanticFunction[N <: Arity](
    name: String,
    adt: SemanticADT[N],
    patternMatching: PatternSystem[N],
    returnType: Expr[Ind]
)(using line: sourcecode.Line, file: sourcecode.File) {

  val patterns: Seq[Pattern[N]] = patternMatching.patterns
  val cases: Seq[Pattern[N]] = patterns

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity
  val adtDomain: SemanticADT[N] = adt
  val returnTypeExpr: Expr[Ind] = returnType

  val fullName = s"$name"
  val typ: Expr[Ind] = adt.term ->: returnType

  private val checkReturnType: Map[Pattern[N], THM] =
    patterns.map(pattern =>
      pattern -> Lemma(pattern.typingPremises |- (pattern.body :: returnType)) {
        have(thesis) by Typecheck.prove
      }
    ).toMap

  private val proofInternals = new SemanticFunctionInternals[N](
    functionName = fullName,
    adt = adt,
    patternMatching = patternMatching,
    returnType = returnType,
    checkReturnType = checkReturnType,
    typ = typ
  )

  private val untypedDefinition = proofInternals.untypedDefinition
  private val uniqueness = proofInternals.uniqueness

  private val definedClassFunction = UniqueCharacterizedSymbol(
    name = fullName,
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = f,
    definitionAt = f0 => untypedDefinition.substitute(f := f0)
  )(uniqueness)

  val id: Identifier = definedClassFunction.id
  val term: Expr[Ind] = definedClassFunction.term

  private val classFunctionCharacterization: THM = definedClassFunction.characterization

  private val shortDefinitionByPattern = patterns.map(pattern =>
    pattern -> Lemma(
      simplify(pattern.branchPremise) ==> (term * pattern.inputTerm === pattern.body)
    ) {
      have(forall(f, (term === f) <=> untypedDefinition)) by
        Restate.from(classFunctionCharacterization)
      thenHave(
        (term === term) <=> (term :: typ) /\
          (seqAnd(patterns.map { branch =>
            forallSeq(
              branch.binders,
              branch.branchPremise ==> (term * branch.inputTerm === branch.body)
            )
          }))
      ) by InstantiateForall(term)
      thenHave(forallSeq(
        pattern.binders,
        pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body)
      )) by Weakening
      pattern.binders.foldLeft(lastStep)((l, _) =>
        lastStep.statement.right.head match
          case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
          case _ => throw UnreachableException
      )
    }
  ).toMap

  def shortDefinition(pattern: Pattern[N]): THM =
    shortDefinitionByPattern(pattern)

  def elimByPattern(pattern: Pattern[N]): THM =
    shortDefinition(pattern)

  def elimByConst(constructor: SemanticConstructor[N]): THM =
    shortDefinitionByPattern(patternMatching.patternFor(constructor))

  def elim(pattern: Pattern[N]): THM =
    elimByPattern(pattern)

  def elim(constructor: SemanticConstructor[N]): THM =
    elimByConst(constructor)

  def shortDefinition(constructor: SemanticConstructor[N]): THM =
    elimByConst(constructor)

  val elimTotal: THM = Lemma(
    seqAnd(patterns.map(pattern =>
      (simplify(pattern.branchPremise) /\ (x === pattern.inputTerm)) ==> (term * x === pattern.body)
    ))
  ) {
    val subcases = patterns.map(pattern =>
      have(
        x === pattern.inputTerm |- simplify(pattern.branchPremise) ==> (term * x === pattern.body)
      ) by Congruence.from(shortDefinitionByPattern(pattern))
      thenHave(
        (simplify(pattern.branchPremise) /\ (x === pattern.inputTerm)) ==> (term * x === pattern.body)
      ) by Restate
    )
    have(thesis) by Tautology.from(subcases*)
  }

  val intro = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
    have(forall(f, (term === f) <=> untypedDefinition)) by
      Restate.from(classFunctionCharacterization)
    thenHave(
      (term === term) <=> (term :: typ) /\
        (seqAnd(patterns.map { pattern =>
          forallSeq(
            pattern.binders,
            pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body)
          )
        }))
    ) by InstantiateForall(term)
    thenHave(term :: typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
  }
}
