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

  val cases: Seq[Pattern[N]] = patternMatching.patterns

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity
  val adtDomain: SemanticADT[N] = adt
  val returnTypeExpr: Expr[Ind] = returnType

  val fullName = s"$name"
  val typ: Expr[Ind] = adt.term ->: returnType

  private val checkReturnType: Map[Pattern[N], THM] =
    cases.map(pattern =>
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

  private val shortDefinitionByPattern = cases.map(pattern =>
    pattern -> Lemma(
      simplify(pattern.branchPremise) ==> (term * pattern.inputTerm === pattern.body)
    ) {
      have(forall(f, (term === f) <=> untypedDefinition)) by
        Restate.from(classFunctionCharacterization)
      thenHave(
        (term === term) <=> (term :: typ) /\
          (seqAnd(cases.map { branch =>
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

  def shortDefinition(constructor: SemanticConstructor[N]): THM =
    shortDefinitionByPattern(patternMatching.patternFor(constructor))

  val intro = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
    have(forall(f, (term === f) <=> untypedDefinition)) by
      Restate.from(classFunctionCharacterization)
    thenHave(
      (term === term) <=> (term :: typ) /\
        (seqAnd(cases.map { pattern =>
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
