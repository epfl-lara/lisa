package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.core.**
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.UniqueCharacterizedSymbol
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

class SemanticFunction[N <: Arity](
    val name: String,
    val adt: SemanticADT[N],
    val argType: Expr[Ind],
    patternMatching: PatternSystem[N],
    val returnType: Expr[Ind]
)(using line: sourcecode.Line, file: sourcecode.File) {

  

  private val checkReturnType: Map[Pattern[N], THM] =
    patterns.map(pattern =>
      pattern -> Lemma(pattern.typingPremises |- (pattern.body :: returnType)) {
        have(thesis) by Typecheck.prove
      }
    ).toMap

  private val proofInternals = new SemanticFunctionInternals[N](
    functionName = name,
    adt = adt,
    argType = argType,
    patternMatching = patternMatching,
    checkReturnType = checkReturnType,
    returnType = returnType
  )

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity
  val adtDomain: SemanticADT[N] = adt
  val typ: Expr[Ind] = proofInternals.typ

  private val untypedDef: Expr[Prop] =
    proofInternals.untypedDefinition

  private def definitionFormula(f0: Expr[Ind]): Expr[Prop] =
    untypedDef.substitute(f := f0)

  private val uniqueness: THM =
    proofInternals.uniqueness

  private val definedClassFunction = UniqueCharacterizedSymbol(
    name = name,
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = f,
    definitionAt = definitionFormula
  )(uniqueness)

  val id: Identifier = definedClassFunction.id

  val term: Expr[Ind] = definedClassFunction.term

  private val classFunctionCharacterization: THM = definedClassFunction.characterization

  val patterns: Seq[Pattern[N]] =
    patternMatching.patterns

  private val shortDefinitionByPattern: Map[Pattern[N], THM] =
    patterns.map(pattern =>
      pattern -> Lemma(
        simplify(
          pattern.branchPremise ==>
            (term * pattern.inputTerm === pattern.body)
        )
      ) {
        have(forall(f, (term === f) <=> untypedDef)) by
          Restate.from(classFunctionCharacterization)

        thenHave(
          (term === term) <=>
            (term :: typ) /\
            (seqAnd(patterns.map { branch =>
              forallSeq(
                branch.binders,
                branch.branchPremise ==>
                  (term * branch.inputTerm === branch.body)
              )
            }))
        ) by InstantiateForall(term)

        thenHave(
          forallSeq(
            pattern.binders,
            pattern.branchPremise ==>
              (term * pattern.inputTerm === pattern.body)
          )
        ) by Weakening

        pattern.binders.foldLeft(lastStep)((_, _) =>
          lastStep.statement.right.head match
            case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        thenHave(thesis) by Restate
      }
    ).toMap

  def shortDefinition(pattern: Pattern[N]): THM =
    shortDefinitionByPattern(pattern)

  def elimByPattern(pattern: Pattern[N]): THM =
    shortDefinition(pattern)

  private val elimByConstThm: Map[SemanticConstructor[N], THM] =
    PatternSystem.constructorCases(patterns)
      .map { (constructor, patternsForConst) =>
        constructor -> Lemma(
          seqAnd(patternsForConst.map(pattern =>
            simplify(pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body))
          ))
        ) {
          have(thesis) by Tautology.from(
            patternsForConst.map(pattern => shortDefinitionByPattern(pattern))*
          )
        }
      }
      .toMap

  def elimByConst(constructor: SemanticConstructor[N]): THM =
    elimByConstThm.getOrElse(
      constructor,
      throw new IllegalArgumentException(s"No pattern registered for constructor ${constructor.name}.")
    )

  def elim(pattern: Pattern[N]): THM =
    elimByPattern(pattern)

  def elim(constructor: SemanticConstructor[N]): THM =
    elimByConst(constructor)

  def shortDefinition(constructor: SemanticConstructor[N]): THM =
    elimByConst(constructor)

  val elimTotal: THM = Lemma(
    seqAnd(patterns.map(pattern =>
      simplify(pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body))
    ))
  ) {
    have(thesis) by Tautology.from(patterns.map(pattern => shortDefinitionByPattern(pattern))*)
  }

  val intro: THM = Lemma(term :: typ) {

    have(forall(f, (term === f) <=> untypedDef)) by
      Restate.from(classFunctionCharacterization)
    thenHave(
      (term === term) <=>
        (term :: typ) /\
        (seqAnd(patterns.map { pattern =>
          forallSeq(
            pattern.binders,
            pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body)
          )
        }))
    ) by InstantiateForall(term)
    thenHave(thesis) by Weakening
  }
}
