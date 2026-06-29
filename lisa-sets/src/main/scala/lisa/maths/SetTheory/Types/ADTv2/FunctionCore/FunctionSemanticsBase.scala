package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.UniqueCharacterizedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.core.**
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Semantic layer shared by the non-recursive
 * ([[lisa.maths.SetTheory.Types.ADTv2.functions.SemanticFunction]]) and
 * recursive ([[lisa.maths.SetTheory.Types.ADTv2.recursion.SemanticFunction]])
 * cases.
 *
 * The two cases produce existence and pointwise uniqueness very differently
 * (a single `RightExists` on the witness vs. the approximant/limit fixpoint
 * construction; direct case coverage vs. well-founded induction on height), and
 * supply those — together with the spec and the pattern bodies — through a
 * [[SemanticFunctionInputs]] strategy. Everything downstream is identical and
 * lives here: assembling existential uniqueness, introducing the defined symbol
 * via [[UniqueCharacterizedSymbol]], and deriving the elimination/introduction
 * theorems from its characterization `forall(f, (term === f) <=> untypedDef)`.
 */
class FunctionSemanticsBase[N <: Arity](data: SemanticFunctionInputs[N]) {
  val name: String = data.name
  val argType: Expr[Ind] = data.spec.argType
  val returnType: Expr[Ind] = data.spec.returnType
  val typeVariables: Variable[Ind] ** N = data.spec.adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = data.spec.typeVariablesSeq
  val typeArity: N = data.spec.typeArity
  val typ: Expr[Ind] = data.spec.typ

  /**
   * The defined symbol, characterized by `forall(f, (term === f) <=> untypedDef)`,
   * assembled from the separately-proved existence and pointwise-uniqueness facts
   * supplied by the strategy.
   */
  private val definedClassFunction: UniqueCharacterizedSymbol =
    UniqueCharacterizedSymbol.fromParts(
      name = name,
      typeVariablesSeq = typeVariablesSeq,
      witnessVar = f,
      definitionAt = data.spec.definitionAt
    )(data.existence.witnessExists, data.uniqueness.pointwiseUniqueness)

  val id: Identifier = definedClassFunction.id

  val term: Expr[Ind] = definedClassFunction.term

  def term(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)

  val patterns: Seq[Pattern[N]] =
    data.buildPatterns(term)

  /**
   * For each pattern, the short defining equation
   * `branchPremise ==> (term * inputTerm === body)`.
   */
  private val shortDefinitionByPattern: Map[Pattern[N], THM] =
    patterns
      .map(pattern =>
        pattern -> Lemma(
          simplify(
            pattern.branchPremise ==>
              (term * pattern.inputTerm === pattern.body)
          )
        ) {
          have(
            forallSeq(
              pattern.binders,
              pattern.branchPremise ==>
                (term * pattern.inputTerm === pattern.body)
            )
          ) by Weakening(definedClassFunction.definitionFact)

          pattern.binders.foldLeft(lastStep)((_, _) =>
            lastStep.statement.right.head match
              case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException
          )
          thenHave(thesis) by Restate
        }
      )
      .toMap

  def shortDefinition(pattern: Pattern[N]): THM =
    shortDefinitionByPattern(pattern)

  def elimByPattern(pattern: Pattern[N]): THM =
    shortDefinition(pattern)

  /**
   * For each constructor, the conjunction of the short defining equations of
   * the patterns covering it.
   */
  private val elimByConstThm: Map[SemanticConstructor[N], THM] =
    PatternSystem
      .constructorCases(patterns)
      .map { (constructor, patternsForConst) =>
        constructor -> Lemma(
          seqAnd(patternsForConst.map(pattern => simplify(pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body))))
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

  /**
   * The conjunction of the short defining equations of all patterns.
   */
  val elimTotal: THM = Lemma(
    seqAnd(patterns.map(pattern => simplify(pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body))))
  ) {
    have(thesis) by Tautology.from(patterns.map(pattern => shortDefinitionByPattern(pattern))*)
  }

  /**
   * Typing introduction: the defined symbol inhabits its function type.
   */
  val intro: THM = Lemma(term :: typ) {
    have(thesis) by Weakening(definedClassFunction.definitionFact)
  }
}
