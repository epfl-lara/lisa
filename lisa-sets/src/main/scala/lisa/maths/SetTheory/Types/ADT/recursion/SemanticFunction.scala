package lisa.maths.SetTheory.Types.ADT.recursion

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.encoding._
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADT.support.UniqueDefinedSymbol
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._

/**
 * Constructs a function by recursion and proves its typing and case equations.
 */
final class SemanticFunction(
    val name: String,
    val typeVariablesSeq: Seq[Variable[Ind]],
    adt: SemanticADT,
    val argType: Expr[Ind],
    typeSubstitutions: Seq[TypeSubstitution],
    selfPlaceholder: Variable[Ind],
    patternMatching: PatternSystem[Expr[Ind]],
    val returnType: Expr[Ind]
) {
  private val spec = new FunSpec(name, typeVariablesSeq, adt, argType, typeSubstitutions, selfPlaceholder, patternMatching, returnType)
  private val witness = new Witness(spec)
  private val approxSeq = new ApproxSequence(spec, witness)
  private val witnessAgreement = new helpers.WitnessAgreement(spec, witness)
  private val approxStab = new ApproxStabilization(spec, witness, approxSeq, witnessAgreement)
  private val limitConstruction = new LimitConstruction(spec, approxSeq, approxStab)
  private val existence = new Existence(spec, witness, approxSeq, approxStab, limitConstruction, witnessAgreement)
  private val uniqueness = new Uniqueness(spec)

  /**
   * The function's set-theoretic type.
   */
  val typ: Expr[Ind] = spec.typ

  /**
   * Defines the unique function satisfying the typing and case equations.
   */
  private val definedClassFunction: UniqueDefinedSymbol =
    UniqueDefinedSymbol.fromParts(
      name = name,
      typeVariablesSeq = typeVariablesSeq,
      witnessVar = spec.proofVariable("f"),
      comparisonVariables = uniqueness.comparisonVariables,
      definitionAt = spec.definitionAt
    )(existence.witnessExists, uniqueness.pointwiseUniqueness)

  val id: Identifier = definedClassFunction.id

  val term: Expr[Ind] = definedClassFunction.term

  def term(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)

  /**
   * Instantiates the bodies while sharing the compiled clauses and their proof caches.
   */
  val cases: PatternSystem[Expr[Ind]] = patternMatching.map(_.substitute(selfPlaceholder := term))

  /**
   * The defining clauses of the completed function in source order.
   */
  val clauses: Seq[Clause[Expr[Ind]]] = cases.clauses

  private lazy val clauseIndices = clauses.zipWithIndex.toMap
  private lazy val clausesByConstructor = clauses.groupBy(_.semanticConstructor)
  private val shortDefinitions = scala.collection.mutable.Map.empty[Clause[Expr[Ind]], Theorem]
  private val constructorDefinitions = scala.collection.mutable.Map.empty[SemanticConstructor, Theorem]

  private def equation(pattern: Clause[Expr[Ind]]): Expr[Prop] =
    simplify(pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body))

  /**
   * Proves and caches the requested clause equation.
   */
  def shortDefinition(pattern: Clause[Expr[Ind]]): Theorem =
    shortDefinitions.getOrElseUpdate(
      pattern, {
        val index = clauseIndices.getOrElse(
          pattern,
          throw new IllegalArgumentException(s"Pattern ${pattern.name} does not belong to function $name.")
        )
        Lemma.named(s"$name/case/$index")(equation(pattern)) {
          have(forallSeq(pattern.binders, pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body))) by
            Weakening(definedClassFunction.definitionFact)
          pattern.binders.foreach { _ =>
            lastStep.statement.right.head match
              case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException
          }
          thenHave(thesis) by Restate
        }
      }
    )

  /**
   * Returns the cached equation of one clause.
   */
  def elimByPattern(pattern: Clause[Expr[Ind]]): Theorem =
    shortDefinition(pattern)

  private def combinedDefinition(patterns: Seq[Clause[Expr[Ind]]], suffix: String): Theorem =
    patterns match
      case Seq(pattern) => shortDefinition(pattern)
      case _ =>
        Lemma.named(s"$name/$suffix")(seqAnd(patterns.map(equation))) {
          have(thesis) by Tautology.from(patterns.map(shortDefinition)*)
        }

  /**
   * Caches one constructor's equations, reusing the branch theorem for a single clause.
   */
  def elimByConst(constructor: SemanticConstructor): Theorem =
    constructorDefinitions.getOrElseUpdate(
      constructor, {
        val patterns = clausesByConstructor.getOrElse(
          constructor,
          throw new IllegalArgumentException(s"No pattern registered for constructor ${constructor.name}.")
        )
        combinedDefinition(patterns, s"constructor/${constructor.name}")
      }
    )

  /**
   * Returns the cached equation of one clause.
   */
  def elim(pattern: Clause[Expr[Ind]]): Theorem =
    elimByPattern(pattern)

  /**
   * Returns the cached equations covering one constructor.
   */
  def elim(constructor: SemanticConstructor): Theorem =
    elimByConst(constructor)

  /**
   * Returns the cached equations covering one constructor.
   */
  def shortDefinition(constructor: SemanticConstructor): Theorem =
    elimByConst(constructor)

  /**
   * The conjunction of the short defining equations of all clauses.
   */
  lazy val elimTotal: Theorem = combinedDefinition(clauses, "cases")

  /**
   * Typing introduction: the defined symbol inhabits its function type.
   */
  val intro: Theorem = Lemma.generated(term :: typ) {
    have(thesis) by Weakening(definedClassFunction.definitionFact)
  }
}
