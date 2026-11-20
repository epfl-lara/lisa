package lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADT.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiate
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.utils.prooflib.Thm

/**
 * A resolved branch paired with its function body or induction proof.
 */
final case class Clause[A](pattern: Pattern, payload: A) {
  export pattern.*

  /**
   * Changes the payload while retaining the exact pattern and its binders.
   */
  def map[B](f: A => B): Clause[B] = Clause(pattern, f(payload))

  /**
   * The expression carried by a function clause.
   */
  def body(using ev: A =:= Expr[Ind]): Expr[Ind] = ev(payload)

  /**
   * Instantiates the body at the supplied binder values.
   */
  def bodySubstituted(substitutions: Seq[(Variable[Ind], Expr[Ind])])(using A =:= Expr[Ind]): Expr[Ind] =
    body.substitute(substitutions.map((v, term) => v := term)*)

  /**
   * Instantiates the body at the supplied proof variables.
   */
  def bodyAt(vars: Seq[Variable[Ind]])(using A =:= Expr[Ind]): Expr[Ind] =
    bodySubstituted(binders.zip(vars))

  /**
   * The body at the second tuple of proof variables.
   */
  def bodyAtFreshVars2(using A =:= Expr[Ind]): Expr[Ind] = bodyAt(variables2)

  /**
   * Membership in this clause's graph, with its witnesses existentially bound.
   */
  private[ADT] def caseMembership(value: Expr[Ind])(using A =:= Expr[Ind]): Expr[Prop] =
    existsSeq(variables2, freshBranchPremise /\ (value === pair(freshInputTerm, bodyAtFreshVars2)))
}

/**
 * Ordered clauses with one validated tree and shared pattern theorems.
 */
final class PatternSystem[A] private (
    val clauses: Seq[Clause[A]],
    private val proofs: PatternSystem.Proofs
) {

  /**
   * The specialized datatype matched by the clauses.
   */
  def domain: SpecializedADT[?] = proofs.domain

  /**
   * The branch patterns in source order.
   */
  def patterns: Seq[Pattern] = proofs.patterns

  /**
   * The retained tree, whose leaf indices refer to the source clause order.
   */
  private[ADT] def decisionTree: DecisionTree = proofs.decisionTree

  /**
   * Changes payloads without recompiling patterns or regenerating their theorems.
   */
  def map[B](f: A => B): PatternSystem[B] =
    new PatternSystem(clauses.map(_.map(f)), proofs)

  /**
   * The constructors of the matched datatype.
   */
  def constructors: Seq[SemanticConstructor] = domain.base.semantic.constructors

  /**
   * Selects clauses headed by the given constructor, retaining source order.
   */
  def clausesFor(constructor: SemanticConstructor): Seq[Clause[A]] =
    clauses.filter(_.semanticConstructor == constructor)

  /**
   * Membership in the graph described by function clauses.
   */
  def caseMembership(value: Expr[Ind])(using A =:= Expr[Ind]): Expr[Prop] =
    seqOr(clauses.map(_.caseMembership(value)))

  /**
   * The disjunction asserting that some pattern matches the input.
   */
  def caseCoverage(term: Expr[Ind]): Expr[Prop] =
    seqOr(patterns.map(pattern => existsSeq(pattern.variables2, pattern.freshBranchPremise /\ (term === pattern.freshInputTerm))))

  /**
   * Every member of the domain matches a clause.
   */
  def coverage: Theorem = proofs.coverage

  /**
   * The cached branch-selection theorem with a schematic input.
   */
  private[ADT] def branchSelectionSchema(constructor: SemanticConstructor): Theorem =
    proofs.branchSelectionCache.getOrElseUpdate(
      constructor,
      PatternProofs.branchSelectionForCaseShape(decisionTree, constructor, proofs.selectionInput, patterns)
    )

  /**
   * Instantiates branch selection for a known constructor without rebuilding its proof.
   */
  def branchSelectionFor(constructor: SemanticConstructor, term: Expr[Ind])(using proof: lisa.SetTheoryLibrary.ProofBuilder): Thm =
    instantiate(branchSelectionSchema(constructor), Seq(proofs.selectionInput := term))

  /**
   * Distinct clauses cannot match the same input.
   */
  def incompatible(first: Pattern, second: Pattern): Theorem =
    proofs.incompatibleCache.getOrElseUpdate((first, second), PatternProofs.incompatibleCaseShape(first, second))

  /**
   * The pattern theorems collected for inspection.
   */
  lazy val debugTheorems: Seq[(String, Theorem)] = {
    val selectors = constructors.map { constructor =>
      ("branchSelectionFor(" + constructor.name + ")", branchSelectionSchema(constructor))
    }
    val incompatibilities = patterns.zipWithIndex.flatMap { (first, index) =>
      patterns.drop(index + 1).zipWithIndex.map { (second, offset) =>
        ("incompatible(" + index + "," + (index + offset + 1) + ")", incompatible(first, second))
      }
    }
    ("coverage", coverage) +: (selectors ++ incompatibilities)
  }

  /**
   * Prints the retained tree and its pattern theorems.
   */
  lazy val debugDump: Unit = {
    println(DecisionTree.render(decisionTree))
    debugTheorems.foreach((label, theorem) => println("[" + label + "] " + theorem.statement))
  }
}

/**
 * Compiles collections of clauses and owns their body-independent proof caches.
 */
object PatternSystem {
  private final class Proofs(
      val domain: SpecializedADT[?],
      val patterns: Seq[Pattern],
      val decisionTree: DecisionTree
  ) {
    lazy val coverage: Theorem = PatternProofs.coverageCaseShape(decisionTree, patterns)
    val incompatibleCache = collection.mutable.Map.empty[(Pattern, Pattern), Theorem]
    val selectionInput = Variable[Ind](
      freshId(
        patterns.flatMap(p => p.binders ++ p.variables2 ++ Seq(p.resolved.term, p.specializedAdtTerm)) :+ domain.term,
        "branchInput"
      )
    )
    val branchSelectionCache = collection.mutable.Map.empty[SemanticConstructor, Theorem]
  }

  /**
   * Validates the collection once before any pattern theorems are constructed.
   */
  def compile[A](domain: SpecializedADT[?], clauses: Seq[Clause[A]]): Either[String, PatternSystem[A]] = {
    val ordered = clauses.toVector
    ordered.find(clause => clause.resolved.constructor.adt.id != domain.base.id || !isSame(clause.specializedAdtTerm, domain.term)) match
      case Some(clause) => Left("Pattern " + clause.name + " was compiled for " + clause.specializedAdtTerm + ", expected " + domain.term + ".")
      case None =>
        val patterns = ordered.map(_.pattern)
        DecisionTree.compile(domain, patterns.map(_.resolved)).map { tree =>
          new PatternSystem(ordered, new Proofs(domain, patterns, tree))
        }
  }
}
