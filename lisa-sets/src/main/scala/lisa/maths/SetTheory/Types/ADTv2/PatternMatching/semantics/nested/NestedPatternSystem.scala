package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.nested

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{Pattern, PatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.forallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.seqOr
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.wellTypedFormula

/**
 * Pattern system supporting multi-level nested patterns (e.g. `isGreaterThanTwo`),
 * where guards may be non-nullary, possibly deeply nested constructor terms whose
 * inner variables are tracked as binders (see [[NestedConstructorPattern]]).
 *
 * It discharges the two obligations the (non-recursive) `fun` path needs —
 * `coverage` and `incompatible` — via the trie-folding generators in
 * [[NestedTrieProofs]], producing the exact trait statement shapes consumed by
 * `WitnessFunctionProofs`. `branchSelectionFor` (recursion only) is not yet
 * implemented.
 */
private[PatternMatching] final case class NestedPatternSystem(
    domain: SemanticADT,
    override val patterns: Seq[NestedConstructorPattern],
    typeSubstitutions: Seq[TypeSubstitution] = Seq.empty,
    specializedAdtTerm: Expr[Ind]
) extends PatternSystem {
  import NestedTrie.Tree
  import NestedTrie.Tree.{Fail, Leaf, Switch}

  validate()

  lazy val (adt, targs) = ADT.unapply(specializedAdtTerm).get

  override def constructors: Seq[SemanticConstructor] = domain.constructors

  override def patternsFor(constructor: SemanticConstructor): Seq[Pattern] =
    patterns.filter(_.semanticConstructor == constructor)

  // The split branches carry guard conditions, so coverage is not automatic.
  override def supportsAutomaticCoverage: Boolean = false

  override lazy val coverage: THM =
    {
      NestedTrieProofs.coverageCaseShape((adt, targs), clauses, patterns)
    }

  override def incompatible(pattern1: Pattern, pattern2: Pattern): THM =
    incompatibleCache.getOrElseUpdate(
      (pattern1, pattern2),
      {
        NestedTrieProofs.incompatibleCaseShape(
          pattern1.asInstanceOf[NestedConstructorPattern],
          pattern2.asInstanceOf[NestedConstructorPattern]
        )
      }
    )

  override def branchSelectionFor(constructor: SemanticConstructor, term: Expr[Ind]): THM =
    branchSelectionCache.getOrElseUpdate(
      (constructor, term),
      {
        val pats = patternsFor(constructor).map(_.asInstanceOf[NestedConstructorPattern])
        if pats.forall(_.guards.isEmpty) then
          // single unconditional pattern: the selection is trivial.
          val target = forallSeq(
            constructor.variables2,
            (wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*) /\
              (term === constructor.appliedTerm2).substitute(typeSubstitutions*)) ==>
              seqOr(pats.map(p => p.branchSelectionDisjunct(term)))
          )
          Lemma(target.asInstanceOf[Expr[Prop]]) { have(thesis) by Tautology }
        else
          NestedTrieProofs.branchSelectionForCaseShape(
            constructor,
            term,
            pats,
            typeSubstitutions
          )
      }
    )

  // ── helpers ────────────────────────────────────────────────────────────────

  // Reconstruct each clause as (constructor, value-argument terms): the guard term
  // at guarded positions, the binder variable elsewhere.
  private lazy val clauses: Seq[(Constructor[?], Seq[Expr[Ind]])] =
    patterns.map(p => (interfaceCtor(p.semanticConstructor), clauseArgs(p)))

  private def clauseArgs(p: NestedConstructorPattern): Seq[Expr[Ind]] =
    (0 until p.arity).map(i => p.guards.find(_.position == i).map(_.guardTerm).getOrElse(p.topBinders(i)))

  private def interfaceCtor(sc: SemanticConstructor): Constructor[?] =
    ADT.allADTs.toSeq.flatMap(_.constructors).find(_.id == sc.id).getOrElse(throw new IllegalArgumentException(s"No interface constructor for ${sc.name}."))

  private def gapNodes(tree: Tree): Seq[(NestedTrie.Occ, List[String])] = tree match
    case Fail(occ, missing) => Seq((occ, missing))
    case Switch(_, _, cases) => cases.flatMap((_, subtree) => gapNodes(subtree))
    case Leaf(_, _, _) => Seq.empty

  private def overlapNodes(tree: Tree): Seq[List[Int]] = tree match
    case Leaf(clause, _, alsoMatched) if alsoMatched.nonEmpty => Seq(clause :: alsoMatched)
    case Switch(_, _, cases) => cases.flatMap((_, subtree) => overlapNodes(subtree))
    case _ => Seq.empty

  private def formattedGapSummary(tree: Tree): String =
    gapNodes(tree)
      .groupBy((occ, _) => occ)
      .toSeq
      .sortBy((occ, _) => occ.mkString("."))
      .map { (occ, entries) =>
        val position = NestedTrie.occName(occ)
        val missingConstructors = entries.flatMap(_._2).distinct.sorted.mkString(", ")
        s"At nested position $position, the following constructor case(s) are missing: $missingConstructors."
      }
      .mkString(" ")

  private def formattedOverlapSummary(tree: Tree): String =
    overlapNodes(tree)
      .map(clauses => s"Clauses ${clauses.distinct.sorted.mkString(", ")} overlap.")
      .mkString(" ")

  // Exhaustive + pairwise-disjoint check via the trie scope checker.
  private def validate(): Unit =
    val tree = NestedTrie.buildTree(adt, targs, clauses)
    val gaps = NestedTrie.gaps(tree)
    val overlaps = NestedTrie.overlaps(tree)
    require(
      gaps.isEmpty,
      s"""NestedPatternSystem rejected the nested pattern set for ADT ${adt.name} because it is not exhaustive.
         |${formattedGapSummary(tree)}
         |This means some constructor combination is not matched by any clause.
         |Decision trie:
         |${NestedTrie.render(tree)}""".stripMargin
    )
    require(
      overlaps.isEmpty,
      s"""NestedPatternSystem rejected the nested pattern set for ADT ${adt.name} because some clauses overlap and would require an explicit priority rule.
         |${formattedOverlapSummary(tree)}
         |Decision trie:
         |${NestedTrie.render(tree)}""".stripMargin
    )
}
