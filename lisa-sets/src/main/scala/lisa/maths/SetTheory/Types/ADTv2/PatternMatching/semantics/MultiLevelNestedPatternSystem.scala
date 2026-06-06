package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.{SemanticADT, SemanticConstructor}
import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.{existsSeq, forallSeq, seqOr, wellTypedFormula}
import lisa.utils.prooflib.ProofTacticLib.Arity

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
final case class MultiLevelNestedPatternSystem[N <: Arity](
    domain: SemanticADT[N],
    override val patterns: Seq[NestedConstructorPattern[N]],
    typeSubstitutions: Seq[TypeSubstitution] = Seq.empty,
    specializedAdtTerm: Expr[Ind]
) extends PatternSystem[N] {

  validate()

  override def constructors: Seq[SemanticConstructor[N]] = domain.constructors

  override def patternsFor(constructor: SemanticConstructor[N]): Seq[Pattern[N]] =
    patterns.filter(_.semanticConstructor == constructor)

  // The split branches carry guard conditions, so coverage is not automatic.
  override def supportsAutomaticCoverage: Boolean = false

  override def coverage(dom: SemanticADT[N]): THM =
    val (adt, targs) = ADT.unapply(specializedAdtTerm).get
    NestedTrieProofs.coverageCaseShape((adt, targs), clauses, patterns)

  override def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM =
    NestedTrieProofs.incompatibleCaseShape(
      pattern1.asInstanceOf[NestedConstructorPattern[?]],
      pattern2.asInstanceOf[NestedConstructorPattern[?]])

  override def branchSelectionFor(constructor: SemanticConstructor[N], term: Expr[Ind]): THM =
    val pats = patternsFor(constructor).map(_.asInstanceOf[NestedConstructorPattern[N]])
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
        constructor, interfaceCtor(constructor), term, pats, typeSubstitutions)

  // ── helpers ────────────────────────────────────────────────────────────────

  // Reconstruct each clause as (constructor, value-argument terms): the guard term
  // at guarded positions, the binder variable elsewhere.
  private def clauses: Seq[(Constructor[?], Seq[Expr[Ind]])] =
    patterns.map(p => (interfaceCtor(p.semanticConstructor), clauseArgs(p)))

  private def clauseArgs(p: NestedConstructorPattern[N]): Seq[Expr[Ind]] =
    (0 until p.arity).map(i =>
      p.guards.find(_.position == i).map(_.guardTerm).getOrElse(p.topBinders(i)))

  private def interfaceCtor(sc: SemanticConstructor[N]): Constructor[?] =
    ADT.allADTs.toSeq.flatMap(_.constructors).find(_.id == sc.id).getOrElse(
      throw new IllegalArgumentException(s"No interface constructor for ${sc.name}."))

  // Exhaustive + pairwise-disjoint check via the trie scope checker.
  private def validate(): Unit =
    val (adt, targs) = ADT.unapply(specializedAdtTerm).get
    val tree = NestedTrie.buildTree(adt, targs, clauses)
    val gaps = NestedTrie.gaps(tree)
    val overlaps = NestedTrie.overlaps(tree)
    require(gaps.isEmpty, s"MultiLevelNestedPatternSystem: not exhaustive — ${gaps.mkString("; ")}")
    require(overlaps.isEmpty, s"MultiLevelNestedPatternSystem: overlapping (needs priority) — ${overlaps.mkString("; ")}")
}
