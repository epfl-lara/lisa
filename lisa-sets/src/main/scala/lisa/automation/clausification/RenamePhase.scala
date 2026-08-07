package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Variable-renaming (screening) phase. Runs **after** [[NegatedPhase]] (so the conjecture is already folded in as a
 * hypothesis) and **before** naming: it rewrites every **open** variable of each hypothesis to the reserved
 * canonical scheme `v_0, v_1, …` (each keeping its own sort).
 *
 * Purpose: every fresh symbol/variable the clausifier introduces downstream uses a *disjoint* prefix — `esk`, `ts`,
 * `sk`, `w`, `nm`, `HOLE`, `abs`, `cv`, … (see the full inventory in
 * [[Clausification.GeneratedNames]]) — none of them the bare `v`. So canonicalising the input's open variables into
 * the `v` namespace guarantees they can neither capture nor be captured by anything we introduce later, without
 * threading a "taken identifiers" set through every phase.
 *
 * Certified by exactly **one `InstSchema` step per hypothesis**, instantiating its open variables to the fresh
 * `v_i` — a bijective renaming, hence sound. A hypothesis with no open variable is passed through unchanged.
 */
private[clausification] object RenamePhase:

  def certifyRename(problem: Problem, prover: ClausificationProver): ClausificationProof =
    val renamed: Seq[(Sequent, Map[Variable, Expression])] = problem.hypotheses.map(h => renameOpenVars(h, problem.frozen))
    val transformed = Problem(renamed.map(_._1), None, problem.frozen)
    val downstream = prover(transformed)
    require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

    // One `InstSchema` per hypothesis, bridging the original import to its `v_i`-renamed form (identity substitution
    // for a hypothesis with no open variable). The subproof then runs over the renamed hypotheses + the lib imports.
    val instSteps: IndexedSeq[ClausificationProofStep] =
      renamed.zipWithIndex.map { case ((h2, subst), i) => KernelStep(InstSchema(h2, problem.hypIndex(i), subst)) }.toIndexedSeq
    val subproof = ClausificationSubproof(downstream, instSteps.indices.toIndexedSeq ++ libRefs(problem.imports.size))
    ClausificationProof(instSteps :+ subproof, problem.imports ++ libImports)

  /** Rename every open variable of `s` (except `frozen` Skolem symbols, which are pinned) to `v_i` of its own sort,
   *  in a deterministic order; return the renamed sequent and the substitution used to certify it via `InstSchema`. */
  private def renameOpenVars(s: Sequent, frozen: Set[Variable]): (Sequent, Map[Variable, Expression]) =
    val open: Seq[Variable] = (s.left.iterator ++ s.right.iterator)
      .flatMap(_.freeVariables).filterNot(frozen.contains).toSeq.distinct.sortBy(v => (v.id.name, v.id.no))
    val subst: Map[Variable, Expression] =
      open.iterator.zipWithIndex.map { (v, i) => v -> (Variable(Identifier(GeneratedNames.inputVar, i), v.sort): Expression) }.toMap
    if subst.isEmpty then (s, subst)
    else (Sequent(s.left.map(substituteVariables(_, subst)), s.right.map(substituteVariables(_, subst))), subst)
