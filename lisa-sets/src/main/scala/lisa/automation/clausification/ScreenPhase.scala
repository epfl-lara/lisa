package lisa.automation.clausification

import lisa.utils.K.{_, given}
import lisa.automation.Problem
import Clausification.*

/**
 * Input screening, the topmost phase: it renames every free input variable into the reserved namespaces
 * (`v_i`/`P_i`/`F_i`, by result sort, counters from 1) and η-expands every quantifier, so that below it the
 * pipeline owns all remaining names and every `∀`/`∃` is an explicit `Application(forall, Lambda(x, b))`.
 */
private[clausification] object ScreenPhase:

  def certifyScreen(problem: Problem, prover: ClausificationProver): ClausificationProof =
    val renaming: Map[Variable, Variable] = screeningRenaming(problem)
    val sigma: Map[Variable, Expression]    = renaming.map((v, w) => v -> (w: Expression))
    val sigmaInv: Map[Variable, Expression] = renaming.map((v, w) => w -> (v: Expression))
    // The entry transformation: rename into the reserved namespaces, then η-expand.
    def screen(s: Sequent): Sequent = etaExpandSequent(applyTo(s, sigma))
    val screenedHyps: Seq[Sequent] = problem.hypotheses.map(screen)
    val screenedConj: Option[Sequent] = problem.conjecture.map(screen)
    // Pass through only when *neither* half does anything. `renaming.isEmpty` alone is not enough: an
    // already-screened problem can still carry η-reduced quantifiers, and skipping the phase would leave them.
    if renaming.isEmpty && screenedHyps == problem.hypotheses && screenedConj == problem.conjecture then prover(problem)
    else
      val transformed = Problem(screenedHyps, screenedConj, problem.frozen.map(v => renaming.getOrElse(v, v)))
      val downstream = prover(transformed)
      require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

      // One step per hypothesis, deducting its screened form with instantiation (or `Restate` if there is no renaming)
      val instSteps: IndexedSeq[ClausificationProofStep] =
        screenedHyps.toIndexedSeq.zipWithIndex.map { case (h, i) =>
          if sigma.isEmpty then Restate(h, problem.hypIndex(i)) else InstSchema(h, problem.hypIndex(i), sigma)
        }
      val subproof = ClausificationSubproof(downstream, instSteps.indices.toIndexedSeq ++ libRefs(problem.imports.size))
      // Restore the caller's names. `σ⁻¹` may α-rename a binder that shadows one of the canonical targets, so
      // prefer the caller's own conjecture sequent when it is the same up to α (callers compare the produced
      // conclusion to their goal structurally)
      val computed = applyTo(subproof.bot, sigmaInv)
      val restored = problem.conjecture.filter(c => isSameSequent(c, computed)).getOrElse(computed)
      val steps =
        if restored == subproof.bot then instSteps :+ subproof
        else instSteps :+ subproof :+
          (if sigmaInv.isEmpty then Restate(restored, instSteps.size) else InstSchema(restored, instSteps.size, sigmaInv))
      ClausificationProof(steps, problem.imports ++ libImports)

  /** η-expand every quantifier on both sides of `s`. See the class doc for why this is the pipeline's entry
    * invariant and why it is free at the kernel level. */
  private def etaExpandSequent(s: Sequent): Sequent =
    Sequent(s.left.map(etaExpandQuantifiers), s.right.map(etaExpandQuantifiers))

  /** The screening renaming: every free variable of the problem to its canonical twin, in a deterministic order
    * (`Ind` variables to `v_1, v_2, …`, predicates to `P_1, P_2, …`, functions to `F_1, F_2, …`). Variables that
    * are already their own canonical twin are dropped, so a fully-screened problem gets an empty map (and a
    * pass-through proof). Third-order and higher variables are dropped too, see below. */
  private[clausification] def screeningRenaming(problem: Problem): Map[Variable, Variable] =
    val sequents: Seq[Sequent] = problem.hypotheses ++ problem.conjecture
    val free: Seq[Variable] = sequents.iterator
      .flatMap(s => s.left.iterator ++ s.right.iterator)
      .flatMap(_.freeVariables)
      .toSeq.distinct
      .sortBy(v => (v.id.name, v.id.no, v.sort.toString)) // sequent sides are Sets, so order the traversal explicitly
    // Three namespaces: an `Ind` variable is a clause variable, a predicate sort `Ind → … → Ind → Prop` a
    // predicate, a function sort `Ind → … → Ind → Ind` a function (the kernel's own `isPredicate`/`isFunctional`,
    // which `Ind` itself also satisfies, hence the split off first). A variable of any other sort is left unchanged as
    // the pipeline never creates new ones.
    val inds   = free.filter(_.sort == Ind)
    val higher = free.filterNot(_.sort == Ind)
    val preds  = higher.filter(_.sort.isPredicate)
    val funs   = higher.filter(_.sort.isFunctional)
    // Counters start at 1, so no screened name is a bare prefix.
    def canonical(vs: Seq[Variable], prefix: String): Seq[(Variable, Variable)] =
      vs.zipWithIndex.map((v, i) => v -> Variable(Identifier(prefix, i + 1), v.sort))
    (canonical(inds, GeneratedNames.inputVar)
      ++ canonical(preds, GeneratedNames.inputPred)
      ++ canonical(funs, GeneratedNames.inputFun)).filter((v, w) => v != w).toMap

  private def applyTo(s: Sequent, m: Map[Variable, Expression]): Sequent =
    Sequent(s.left.map(substituteVariablesOpti(_, m)), s.right.map(substituteVariablesOpti(_, m)))
