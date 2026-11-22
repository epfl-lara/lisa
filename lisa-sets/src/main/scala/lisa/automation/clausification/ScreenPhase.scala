package lisa.automation.clausification

import lisa.automation.Problem
import lisa.automation.ProofSyntax.{_, given}

import Clausification._

/**
 * Input screening, the topmost phase: it renames every free input variable into the reserved namespaces
 * (`v_i`/`P_i`/`F_i`, by result sort, counters from 1) and η-expands every quantifier, so that below it the
 * pipeline owns all remaining names and every `∀`/`∃` is an explicit `Application(forall, Lambda(x, b))`.
 */
private[clausification] object ScreenPhase:

  def certifyScreen(problem: Problem, prover: ClausificationProver, goal: Set[Int] = Set.empty)(using ClausifierOptions): ClausificationProof =
    val renaming: Map[Variable, Variable] = screeningRenaming(problem)
    val sigma: Map[Variable, Expression] = renaming.map((v, w) => v -> (w: Expression))
    val sigmaInv: Map[Variable, Expression] = renaming.map((v, w) => w -> (v: Expression))
    val steps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    def emit(step: ClausificationProofStep): Int =
      steps += step
      steps.size - 1

    val (screenedHyps, hypRefs) = problem.hypotheses.iterator.zipWithIndex.map { case (source, i) =>
      val renamed = applyTo(source, sigma)
      val screened = etaExpandSequent(renamed)
      val premise = problem.hypIndex(i)
      val renamedRef = if renamed == source then premise else emit(InstSchema(renamed, premise, sigma))
      val screenedRef = if screened == renamed then renamedRef else emit(Restate(screened, renamedRef))
      (screened, screenedRef)
    }.toVector.unzip
    val renamedConj = problem.conjecture.map(applyTo(_, sigma))
    val screenedConj = renamedConj.map(etaExpandSequent)
    if renaming.isEmpty && steps.isEmpty && screenedConj == problem.conjecture then prover(problem, goal)
    else
      val transformed = Problem(screenedHyps, screenedConj, problem.frozen.map(v => renaming.getOrElse(v, v)))
      val downstream = prover(transformed, goal)
      require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

      val subproof = ClausificationSubproof(downstream, hypRefs ++ libRefs(problem.imports.size))
      val subRef = emit(subproof)
      // Undo the two entry transformations in reverse order. Use the caller's original binders
      // when undoing the renaming, since capture avoidance may have freshened them.
      (problem.conjecture, renamedConj, screenedConj) match
        case (Some(original), Some(renamed), Some(screened)) if subproof.bot == screened =>
          val renamedRef = if renamed == screened then subRef else emit(Restate(renamed, subRef))
          if original != renamed then emit(InstSchema(original, renamedRef, sigmaInv))
        case _ =>
          val restored = applyTo(subproof.bot, sigmaInv)
          if restored != subproof.bot then emit(InstSchema(restored, subRef, sigmaInv))
      ClausificationProof(steps.toIndexedSeq, problem.imports ++ libImports)

  /**
   * η-expand every quantifier on both sides of `s`. See the class doc for why this is the pipeline's entry
   * invariant and why it is free at the kernel level.
   */
  private def etaExpandSequent(s: Sequent): Sequent =
    Sequent(s.left.map(etaExpandQuantifiers), s.right.map(etaExpandQuantifiers))

  /**
   * The screening renaming: every free variable of the problem to its canonical twin, in a deterministic order
   * (`Ind` variables to `v_1, v_2, …`, predicates to `P_1, P_2, …`, functions to `F_1, F_2, …`). Variables that
   * are already their own canonical twin are dropped, so a fully-screened problem gets an empty map (and a
   * pass-through proof). Third-order and higher variables are dropped too, see below.
   */
  private[clausification] def screeningRenaming(problem: Problem): Map[Variable, Variable] =
    val sequents: Seq[Sequent] = problem.hypotheses ++ problem.conjecture
    val free: Seq[Variable] = sequents.iterator
      .flatMap(s => s.left.iterator ++ s.right.iterator)
      .flatMap(_.freeVariables)
      .toSeq
      .distinct
      .sortBy(v => (v.id.name, v.id.no, v.sort.toString)) // sequent sides are Sets, so order the traversal explicitly
    // Three namespaces: an `Ind` variable is a clause variable, a predicate sort `Ind → … → Ind → Prop` a
    // predicate, a function sort `Ind → … → Ind → Ind` a function (the kernel's own `isPredicate`/`isFunctional`,
    // which `Ind` itself also satisfies, hence the split off first). A variable of any other sort is left unchanged as
    // the pipeline never creates new ones.
    val inds = free.filter(_.sort == Ind)
    val higher = free.filterNot(_.sort == Ind)
    val preds = higher.filter(_.sort.isPredicate)
    val funs = higher.filter(_.sort.isFunctional)
    // Counters start at 1, so no screened name is a bare prefix.
    def canonical(vs: Seq[Variable], prefix: String): Seq[(Variable, Variable)] =
      vs.zipWithIndex.map((v, i) => v -> Variable(Identifier(prefix, i + 1), v.sort))
    (canonical(inds, GeneratedNames.inputVar)
      ++ canonical(preds, GeneratedNames.inputPred)
      ++ canonical(funs, GeneratedNames.inputFun)).filter((v, w) => v != w).toMap

  private def applyTo(s: Sequent, m: Map[Variable, Expression]): Sequent =
    if m.isEmpty then s else Sequent(s.left.map(substituteVariablesOpti(_, m)), s.right.map(substituteVariablesOpti(_, m)))
