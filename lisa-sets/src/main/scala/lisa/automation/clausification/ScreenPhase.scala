package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Input-screening phase — the **topmost** phase of the certified pipeline, running *before* [[NegatedPhase]]. It
 * renames every free variable of the input problem into the three namespaces reserved for screened input, chosen
 * by the sort the symbol ultimately returns: [[Clausification.GeneratedNames.inputVar]] `v_i` for an `Ind`
 * variable, [[Clausification.GeneratedNames.inputPred]] `P_i` for a predicate (`Ind → … → Ind → Prop`, nullary
 * included), and [[Clausification.GeneratedNames.inputFun]] `F_i` for a function (`Ind → … → Ind → Ind`). From
 * here down the pipeline owns *all* the remaining names.
 *
 * The counters start at 1, so a screened name is never the bare prefix. That is what keeps `P_i` clear of
 * [[Clausification.schemaP]], which is `P` itself, and it is not a detail: a screened predicate that collided
 * with the schema the prenex and Skolem bridges instantiate would reintroduce exactly the fault this phase
 * exists to remove.
 *
 * '''Why the whole thing has to happen here, above `certifyNegated`.''' Every phase below runs inside a
 * [[ClausificationSubproof]] whose assumption is the negated conjecture `¬∀x̄.φ` (plus, deeper, the naming and
 * Skolem definitions), and an `InstSchema` on a variable free in an assumption is rejected by the kernel — the
 * restriction documented on [[ClausificationSubproof]]. But the pipeline *does* instantiate schema variables from
 * inside that region:
 *
 *   - the fixed placeholders `P`/`R` of the library statements — [[SkolemPhase.skolemizeOne]]'s bridge
 *     (`P := λx.φ` against [[Clausification.existsEpsilonIffStatement]]) and [[PrenexPhase]]'s lifting bridges
 *     (`P`, `R` against the four prenex laws);
 *   - the fresh symbols `esk_i` / `nm_i`, instantiated to their values by
 *     [[Clausification.dischargeAssumptionsLatestFirst]].
 *
 * So an input free variable that happens to be named like any of those (a Lisa goal over `P : Ind → Prop` or
 * `R : Prop` is the common case; `esk`/`nm` at a matching sort is the exotic one) is instantiated together with
 * the clausifier's own schema, the lowering pastes the *unchanged* assumption on the left, and the kernel rejects
 * the step. Only `Ind`-sorted variables could be screened lower down (they are ∀-closed in the assumption, hence
 * not free in it), which is why doing this per-hypothesis below `certifyNegated` — the previous `RenamePhase` —
 * could never cover the sorts that actually collide. Here every sequent still has an empty left-hand side, so a
 * plain `InstSchema` renaming is legal for all sorts at once.
 *
 * Screening is total rather than collision-driven on purpose: afterwards the invariant "no input name outside
 * `v`/`usr`" holds by construction, with no "taken identifiers" set threaded through the phases and no list of
 * reserved prefixes to keep in sync.
 *
 * ==The second half: η-expanding every quantifier==
 *
 * The phase also applies [[Clausification.etaExpandQuantifiers]] to every input formula, establishing the other
 * shape invariant the pipeline below relies on: '''every `∀`/`∃` is an explicit `Application(forall, Lambda(x, b))`'''.
 *
 * The kernel's `betaNormalForm` η-reduces `λy. p(y)` to `p`, so `∀y. p(y)` can present as `∀(p)` — which the
 * [[Forall]]/[[Exists]] extractors, needing a literal `Lambda`, do not match. Every phase below is written against
 * those extractors, so an η-reduced quantifier is silently treated as an *atom*: NNF does not push a negation
 * through it, `SkolemPhase` never Skolemizes it, `PrenexPhase.hasForall` does not strip it, and it reaches
 * [[DistributePhase]] as a literal (which now rejects it, but only as a backstop). Nothing is unsound — the clause
 * is still a consequence — but the problem quietly looks unprovable.
 *
 * Expanding at the *entry* rather than at the places that create the shape is what makes it an invariant
 * instead of a patch: a caller may simply hand us an η-reduced formula, which no producer-side repair covers.
 * The remaining obligation is "re-expand after any `betaNormalForm`", and [[SkolemPhase.skolemizeOne]] is the
 * only site that needs to. The uncertified [[UncertifiedClausifier]] path has the same input exposure and does the same
 * thing at its own entry, `clausalFormWithOrigins`.
 *
 * η-expansion is invisible to the kernel: `isSame` compares `betaNormalForm`s, so `∀(p)` and `∀(λz. p(z))` are
 * indistinguishable to it, and every step below accepts either form. It therefore costs no extra proof step and no
 * lemma. It is applied *after* the renaming, so the fresh `etaZ` binders cannot collide with anything of the
 * caller's — by the time they are minted, every input name is already a `v`/`usr`.
 *
 * '''Certification.''' Write `screen(·) = ηexp(σ(·))`. The renaming `σ` is injective (distinct canonical targets)
 * and applied simultaneously, so both it and its inverse are legal instantiations:
 *
 * {{{
 *   0 .. n-1   InstSchema(⊢ screen(hypᵢ), -(i+1), σ)   -- lift each hypothesis import to its screened form
 *   n          ClausificationSubproof(pipeline on the screened problem)      -- concludes ⊢ screen(φ)
 *   n+1        InstSchema(⊢ φ, n, σ⁻¹)                 -- restore the caller's names in the conclusion
 * }}}
 *
 * `InstSchema` checks with `containsEq`, i.e. up to `isSame`, so the η-expansion rides along inside these steps
 * for free. When `σ` is empty but the η-expansion is not, the same two slots are a plain `Restate` — the honest
 * step for a reshaping that instantiates nothing.
 *
 * The last step is omitted when neither half touches the conclusion (a conjecture-free refutation concludes `⊢`).
 */
private[clausification] object ScreenPhase:

  def certifyScreen(problem: Problem, prover: ClausificationProver): ClausificationProof =
    val renaming: Map[Variable, Variable] = screeningRenaming(problem)
    val sigma: Map[Variable, Expression]    = renaming.map((v, w) => v -> (w: Expression))
    val sigmaInv: Map[Variable, Expression] = renaming.map((v, w) => w -> (v: Expression))
    // The entry transformation, in this order: rename into the reserved namespaces, *then* η-expand — so the
    // fresh `etaZ` binders are minted against names that are already all `v`/`usr`.
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

      // One step per hypothesis, lifting the import `() ⊢ hypᵢ` to its screened form. `InstSchema` is what performs
      // the renaming; with no renaming to do it degenerates to a reshaping, which `Restate` states more honestly.
      // Either step accepts the η-expansion, since both check up to `isSame` and that ignores it.
      val instSteps: IndexedSeq[ClausificationProofStep] =
        screenedHyps.toIndexedSeq.zipWithIndex.map { case (h, i) =>
          KernelStep(if sigma.isEmpty then Restate(h, problem.hypIndex(i)) else InstSchema(h, problem.hypIndex(i), sigma))
        }
      val subproof = ClausificationSubproof(downstream, instSteps.indices.toIndexedSeq ++ libRefs(problem.imports.size))
      // Restore the caller's names. `σ⁻¹` may α-rename a binder that shadows one of the canonical targets, so
      // prefer the caller's own conjecture sequent when it is the same up to α (callers compare the produced
      // conclusion to their goal structurally); the kernel's `InstSchema` check is up to α either way. The same
      // preference is what hands back the caller's *un*-expanded quantifiers: `isSameSequent` does not
      // distinguish the two forms, so the original sequent is chosen over the reconstructed one.
      val computed = applyTo(subproof.bot, sigmaInv)
      val restored = problem.conjecture.filter(c => isSameSequent(c, computed)).getOrElse(computed)
      val steps =
        if restored == subproof.bot then instSteps :+ subproof
        else instSteps :+ subproof :+ KernelStep(
          if sigmaInv.isEmpty then Restate(restored, instSteps.size) else InstSchema(restored, instSteps.size, sigmaInv))
      ClausificationProof(steps, problem.imports ++ libImports)

  /** η-expand every quantifier on both sides of `s` — see the class doc for why this is the pipeline's entry
    * invariant and why it is free at the kernel level. */
  private def etaExpandSequent(s: Sequent): Sequent =
    Sequent(s.left.map(etaExpandQuantifiers), s.right.map(etaExpandQuantifiers))

  /** The screening renaming: every free variable of the problem to its canonical twin, in a deterministic order
    * (`Ind` variables to `v_1, v_2, …`, predicates to `P_1, P_2, …`, functions to `F_1, F_2, …`). Variables that
    * are already their own canonical twin are dropped, so a fully-screened problem gets an empty map (and a
    * pass-through proof). */
  private[clausification] def screeningRenaming(problem: Problem): Map[Variable, Variable] =
    val sequents: Seq[Sequent] = problem.hypotheses ++ problem.conjecture
    val free: Seq[Variable] = sequents.iterator
      .flatMap(s => s.left.iterator ++ s.right.iterator)
      .flatMap(_.freeVariables)
      .toSeq.distinct
      .sortBy(v => (v.id.name, v.id.no, v.sort.toString)) // sequent sides are Sets — order the traversal explicitly
    // Three namespaces, by what the symbol ultimately returns: an `Ind` variable is a clause variable, anything
    // returning `Prop` is a predicate, anything else returns `Ind` and is a function.
    val inds = free.filter(_.sort == Ind)
    val (preds, funs) = free.filterNot(_.sort == Ind).partition(v => resultSort(v.sort) == Prop)
    // Counters start at 1, so no screened name is a bare prefix. This is what keeps the predicate namespace
    // clear of `P` = `Identifier("P", 0)`, which is [[Clausification.schemaP]] itself: screening exists to move
    // input variables out of the way of the schemas the pipeline instantiates, so producing one would defeat it.
    def canonical(vs: Seq[Variable], prefix: String): Seq[(Variable, Variable)] =
      vs.zipWithIndex.map((v, i) => v -> Variable(Identifier(prefix, i + 1), v.sort))
    (canonical(inds, GeneratedNames.inputVar)
      ++ canonical(preds, GeneratedNames.inputPred)
      ++ canonical(funs, GeneratedNames.inputFun)).filter((v, w) => v != w).toMap

  /** The sort a symbol ultimately returns, reached by walking the arrows to the right: `Prop` for a predicate of
    * any arity (including a nullary one), `Ind` for a function or constant. Every sort is built from `Ind` and
    * `Prop`, so these are the only two outcomes. */
  private def resultSort(s: Sort): Sort = s match
    case Arrow(_, r) => resultSort(r)
    case other       => other

  private def applyTo(s: Sequent, m: Map[Variable, Expression]): Sequent =
    Sequent(s.left.map(substituteVariablesOpti(_, m)), s.right.map(substituteVariablesOpti(_, m)))
