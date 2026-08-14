package lisa.automation.clausification
import lisa.utils.K
import lisa.utils.K.{_, given}

/** Certified clausification for Lisa, following the SC-TPTP pipeline structure.
  *
  * The reusable proof IR (`ClausificationProof`, `ClausificationSubproof`,
  * conversion to `SCProof`, etc.) lives in [[ProofIR]] (same package). This module hosts the
  * clausification-specific certification pipeline. */
object Clausification {

  /**
   * Where every fresh name the clausifier and proof
   * reconstruction generate is defined. Every prefix is short and purely alphabetic, and the counter lives in the
   * identifier's `no` field.
   */
  private[automation] object GeneratedNames:
    // Certified clausification pipeline (kernel schema vars, naming atoms, substitution-context holes):
    val skolemFun      = "esk"  // SkolemPhase:            Skolem ε-function schema var
    val skolemBound    = "u"    // SkolemPhase:            fresh bound-var base (freshId) inside a Skolem-term
    val namingAtom     = "nm"   // both clausifiers:       the definitional-naming atom (via NamingSupport.freshNamingAtom)
    val clauseVar      = "w"    // both clausifiers:       the fresh variable each stripped ∀ is instantiated with
    val epsAbs         = "epsi" // Clausal:                ε-abstraction function schema var lifting ε-terms
    val etaVar         = "etaZ" // Clausification:         fresh var for η-expansion, avoiding capture when `∀ P` becomes `∀(λz. P(z))`
    val uncertifiedSkolem = "sk"// UncertifiedClausifier:  Skolem function Constant (not the certified `esk`)
    // Input screening ([[ScreenPhase]]): the three namespaces every free input variable is renamed into,
    // by the sort a symbol ultimately returns. Screening counters start at 1.
    val inputVar       = "v"    // Ind:                    the clause variables of the input
    val inputPred      = "P"    // Ind → … → Ind → Prop:   the input's uninterpreted predicate symbols
    val inputFun       = "F"    // Ind → … → Ind → Ind:    the input's uninterpreted function symbols
    // Proof reconstruction (superposition DAG → kernel, [[lisa.automation.superposition.Reconstruction]]):
    val reconClauseVar = "cv"   // per-clause canonical clause variable (reused across clauses; instantiated independently)
    val hole           = "HOLE" // for specifying rewrite positions in proofs.

  // ── Clause-count estimation (shared by the uncertified [[UncertifiedClausifier]] and its certified twin
  //    [[CertifiedClausifier]], whose naming decisions must agree bit-for-bit) ──────────────────
  //
  /** Positive/negative CNF clause-count estimate of a subformula, each saturated at [[clauseCountCap]]. We
   *  only ever compare it against a naming `threshold`, so the exact count past the cap is irrelevant. */
  private[clausification] final case class Est(pos: Long, neg: Long)
  private[clausification] val atomEst: Est = Est(1, 1)
  private[clausification] val clauseCountCap: Long = 1L << 20
  private[clausification] inline def capMul(a: Long, b: Long): Long = math.min(clauseCountCap, a * b)
  private[clausification] inline def capAdd(a: Long, b: Long): Long = math.min(clauseCountCap, a + b)

  /** How an estimate combines at each connective, in one place so the two paths cannot drift. `implies` is
    * defined through `or`/`neg` because the uncertified path reaches it that way, rewriting `g ⇒ h` first. */
  private[clausification] object Est:
    def and(a: Est, b: Est): Est     = Est(capAdd(a.pos, b.pos), capMul(a.neg, b.neg))
    def or(a: Est, b: Est): Est      = Est(capMul(a.pos, b.pos), capAdd(a.neg, b.neg))
    def neg(a: Est): Est             = Est(a.neg, a.pos)
    def implies(a: Est, b: Est): Est = or(neg(a), b)
    def iff(a: Est, b: Est): Est     = Est(capAdd(capMul(a.pos, b.neg), capMul(a.neg, b.pos)),
                                           capAdd(capMul(a.pos, b.pos), capMul(a.neg, b.neg)))
    /** Total clause count, the size the `⇔` naming loop compares its two sides by. */
    def size(a: Est): Long = capAdd(a.pos, a.neg)

  // ─────────────────────────────────────────────────────────────────────────────
  // Library theorem statements used by the certified bridges. They are imports in the resulting kernel proof.
  // ─────────────────────────────────────────────────────────────────────────────

  /** The schema variable appearing in the library statement: predicate `P` (`Ind → Prop`). */
  private[clausification] val schemaP: Variable = Variable(Identifier("P", 0), Ind >>: Prop)
  private val vX: Variable = Variable(Identifier("x", 0), Ind)

  /** Statement of `lisa.maths.Quantifiers.existsEpsilonIff`: `() ⊢ ∃(λx.P(x)) ⇔ P(ε(λx.P(x)))`. */
  val existsEpsilonIffStatement: Sequent = () |- (exists(vX, schemaP(vX)) <=> schemaP(epsilon(vX, schemaP(vX))))

  /** Library imports threaded to every clausification proof, in fixed order. */
  val libImports: IndexedSeq[Sequent] = IndexedSeq(existsEpsilonIffStatement)
  private[clausification] val libExistsEpsilonIffIdx: Int = 0

  // ─────────────────────────────────────────────────────────────────────────────
  // Data types
  // ─────────────────────────────────────────────────────────────────────────────

  /** An input to a solver is a conjecture and a set of hypothesis.
    * Problems are transformed by the different stages of the clausification process into problems closer to a clausal form.
    * After the [[NegatedPhase]], the conjecture is None. `frozen` is the set of variables that are fixed
    * and non-instantiable or quantifiable (e.g. skolem symbols).
    */
  case class Problem(hypotheses: Seq[Sequent], conjecture: Option[Sequent], frozen: Set[Variable] = Set.empty) {
    /** User-facing imports: just the hypotheses. Library imports are threaded
      * separately via [[Clausification.libImports]] and appear at the end of the
      * produced kernel proof's imports. */
    def imports: IndexedSeq[Sequent] = hypotheses.toIndexedSeq

    def hypIndex(i: Int): Int = -(i + 1)
  }
  /** Total node count of a kernel expression (variables/constants/applications/lambdas). */
  def formulaSize(e: Expression): Int = e match
    case Application(f, a) => 1 + formulaSize(f) + formulaSize(a)
    case Lambda(_, body)   => 1 + formulaSize(body)
    case _                 => 1

  /** Sum of formula sizes across all sequents in a problem (LHS + RHS, hypotheses + conjecture). */
  def problemSize(p: Problem): Int =
    def seqSize(s: Sequent): Int = s.left.toSeq.map(formulaSize).sum + s.right.toSeq.map(formulaSize).sum
    p.hypotheses.map(seqSize).sum + p.conjecture.fold(0)(seqSize)

  private[clausification] def singleRightFormula(sequent: Sequent, what: String): Expression = {
    require(sequent.left.isEmpty, s"$what must have empty left-hand side, got ${sequent.repr}")
    require(sequent.right.size == 1, s"$what must have a single formula on the right-hand side, got ${sequent.repr}")
    sequent.right.head
  }

  /** `base`, which must conclude `() ⊢ body`, wrapped in one `RightForall` per variable, innermost first, so the
    * result concludes `() ⊢ ∀x̄. body`. The shared tail of the two closed proofs that discharge a definition,
    * [[NamingSupport.proveQuantifiedReflIff]] and [[SkolemPhase.proveQuantifiedReflEq]]. */
  private[clausification] def quantifyProof(base: IndexedSeq[SCProofStep], body: Expression, vars: Seq[Variable]): SCProof =
    val n = vars.size
    val steps = new Array[SCProofStep](base.size + n)
    base.copyToArray(steps)
    var current = body
    var ref = base.size - 1
    for k <- 0 until n do
      val v = vars(n - 1 - k)
      val next = forall(v, current)
      steps(base.size + k) = RightForall(() |- next, ref, current, v)
      ref = base.size + k
      current = next
    SCProof(steps.toIndexedSeq, IndexedSeq.empty)

  private[clausification] def sameImportList(left: Seq[Sequent], right: Seq[Sequent]): Boolean =
    left.size == right.size && left.zip(right).forall((l, r) => l == r || isSameSequent(l, r))

  /** Negative kernel reference (`-(idx+1)` form) for a library import at `libIdx`
    * within an outer imports list whose first `nonLibSize` entries are non-library
    * imports and last [[libImports.size]] entries are the library imports. */
  private[clausification] def libRef(nonLibSize: Int, libIdx: Int): Int = -(nonLibSize + libIdx + 1)

  /** References into outer imports for the library imports, in their fixed order. */
  private[clausification] def libRefs(nonLibSize: Int): IndexedSeq[Int] = libImports.indices.map(libRef(nonLibSize, _)).toIndexedSeq

  private[clausification] type ClausificationProver = Problem => ClausificationProof

  /**
   * Expand η-reduced quantifier bodies: rewrite `∀(f)` / `∃(f)` to
   * `∀(λz. f(z))` / `∃(λz. f(z))`. The kernel's `betaNormalForm` η-reduces `λy. p(x, y)` to `p(x)`, so a
   * `∀y. p(x, y)` can come back as `∀(p(x))`, which the [[Forall]]/[[Exists]] extractors (they require an
   * explicit `Lambda`) do not recognise, leaving the quantifier stranded as an opaque atom in the clause.
   * Applying this after every `betaNormalForm` restores the `Lambda` form so the phases can strip/skolemize it.
   *
   * Rule for new code: re-apply after any `betaNormalForm` or kernel normal-form round-trip.
   * ε-terms are left untouched.
   */
  private[automation] def etaExpandQuantifiers(e: Expression): Expression =
    def freshEtaVar(free: Set[Variable]): Variable =
      var n = 0
      var z = Variable(Identifier(GeneratedNames.etaVar, n), Ind)
      while free.contains(z) do { n += 1; z = Variable(Identifier(GeneratedNames.etaVar, n), Ind) }
      z
    def wrapBinder(binder: Expression, body: Expression): Expression = body match
      case Lambda(v, inner) => binder(Lambda(v, etaExpandQuantifiers(inner)))
      case f =>
        val ef = etaExpandQuantifiers(f)
        val z  = freshEtaVar(ef.freeVariables)
        binder(Lambda(z, ef(z)))
    e match
      case Application(`forall`, body)  => wrapBinder(forall, body)
      case Application(`exists`, body)  => wrapBinder(exists, body)
      case Application(`epsilon`, _)    => e // leave Skolem ε-terms exactly as β-normalisation produced them
      case Application(f, a)            => Application(etaExpandQuantifiers(f), etaExpandQuantifiers(a))
      case Lambda(v, b)                 => Lambda(v, etaExpandQuantifiers(b))
      case _                            => e

  /** Negative kernel references for `n` consecutive imports starting at zero-based `start`. */
  private[clausification] def negRange(start: Int, n: Int): IndexedSeq[Int] =
    (start until start + n).map(i => -(i + 1)).toIndexedSeq

  /**
   * The outer **discharge** loop shared by [[SkolemPhase.certifySkolem]] and
   * [[CertifiedClausifier.certifyNaming]]. `csub` carries `count` fresh-symbol definitions as
   * assumptions on its antecedent; this discharges them **latest-first**: for each `j = count-1 … 0`,
   * instantiate the fresh symbol to its value (which turns assumption `j` into a reflexive formula), prove that
   * reflexive formula, and `Cut` it away. `perStep(j)` supplies the three things that differ between the two
   * callers: the schema substitution `F := value`, the assumption formula being discharged (`oldLhs`, present on
   * `csub`'s antecedent), and the closed proof of its reflexive instance `substituteVariablesOpti(oldLhs, subst)`.
   *
   * Precondition: every `perStep` substitution must leave `csub.bot.right` unchanged, since that
   * succedent is carried across the whole `InstSchema`/`Cut` chain as written. This is vacuous for both callers, whose
   * subproof concludes `⊢`.
   */
  private[clausification] def dischargeAssumptionsLatestFirst(
      csub: ClausificationSubproof,
      count: Int,
      outerImports: IndexedSeq[Sequent],
      perStep: Int => (Map[Variable, Expression], Expression, SCProof)): ClausificationProof =
    val outerSteps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    outerSteps += csub
    val rhs = csub.bot.right
    val mutableLhs = scala.collection.mutable.HashSet.from(csub.bot.left)
    var prevBotRef = 0
    for j <- (count - 1) to 0 by -1 do
      val (schemaSubst, oldLhs, reflProof) = perStep(j)
      val reflexive = substituteVariablesOpti(oldLhs, schemaSubst) // instantiating the fresh symbol makes it reflexive
      mutableLhs -= oldLhs; mutableLhs += reflexive
      outerSteps += InstSchema(Sequent(mutableLhs.toSet, rhs), prevBotRef, schemaSubst)
      val instRef = outerSteps.size - 1
      outerSteps += SCSubproof(reflProof, IndexedSeq.empty)
      val reflRef = outerSteps.size - 1
      mutableLhs -= reflexive
      outerSteps += Cut(Sequent(mutableLhs.toSet, rhs), reflRef, instRef, reflexive)
      prevBotRef = outerSteps.size - 1
    ClausificationProof(outerSteps.toIndexedSeq, outerImports)

  /** Heap ceiling for the safety valve below: 90% of max. `maxMemory` is fixed for the life of the JVM, so
    * it is read once rather than on every poll. */
  private val heapCeiling: Long = (Runtime.getRuntime.maxMemory / 10) * 9

  /** Counts calls to [[checkInterrupted]] so the heap is polled only every [[heapPollInterval]]th one. Not
    * synchronised: it is a heuristic trigger, and a lost increment under concurrent use only shifts *when*
    * the poll happens, never whether the valve is correct. */
  private var interruptPolls: Int = 0
  private inline val heapPollInterval = 256

  /** Cooperative cancellation hook: throw `InterruptedException` if the
    * current thread has been interrupted, OR if the JVM is dangerously close
    * to OOM (used heap > 90% of max).  The latter is a safety valve so a
    * runaway problem (e.g. an exponential blow-up that allocates faster than
    * `Thread.interrupted()` can be polled) cannot crash the whole bench.
    *
    * The interrupt flag is checked every call, being a plain field read. The heap is not: `totalMemory` and
    * `freeMemory` are native calls, and this runs per axiom, per naming step and per distribute step, of
    * which there are thousands. Polling every 256th call keeps the valve responsive (a step allocates a
    * bounded amount, so the heap cannot run far between polls) at 1/256th of the cost. */
  private[clausification] inline def checkInterrupted(): Unit = {
    if (Thread.interrupted()) throw new InterruptedException("Clausification cancelled")
    interruptPolls += 1
    if ((interruptPolls & (heapPollInterval - 1)) == 0) checkHeadroom()
  }

  /** The out-of-line half of [[checkInterrupted]]: the part worth paying for only occasionally. */
  private def checkHeadroom(): Unit = {
    val rt = Runtime.getRuntime
    val used = rt.totalMemory() - rt.freeMemory()
    if (used > heapCeiling)
      throw new InterruptedException(s"Memory pressure: heap ${used / (1024*1024)}MB / max ${rt.maxMemory() / (1024*1024)}MB")
  }

  // The top-level certified clausification pipeline lives in [[CertifiedClausifier.certifyClausal]] (it adds a
  // threshold-gated naming pass before NNF to cap CNF blow-up). The per-phase certifiers and the shared helpers
  // (libImports, clausificationProofToSCProof, ClausificationProof) below are what it composes.

  // ─────────────────────────────────────────────────────────────────────────────
  // Pure (uncertified) formula transformations  (helpers for the pipeline)
  // ─────────────────────────────────────────────────────────────────────────────

  /** Like [[lisa.kernel.fol.Syntax.substituteVariables]] but avoids redundant work and
    * heap allocation when parts of the expression tree are unaffected by the substitution:
    *  - `m.isEmpty` guard: if the substitution is empty, returns `e` unchanged (same reference).
    *  - Lambda stripping: when a Lambda binder removes the last key from `m`, the body subtree
    *    is returned as-is without recursion.
    *  - Smart constructors: the result of an Application or Lambda is the original expression `e`
    *    (same reference) when both sub-results are reference-equal to the originals. This avoids
    *    allocating new nodes for unchanged subtrees and lets parent calls short-circuit too.
    *
    * The function is observationally identical to the kernel version on well-sorted inputs.
    */
  private[clausification] def substituteVariablesOpti(e: Expression, m: Map[Variable, Expression]): Expression =
    if (m.isEmpty) e
    else
      // Pre-compute the free variables of all substitution values once at the top level.
      // This set is passed down so that Lambda cases don't recompute it from scratch for
      // every nested binder (which would be O(depth × |m| × value_size) total).
      val fvOfValues: Set[Variable] = m.values.flatMap(_.freeVariables).toSet
      substituteVariablesOptiRec(e, m, fvOfValues)

  private[clausification] def substituteVariablesOptiRec(e: Expression, m: Map[Variable, Expression], fvOfValues: Set[Variable]): Expression =
    e match
      case v: Variable => m.getOrElse(v, v)
      case _: Constant => e
      case Application(f, arg) =>
        val newF   = substituteVariablesOptiRec(f, m, fvOfValues)
        val newArg = substituteVariablesOptiRec(arg, m, fvOfValues)
        if (newF eq f) && (newArg eq arg) then e else Application(newF, newArg)
      case Lambda(v, t) =>
        val newM = m - v
        if (newM.isEmpty) e
        else
          // Remove v from fvOfValues only if v was a key (its value may have had v free).
          // In practice fvOfValues is a conservative over-approximation: we recompute it
          // precisely only when we need to check for capture.
          if fvOfValues.contains(v) then
            // Potential capture: recompute precisely for this binder.
            val newFv = newM.values.flatMap(_.freeVariables).toSet
            if newFv.contains(v) then
              val newV = Variable(freshId(newFv.view.map(_.id) ++ newM.keys.view.map(_.id), v.id), v.sort)
              Lambda(newV, substituteVariablesOptiRec(t, newM + (v -> newV), newFv + newV))
            else
              val newT = substituteVariablesOptiRec(t, newM, newFv)
              if (newT eq t) e else Lambda(v, newT)
          else
            val newT = substituteVariablesOptiRec(t, newM, fvOfValues)
            if (newT eq t) e else Lambda(v, newT)

  // ─────────────────────────────────────────────────────────────────────────────
  // Counter helper
  // ─────────────────────────────────────────────────────────────────────────────

  class Counter(var value: Int = 0) {
    def next(): Int = { val v = value; value += 1; v }
  }
}
