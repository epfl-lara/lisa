package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K
import lisa.automation.clausification.{Clausification, UncertifiedClausifier}

/**
 * The clausifier ↔ prover adapter: ε-abstraction, the `certifyClausal` prover contract, and the CASC
 * clausal setup.
 *
 * Lisa's certified clausifier (`lisa.automation.clausification`) Skolemizes with Hilbert ε-terms
 * `ε(λx.φ)`, which carry an embedded lambda and so are **not** first-order; our prover is first-order over a
 * flat term bank with no lambda support. Before a clause reaches the prover we therefore **abstract** every
 * maximal non-first-order subterm into a fresh schematic function *variable* applied to its free variables:
 * `ε(λx.φ(x, y)) ↦ F(y)` with `F := λy. ε(λx.φ(x, y))` recorded, making the clause purely first-order. The
 * prover and reconstruction work entirely in this abstracted world; a single `InstSchema` at the very end of
 * the proof instantiates every `F` back to its original expression (no per-step rewriting). Schematic
 * *variables* (not constants) are used precisely so the kernel's `InstSchema` can discharge them, the same
 * device the clausifier uses for its definitional naming atoms (`nm`).
 *
 * Besides the abstraction this file holds the prover adapter ([[prove]] / [[proveOutcome]] /
 * [[solveOutcome]]) and the CASC clausal setup ([[cascSetup]], [[distinctObjectAxioms]]).
 * `archive/Phase3.md` records the abstraction's original design, before either of those existed.
 */
object Clausal:

  /**
   * A first-order abstraction state, threaded across all clauses of one problem so that identical
   * non-first-order subterms share a single schematic symbol. Stateful and single-threaded.
   */
  final class Abstraction:
    // identical non-first-order subterms map to the same replacement `F(fv…)` (so `F` is one genuine function)
    private val replacement: mutable.Map[K.Expression, K.Expression] = mutable.Map.empty
    // discharge: each introduced schematic function variable `F` ↦ its closed value `λfv. e`
    private val values: mutable.Map[K.Variable, K.Expression] = mutable.Map.empty
    private var counter: Int = 0

    /** The substitution instantiating every introduced symbol back to its original expression (for the final
     *  `InstSchema`); empty iff nothing was abstracted. */
    def dischargeSubst: Map[K.Variable, K.Expression] = values.toMap

    /** Whether any non-first-order subterm was abstracted. */
    def isEmpty: Boolean = values.isEmpty

    /**
     * Abstract `e`: replace every **maximal** non-first-order `Ind`-subterm by a fresh schematic function
     * variable applied to its free variables. First-order skeleton (predicates, connectives, first-order
     * function applications) is descended into; the result is `e` with all such subterms replaced.
     *
     * '''Precondition:''' every free variable of an abstracted subterm is `Ind`-sorted, since that is what
     * [[abstractWhole]] builds the fresh symbol's `Ind → … → Ind` sort from; a higher-sorted one would be given
     * the wrong sort.
     */
    def apply(e: K.Expression): K.Expression =
      if e.sort == K.Ind then
        // a term position: descend through a first-order function head, else abstract the whole subterm
        val (h, args) = headAndArgs(e)
        if isFirstOrderFunction(h) then rebuild(h, args.map(apply))
        else abstractWhole(e)
      else
        e match // a formula / higher-sorted skeleton: recurse structurally, abstracting `Ind`-subterms within
          case K.Application(f, a) => K.Application(apply(f), apply(a))
          case K.Lambda(v, b)      => K.Lambda(v, apply(b))
          case _                   => e

    private def abstractWhole(e: K.Expression): K.Expression =
      replacement.getOrElseUpdate(
        e, {
          val fv: Seq[K.Variable] = e.freeVariables.toSeq.sortBy(v => (v.id.name, v.id.no))
          val fSort: K.Sort = fv.foldRight(K.Ind: K.Sort)((_, acc) => K.Ind -> acc)
          // counter goes in the identifier's `no` field, so `toString` is `abs`/`abs_1`/…, so at most one
          // `_` separator, which the kernel's `String → Identifier` round-trip requires.
          val f: K.Variable = K.Variable(K.Identifier(Clausification.GeneratedNames.epsAbs, counter), fSort)
          counter += 1
          values(f) = fv.foldRight(e)((v, body) => K.Lambda(v, body)) // F := λfv. e
          fv.foldLeft(f: K.Expression)((acc, v) => K.Application(acc, v)) // F(fv…)
        }
      )

  /** Decompose a curried application into head and arguments; see [[Bridge.headAndArgs]]. */
  private def headAndArgs(e: K.Expression): (K.Expression, List[K.Expression]) = Bridge.headAndArgs(e)

  private def rebuild(head: K.Expression, args: List[K.Expression]): K.Expression =
    args.foldLeft(head)((acc, a) => K.Application(acc, a))

  /** A first-order function symbol: a variable or constant whose sort is `Ind → … → Ind` (every argument
   *  place is `Ind`). Excludes `ε` (sort `(Ind → Prop) → Ind`) and any higher-order head. */
  private def isFirstOrderFunction(h: K.Expression): Boolean = h match
    case _: K.Variable | _: K.Constant => firstOrderSort(h.sort)
    case _                             => false

  private def firstOrderSort(s: K.Sort): Boolean = s match
    case K.Ind             => true
    case K.Arrow(K.Ind, r) => firstOrderSort(r)
    case _                 => false

  // ── The clausal-prover adapter for `CertifiedClausifier.certifyClausal` ──────────────────────────────────────

  /** Move any negative literal still written `¬A` on the right of a clause to the left as `A`, the form
   *  [[Bridge]] works in. Both clausifiers already emit that form, so this is the identity on their output;
   *  it is kept for clauses reaching the prover from elsewhere, and because the two forms are only
   *  propositionally equal, which costs a `Restate` to bridge rather than nothing at all. */
  def toWorkingSequent(s: K.Sequent): K.Sequent =
    val left = mutable.Set.from(s.left)
    val right = mutable.Set.empty[K.Expression]
    s.right.foreach {
      case K.Application(K.neg, a) => left += a
      case d                       => right += d
    }
    K.Sequent(left.toSet, right.toSet)

  /** Abstract every maximal non-first-order subterm in a clause's literals to a schematic function symbol,
   *  memoised across the whole problem via the shared `abs`. */
  private def abstractSequent(abs: Abstraction, s: K.Sequent): K.Sequent =
    K.Sequent(s.left.map(abs(_)), s.right.map(abs(_)))

  /**
   * The clausal prover to hand to [[lisa.automation.clausification.CertifiedClausifier.certifyClausal]].
   *
   * Abstracts every non-first-order subterm (ε-terms) to a fresh schematic function symbol `F(fv…)`, refutes
   * the resulting first-order clause set with [[Bridge]] (which reconstructs with each `F` inlined back to its
   * ε-term), and presents the proof's imports as the **original** clausifier clauses via a per-used-import
   * `Restate` into the working form [[Bridge]] uses. Conclusion is the empty sequent `⊢`, as the contract
   * requires. Purely first-order problems take the same path with an empty abstraction (no `F`, no discharge).
   */
  def prove(problem: Clausification.Problem): K.SCProof =
    proveOutcome(problem) match
      case Right(proof) => proof
      case Left(other)  => throw new RuntimeException(s"Clausal.prove: expected a refutation, got $other")

  /**
   * Like [[prove]] but budgeted and total: returns `Right(proof)` on a refutation, or `Left(outcome)` for a
   * `Saturated`/`Timeout` [[Bridge.Outcome]] instead of throwing, so a benchmark can categorise the result.
   * `maxGiven`/`maxMillis` bound the underlying [[Bridge]] search.
   */
  def proveOutcome(problem: Clausification.Problem, maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue,
                   opts: SearchOptions = SearchOptions(), goal: Set[Int] = Set.empty,
                   onStats: Discount.LoopStats => Unit = _ => ()): Either[Bridge.Outcome, K.SCProof] =
    val p = prepare(problem)
    Bridge.solve(p.work, maxGiven, maxMillis, opts, symbolVars = p.symbolVars, discharge = p.abs.dischargeSubst, goal = goal, onStats = onStats) match
      case s: Bridge.Outcome.Success =>
        val base: K.SCProof = s.reconstructKernelProof //              ε-bearing, imports = the working-form ε-clauses, ∅ ⊢
        val work0: IndexedSeq[K.Sequent] = p.orig.map(toWorkingSequent) // every clause in working form;
        //                                                                `base.imports` is the sub-list actually used
        // Slot of each working clause, first occurrence winning (as the `indexOf` this replaces did, since duplicate
        // input clauses are equal sequents, so either slot would do). Built once so composing the proof is linear
        // in the clause count; the per-import scan it replaces was O(|clauses| × |used imports|) with a full
        // `Sequent` structural comparison as its inner step, which bites on CASC-sized inputs.
        val slotOf = mutable.HashMap.empty[K.Sequent, Int]
        var k = 0
        while k < work0.length do { slotOf.getOrElseUpdate(work0(k), k); k += 1 }
        val steps = mutable.ArrayBuffer.empty[K.SCProofStep]
        val premises: Seq[Int] = base.imports.map { w => //             each used working import ← Restate of its original
          // A miss means reconstruction imported a clause the clausifier never produced, impossible unless the
          // ε-discharge round-trip stops being exact. Fail loudly: `indexOf` returned -1 here, which silently
          // became a reference to step 0.
          val i = slotOf.getOrElse(w, throw new IllegalStateException(
            s"reconstructed proof imports a clause absent from the clausifier's clause set: $w"))
          steps += K.Restate(w, -(i + 1))
          steps.length - 1
        }
        steps += K.SCSubproof(base, premises) //                       conclusion ∅ ⊢, over the working imports
        Right(K.SCProof(steps.toIndexedSeq, p.orig)) //                imports = original clausifier clauses
      case other => Left(other)

  /** Pre-solve setup shared by [[proveOutcome]] and [[solveOutcome]]: ε-abstract the clausifier clauses to a
   *  first-order working set, and collect the symbol-variables the solver must treat as symbols rather than
   *  clause variables: the ε-abstraction functions `F` (explicit, incl. bare-nullary), plus every non-`Ind`-sorted
   *  free variable (definitional naming atoms `nm…` and any Lisa predicate/function variable; clause
   *  variables are `Ind`). */
  private final case class Prepared(abs: Abstraction, orig: IndexedSeq[K.Sequent], work: IndexedSeq[K.Sequent], symbolVars: Set[K.Variable])
  private def prepare(problem: Clausification.Problem): Prepared =
    val abs = new Abstraction
    val orig: IndexedSeq[K.Sequent] = problem.imports //               clausifier clauses (contract import list)
    val absSeqs: IndexedSeq[K.Sequent] = orig.map(o => abstractSequent(abs, o))
    val work: IndexedSeq[K.Sequent] = absSeqs.map(toWorkingSequent)
    val symbolVars: Set[K.Variable] =
      abs.dischargeSubst.keySet ++
        problem.frozen ++ //                                            Skolem-function symbols from SkolemPhase: a
        //  NULLARY one is Ind-sorted so the `sort != Ind` filter below misses it; it must NOT be a clause variable.
        absSeqs.iterator.flatMap(s => (s.left ++ s.right).iterator.flatMap(_.freeVariables)).filter(_.sort != K.Ind).toSet
    Prepared(abs, orig, work, symbolVars)

  /**
   * Like [[proveOutcome]] but stops at the saturation verdict: returns the raw [[Bridge.Outcome]] **without**
   * reconstructing a kernel proof (no `reconstructKernelProof`, no import composition, no kernel check). For
   * benchmarking the prover's search in isolation from proof reconstruction. `onStats` still reports the loop
   * instrumentation. An [[Bridge.Outcome.Success]] means `□` was derived (a refutation); the proof DAG is left
   * unwalked.
   */
  def solveOutcome(problem: Clausification.Problem, maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue,
                   opts: SearchOptions = SearchOptions(), goal: Set[Int] = Set.empty,
                   onStats: Discount.LoopStats => Unit = _ => ()): Bridge.Outcome =
    val p = prepare(problem)
    Bridge.solve(p.work, maxGiven, maxMillis, opts, symbolVars = p.symbolVars, discharge = p.abs.dischargeSubst, goal = goal, onStats = onStats)

  /**
   * The uncertified CASC clausal setup shared by the prover ([[CascProver]]) and its strategy benchmark
   * ([[bench.StrategyEvaluation]]): clausify `problem` (already SInE-pruned by the caller) with origin tags, append
   * the TPTP distinct-object distinctness axioms (origin `-1`), and derive the goal-clause index set, the
   * clauses coming from the negated conjecture, whose origin equals the hypothesis count. Returns the
   * origin-tagged clauses (which [[CascProver]] needs for proof printing), the flat clausal problem to solve,
   * and the goal indices.
   */
  def cascSetup(problem: Clausification.Problem, orthologic: Boolean): (IndexedSeq[(K.Sequent, Int)], Clausification.Problem, Set[Int]) =
    val clauses0 = UncertifiedClausifier.clausalFormWithOrigins(problem, orthologic = orthologic)
    val distinct = distinctObjectAxioms(clauses0.map(_._1))
    val clauses  = clauses0 ++ distinct.map(s => (s, -1))
    val clausal  = Clausification.Problem(clauses.map(_._1).toList, None)
    val goal     = clauses.iterator.zipWithIndex.collect { case ((_, origin), i) if origin == problem.hypotheses.size => i }.toSet
    (clauses, clausal, goal)

  /**
   * The pairwise **distinctness axioms** for TPTP distinct objects: `$da ≠ $db` for every two different
   * distinct-object constants (`$d`-prefixed, introduced by [[lisa.tptp.KernelParser]] Fix B) occurring in
   * `clauses`. TPTP distinct objects are pairwise distinct *by definition*, so these are the intended-semantics
   * axioms, sound to add, and they let the prover exploit object distinctness that the uninterpreted-constant
   * encoding otherwise misses (without them the treatment is merely incomplete).
   *
   * Returned in the same clause shape as everything else, a negative literal being its atom on the left, so
   * `$da = $db ⊢`, hence they feed the solver and print identically to ordinary clauses. Added on the
   * **solve** path (after clausification, before solving); they carry no derivation, so a CASC caller prints
   * them with `inference(distinct, …, [])`.
   */
  def distinctObjectAxioms(clauses: Seq[K.Sequent]): IndexedSeq[K.Sequent] =
    val objs = mutable.LinkedHashSet.empty[K.Constant]
    def scan(e: K.Expression): Unit = e match
      case K.Application(f, a) => scan(f); scan(a)
      case K.Lambda(_, b)      => scan(b)
      case c: K.Constant       => if c.id.name.startsWith("$d") then objs += c
      case _                   => ()
    clauses.foreach(s => { s.left.foreach(scan); s.right.foreach(scan) })
    val os = objs.toIndexedSeq
    (for i <- os.indices; j <- (i + 1) until os.size
     yield K.Sequent(Set(K.equality(os(i))(os(j))), Set.empty)).toIndexedSeq
