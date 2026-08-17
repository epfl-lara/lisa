package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K
import lisa.automation.clausification.{Clausification, UncertifiedClausifier}

/** The adapter between the clausification package and the prover: the abstraction of non-first-order subterms,
  * the entry points [[prove]], [[proveOutcome]] and [[solveOutcome]], and the CASC setup [[cascSetup]].
  *
  * The prover is first-order over a flat term bank, so every maximal non-first-order subterm of a clause is
  * replaced by a fresh schematic function variable applied to its free variables, and its value recorded. The
  * search runs on the abstracted problem, but the proof is not: [[Reconstruction]] substitutes each value back
  * as it builds, so no fresh symbol appears in it and the imports can be the clausifier's own clauses.
  *
  * [[Bridge]] is the other half of the boundary and does the encoding: kernel clause sequents to internal
  * clauses and back. Everything here is above that, on the clausification side of it. */
object Clausal:

  /** A first-order abstraction state, threaded across all clauses of one problem so that identical
    * non-first-order subterms share a single schematic symbol. Stateful and single-threaded. */
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

    /** Replace every maximal non-first-order subterm of `e` by a fresh schematic function variable applied to
     *  its free variables, descending through the first-order skeleton. Every free variable of an abstracted
     *  subterm must be `Ind`-sorted, since that is what the fresh symbol's sort is built from. */
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

  private def headAndArgs(e: K.Expression): (K.Expression, List[K.Expression]) = Bridge.headAndArgs(e)

  private def rebuild(head: K.Expression, args: List[K.Expression]): K.Expression =
    args.foldLeft(head)((acc, a) => K.Application(acc, a))

  /** A first-order function symbol: a variable or constant whose sort is `Ind → … → Ind` (every argument
   *  place is `Ind`). Any head taking a non-`Ind` argument is excluded. */
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

  /** The clausal prover to hand to [[lisa.automation.clausification.CertifiedClausifier.certifyClausal]].
    *
    * Abstracts every non-first-order subterm to a fresh schematic function symbol `F(fv…)`, refutes
    * the resulting first-order clause set with [[Bridge]] (which reconstructs with each `F` inlined back to its
    * original subterm), and presents the proof's imports as the **original** clausifier clauses via a per-used-import
    * `Restate` into the working form [[Bridge]] uses. Conclusion is the empty sequent `⊢`, as the contract
    * requires. Purely first-order problems take the same path with an empty abstraction (no `F`, no discharge). */
  def prove(problem: Clausification.Problem): K.SCProof =
    proveOutcome(problem) match
      case Right(proof) => proof
      case Left(other)  => throw new RuntimeException(s"Clausal.prove: expected a refutation, got $other")

  /** Like [[prove]] but budgeted and total: returns `Right(proof)` on a refutation, or `Left(outcome)` for a
    * `Saturated`/`Timeout` [[Bridge.Outcome]] instead of throwing, so a benchmark can categorise the result.
    * `maxGiven`/`maxMillis` bound the underlying [[Bridge]] search. */
  def proveOutcome(problem: Clausification.Problem, maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue,
                   opts: SearchOptions = SearchOptions(), goal: Set[Int] = Set.empty,
                   onStats: Discount.LoopStats => Unit = _ => ()): Either[Bridge.Outcome, K.SCProof] =
    val p = prepare(problem)
    Bridge.solve(p.work, maxGiven, maxMillis, opts, symbolVars = p.symbolVars, discharge = p.abs.dischargeSubst, goal = goal, onStats = onStats) match
      case s: Bridge.Outcome.Success => Right(composeProof(s.reconstructKernelProof, p.orig))
      case other                     => Left(other)

  /** Present `base`, whose imports are the working-form abstracted clauses and whose conclusion is `∅ ⊢`, as a
    * proof over the **original** clausifier clauses `orig`: each import `base` actually used becomes a `Restate`
    * of the original clause it came from, and `base` itself becomes a subproof over those.
    *
    * The `Restate` is what bridges the two forms, which differ only propositionally (see [[toWorkingSequent]]). */
  private def composeProof(base: K.SCProof, orig: IndexedSeq[K.Sequent]): K.SCProof =
    // Slot of each working clause, first occurrence winning (duplicate inputs are equal sequents, so either
    // would do). Built once, so composition is linear rather than a structural `Sequent` scan per import.
    val slotOf = mutable.HashMap.empty[K.Sequent, Int]
    var k = 0
    while k < orig.length do { slotOf.getOrElseUpdate(toWorkingSequent(orig(k)), k); k += 1 }
    val steps = mutable.ArrayBuffer.empty[K.SCProofStep]
    val premises: Seq[Int] = base.imports.map { w =>
      // A miss means reconstruction imported a clause the clausifier never produced, impossible unless the
      // abstraction round-trip stops being exact; failing loudly beats silently referencing step 0.
      val i = slotOf.getOrElse(w, throw new IllegalStateException(
        s"reconstructed proof imports a clause absent from the clausifier's clause set: $w"))
      steps += K.Restate(w, -(i + 1))
      steps.length - 1
    }
    steps += K.SCSubproof(base, premises) // conclusion ∅ ⊢, over the working imports
    K.SCProof(steps.toIndexedSeq, orig) //   imports = the original clausifier clauses

  /** Pre-solve setup shared by [[proveOutcome]] and [[solveOutcome]]: abstract the clausifier clauses to a
   *  first-order working set, and collect the symbol-variables the solver must treat as symbols rather than
   *  clause variables: the abstraction functions `F` (explicit, incl. bare-nullary), plus every non-`Ind`-sorted
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

  /** Like [[proveOutcome]] but stops at the saturation verdict: returns the raw [[Bridge.Outcome]] **without**
    * reconstructing a kernel proof (no `reconstructKernelProof`, no import composition, no kernel check). For
    * benchmarking the prover's search in isolation from proof reconstruction. `onStats` still reports the loop
    * instrumentation. An [[Bridge.Outcome.Success]] means `□` was derived (a refutation); the proof DAG is left
    * unwalked. */
  def solveOutcome(problem: Clausification.Problem, maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue,
                   opts: SearchOptions = SearchOptions(), goal: Set[Int] = Set.empty,
                   onStats: Discount.LoopStats => Unit = _ => ()): Bridge.Outcome =
    val p = prepare(problem)
    Bridge.solve(p.work, maxGiven, maxMillis, opts, symbolVars = p.symbolVars, discharge = p.abs.dischargeSubst, goal = goal, onStats = onStats)

  /** The uncertified CASC clausal setup shared by the prover ([[CascProver]]) and its strategy benchmark
    * ([[bench.StrategyEvaluation]]): clausify `problem` (already SInE-pruned by the caller) with origin tags, append
    * the TPTP distinct-object distinctness axioms (origin `-1`), and derive the goal-clause index set, the
    * clauses coming from the negated conjecture, whose origin equals the hypothesis count. Returns the
    * origin-tagged clauses (which [[CascProver]] needs for proof printing), the flat clausal problem to solve,
    * and the goal indices. */
  def cascSetup(problem: Clausification.Problem, orthologic: Boolean): (IndexedSeq[(K.Sequent, Int)], Clausification.Problem, Set[Int]) =
    val clauses0 = UncertifiedClausifier.clausalFormWithOrigins(problem, orthologic = orthologic)
    val distinct = distinctObjectAxioms(clauses0.map(_._1))
    val clauses  = clauses0 ++ distinct.map(s => (s, -1))
    val clausal  = Clausification.Problem(clauses.map(_._1).toList, None)
    val goal     = clauses.iterator.zipWithIndex.collect { case ((_, origin), i) if origin == problem.hypotheses.size => i }.toSet
    (clauses, clausal, goal)

  /** The pairwise distinctness axioms for the TPTP distinct objects occurring in `clauses`. Such objects are
    * distinct by definition, so adding these is sound, and without them the encoding as uninterpreted
    * constants simply loses that information.
    *
    * They are returned in the ordinary clause shape, so they feed the prover and print like any other clause.
    * They carry no derivation, since they are added after clausification. */
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
