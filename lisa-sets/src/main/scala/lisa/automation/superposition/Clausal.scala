package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K
import lisa.automation.clausification.Clausification
import lisa.automation.Problem

import Core.*
import lisa.automation.superposition.ordering.*

/** Everything between [[Prover]] and the saturation engine: the encoding of kernel sequents as internal
  * clauses and back, the abstraction of non-first-order subterms, and the clausal-level entry points
  * [[solve]] and [[prove]], which [[Prover]] calls once its own phases have produced a clausal problem.
  * [[refute]] beneath them is the engine boundary: a clause set in, a verdict out.
  *
  * A clause is a kernel sequent: `a₁, …, aₘ ⊢ b₁, …, bₙ` is `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ`, so the left side
  * carries the negative literals and the empty sequent is the empty clause.
  *
  * The prover is first-order over a flat term bank, so every maximal non-first-order subterm of a clause is
  * replaced by a fresh schematic function variable applied to its free variables, and its value recorded. The
  * search runs on the abstracted problem, but the proof is not: [[Reconstruction]] substitutes each value back
  * as it builds, so no fresh symbol appears in it and the imports can be the clausifier's own clauses. */
object Clausal:

  /** The result of a [[solve]] run: a [[Outcome.Success]] (the empty clause `□` was derived) carrying
    * everything needed to reconstruct a kernel proof, [[Outcome.Saturated]] (the passive set was
    * exhausted without `□`, so the clause set is satisfiable, a genuine decision), or [[Outcome.Timeout]]
    * (a budget was hit before deciding, so the set's status is unknown). */
  sealed trait Outcome:
    def refuted: Boolean = this match
      case _: Outcome.Success => true
      case Outcome.Saturated | Outcome.Timeout => false

  object Outcome:
    /** A refutation. Holds the empty clause `empty` and the run's [[TermBank]] plus the per-input-clause
      * variable maps (`inputs`), the context [[reconstructKernelProof]] needs to rebuild the proof. */
    final case class Success(
        empty: Clause,
        bank: TermBank,
        inputs: collection.Map[Int, Reconstruction.InputInfo],
        schematicIds: Set[K.Identifier] = Set.empty,
        discharge: Map[K.Variable, K.Expression] = Map.empty) extends Outcome:
      /** Reconstruct a kernel [[lisa.utils.K.SCProof]] from this refutation: its imports are the input
        * clause-sequents and its conclusion is the empty sequent `⊢`. See [[Reconstruction]]. */
      def reconstructKernelProof: K.SCProof = Reconstruction.reconstruct(empty, bank, inputs, schematicIds, discharge)

    /** The passive set was exhausted without deriving `□`: the clause set is satisfiable (a decision). */
    case object Saturated extends Outcome

    /** A budget, either the `maxGiven` given-clause count or the `maxMillis` wall-clock limit, was hit before
     *  the search could decide. */
    case object Timeout extends Outcome

  /**
   * Run the saturation **once** on a clause set (kernel sequents `left ⊢ right` = the clause
   * `¬left ∨ right`). Builds a fresh bank + complete selector, converts each sequent in that bank, and
   * saturates within the given-clause and wall-clock budgets `opts` carries. Returns
   * [[Outcome.Success]] with the empty clause (and the context to reconstruct it) iff `□` is derived,
   * else [[Outcome.Saturated]] (passive exhausted) or [[Outcome.Timeout]] (budget hit). The per-input
   * variable maps are always recorded so a `Success` can be reconstructed later (cheap: O(input size);
   * the proof DAG itself is only walked by [[Outcome.Success.reconstructKernelProof]]).
   *
   * @param sequents   the clause set, one sequent per clause.
   * @param opts       every search knob and both budgets, in one value; see [[SearchOptions]].
   * @param symbolVars schematic symbol variables: kernel `Variable`s to be treated as **symbols** by the prover
   *                   rather than as clause variables, and rebuilt as variables in reconstruction.
   *                   Empty for pure first order clausal input.
   * @param discharge  abstraction discharge: each symbol `F` ↦ its closed value `λfv. e`. When non-empty,
   *                   reconstruction inlines `F` back to `e`, so the proof carries the original subterms.
   * @param goal       indices (into `sequents`) of the goal input clauses, the negated conjecture, for
   *                   goal-directed clause selection. Goal-ness propagates through inferences; empty means no
   *                   goal bias, as for a conjecture-free problem.
   */
  def refute(
      sequents: Iterable[K.Sequent],
      opts: SearchOptions = SearchOptions(),
      symbolVars: Set[K.Variable] = Set.empty,
      discharge: Map[K.Variable, K.Expression] = Map.empty,
      goal: Set[Int] = Set.empty): Outcome =
    val sig: Signature = new Signature(opts.weightScheme.weightOf)
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)
    val inputs = mutable.Map.empty[Int, Reconstruction.InputInfo]
    val clauses: Seq[Clause] = sequents.iterator.zipWithIndex.map { (s, i) =>
      val vars = mutable.HashMap.empty[K.Variable, Int]
      val c = clauseOfSequent(bank, s, vars, symbolVars, goalInput = goal.contains(i))
      inputs(c.id) = (s, vars.iterator.map((kv, n) => n -> kv).toMap)
      c
    }.toSeq
    // Generate the KBO precedence from the fully-interned signature. This is the one time the ordering is definitely fixed.
    Precedence.assign(sig, bank, clauses, opts.precedenceScheme)
    // Sanity check that the given order is admissible
    val inadmissible: Option[String] = bank.order.kbo.checkAdmissibility()
    assert(inadmissible.isEmpty, s"KBO is not admissible under this configuration: ${inadmissible.getOrElse("")}")
    bank.selector = LiteralSelection.selector(opts.selection, bank)
    // Equality inferences can fire only if the input contains `=`
    val hasEquality: Boolean = clauses.exists(c => c.literals.exists(l => bank.isEquality(l)))
    val schematicIds: Set[K.Identifier] = symbolVars.map(_.id)
    val discount = new Discount(bank, trail, clauses, opts.copy(equality = opts.equality && hasEquality))
    val result = discount.saturate()
    opts.onStats(discount.loopStats)
    result match
      case Discount.Result.Refutation(empty) => Outcome.Success(empty, bank, inputs, schematicIds, discharge)
      case Discount.Result.Saturated => Outcome.Saturated
      case Discount.Result.Unknown => Outcome.Timeout

  // ── Kernel formulas to internal clauses ───────────────────────────────────────────────────────────────
  //
  // Symbols are interned into the shared signature by their whole identifier string, not by `id.name`: the
  // kernel keeps a trailing numeric suffix in the separate counter field, so `e_1` and `e_2` share the name
  // `e` and keying on it alone would collapse them into one symbol. Each clause numbers its own variables
  // from zero, since clause variables are independent.

  /** Convert a kernel sequent (`left ⊢ right` = the clause `¬left ∨ right`) to an internal clause, threading a
   *  caller-owned variable map (kernel variable → internal number) for reconstruction and the set of `symbolVars`
   *  (schematic variables treated as predicate/function symbols, not variables). */
  private def clauseOfSequent(bank: TermBank, seq: K.Sequent, vars: mutable.HashMap[K.Variable, Int], symbolVars: Set[K.Variable], goalInput: Boolean = false): Clause =
    val lits: List[Literal] =
      seq.left.toList.map(f => literal(bank, vars, f, positive = false, symbolVars)) :::
        seq.right.toList.map(f => literal(bank, vars, f, positive = true, symbolVars))
    bank.mkClause(lits.toArray, goalInput = goalInput)

  /** Convert one literal: peel a leading `¬` (flipping polarity), then build the atom. */
  private def literal(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], f: K.Expression, positive: Boolean, symbolVars: Set[K.Variable]): Literal =
    f match
      case K.Application(n, inner) if n == K.neg => literal(bank, vars, inner, !positive, symbolVars)
      case _ => bank.mkLiteral(atomTerm(bank, vars, f, symbolVars), positive)

  /** Build the internal atom term for a predicate application: the head must be a predicate constant, or a
   *  schematic **predicate** variable listed in `symbolVars` (a clausifier naming atom `nm…`, or a Lisa
   *  predicate variable), interned as an (uninterpreted) predicate symbol. */
  private def atomTerm(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], f: K.Expression, symbolVars: Set[K.Variable]): Term =
    val (head, args) = headAndArgs(f)
    def app(sym: Symbol): Term = bank.mkApp(sym, args.iterator.map(a => term(bank, vars, a, symbolVars)).toArray)
    head match
      case c: K.Constant                           => app(bank.signature.intern(c.id.name, c.id.no, args.size, isPredicate = true))
      case v: K.Variable if symbolVars.contains(v) => app(bank.signature.intern(v.id.name, v.id.no, args.size, isPredicate = true))
      case other =>
        throw IllegalArgumentException(s"not a pure clause: literal head is not a predicate constant or symbol variable: $other")

  /** Build an internal term: a clause variable (renumbered per clause), a function/constant application, or a
   *  schematic **function** variable in `symbolVars` (a [[Clausal]] abstraction function `F`, or a Lisa function
   *  variable), interned as a function symbol (applied or bare-nullary) rather than treated as a clause variable. */
  private def term(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], t: K.Expression, symbolVars: Set[K.Variable]): Term =
    t match
      case v: K.Variable if symbolVars.contains(v) => // bare nullary function symbol
        bank.mkConst(bank.signature.intern(v.id.name, v.id.no, 0, isPredicate = false))
      case v: K.Variable => bank.mkVar(Core.Variable(vars.getOrElseUpdate(v, vars.size)))
      case _ =>
        val (head, args) = headAndArgs(t)
        val sym: Symbol = head match
          case c: K.Constant => bank.signature.intern(c.id.name, c.id.no, args.size, isPredicate = false)
          case v: K.Variable if symbolVars.contains(v) => // applied function symbol `F(fv…)`
            bank.signature.intern(v.id.name, v.id.no, args.size, isPredicate = false)
          case other =>
            throw IllegalArgumentException(s"not first-order: term head is not a constant (applied variable?): $other")
        bank.mkApp(sym, args.iterator.map(a => term(bank, vars, a, symbolVars)).toArray)

  /** Decompose a curried kernel application `f(a₁)…(aₙ)` into its head `f` and argument list `[a₁, …, aₙ]`.
    * Shared with [[Clausal]] and [[CascProver]], which each carried an identical private copy.
    *
    * Peels the spine into an accumulator, so the arguments arrive in order without appending to the tail of a
    * list per argument: the natural spelling of this is a recursion returning `as :+ arg`, which copies the whole
    * list at every step. Arities are small, but this runs over every term of every input clause. */
  private[superposition] def headAndArgs(e: K.Expression): (K.Expression, List[K.Expression]) =
    var head: K.Expression = e
    var args: List[K.Expression] = Nil
    var peeling = true
    while peeling do
      head match
        // The outermost application peels first, so the arguments come off last-to-first; prepending each puts
        // them back in source order without a copy.
        case K.Application(f, arg) => args = arg :: args; head = f
        case _                     => peeling = false
    (head, args)


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
   *  [[Clausal]] works in. Both clausifiers already emit that form, so this is the identity on their output;
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

  /** A kernel proof of `∅ ⊢` from `problem`'s clauses, taken as imports in order, or `Left(outcome)` when the
    * search saturates or runs out of budget. */
  def prove(problem: Problem, opts: SearchOptions = SearchOptions(),
                   goal: Set[Int] = Set.empty): Either[Clausal.Outcome, K.SCProof] =
    val p = prepare(problem)
    Clausal.refute(p.work, opts, symbolVars = p.symbolVars, discharge = p.abs.dischargeSubst, goal = goal) match
      case s: Clausal.Outcome.Success => Right(composeProof(s.reconstructKernelProof, p.orig))
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

  /** Pre-solve setup shared by [[prove]] and [[solve]]: abstract the clausifier clauses to a
   *  first-order working set, and collect the symbol-variables the solver must treat as symbols rather than
   *  clause variables: the abstraction functions `F` (explicit, incl. bare-nullary), plus every non-`Ind`-sorted
   *  free variable (definitional naming atoms `nm…` and any Lisa predicate/function variable; clause
   *  variables are `Ind`). */
  private final case class Prepared(abs: Abstraction, orig: IndexedSeq[K.Sequent], work: IndexedSeq[K.Sequent], symbolVars: Set[K.Variable])
  private def prepare(problem: Problem): Prepared =
    val abs = new Abstraction
    val orig: IndexedSeq[K.Sequent] = problem.imports //               clausifier clauses (contract import list)
    val absSeqs: IndexedSeq[K.Sequent] = orig.map(o => abstractSequent(abs, o))
    val work: IndexedSeq[K.Sequent] = absSeqs.map(toWorkingSequent)
    val symbolVars: Set[K.Variable] =
      abs.dischargeSubst.keySet ++
        problem.frozen ++ //                                            Skolem-function symbols from SkolemPhase: a
        //  NULLARY one is Ind-sorted so the `sort != Ind` filter below misses it; it must NOT be a clause variable.
        absSeqs.iterator.flatMap(s => s.left.iterator ++ s.right.iterator).flatMap(_.freeVariables).filter(_.sort != K.Ind)
    Prepared(abs, orig, work, symbolVars)

  /** Like [[prove]] but stops at the verdict: no `reconstructKernelProof`, no import composition, no kernel
    * check, so a [[Clausal.Outcome.Success]] leaves the proof DAG unwalked and only says `□` was derived. What
    * [[Prover.solve]] and [[Prover.proveTstp]] want, neither of which asks for a kernel proof. */
  def solve(problem: Problem, opts: SearchOptions = SearchOptions(),
                   goal: Set[Int] = Set.empty): Clausal.Outcome =
    val p = prepare(problem)
    Clausal.refute(p.work, opts, symbolVars = p.symbolVars, discharge = p.abs.dischargeSubst, goal = goal)

