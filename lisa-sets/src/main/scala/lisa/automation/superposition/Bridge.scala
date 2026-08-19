package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K
import lisa.tptp.{Problem, AnnotatedFormula, AnnotatedSequent}
import lisa.automation.clausification.Clausification

import Core.*
import lisa.automation.superposition.ordering.*

/** Runs the prover on clauses given as kernel sequents, converting between that form and the internal one. A
  * sequent `a₁, …, aₘ ⊢ b₁, …, bₙ` is the clause `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ`, so the left side carries the
  * negative literals and the empty sequent is the empty clause.
  *
  * [[solve]] saturates once and returns an [[Outcome]]; `Success.reconstructKernelProof` turns a refutation
  * into a kernel proof.
  *
  * The **encoding** half of the boundary with the kernel. [[Clausal]] is the other half, adapting the
  * clausification package to this one. A caller with a first-order problem enters through `Clausal`, one that
  * already holds clause sequents enters here. */
object Bridge:

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
   * saturates within the `maxGiven` given-clause and `maxMillis` wall-clock budgets. Returns
   * [[Outcome.Success]] with the empty clause (and the context to reconstruct it) iff `□` is derived,
   * else [[Outcome.Saturated]] (passive exhausted) or [[Outcome.Timeout]] (budget hit). The per-input
   * variable maps are always recorded so a `Success` can be reconstructed later (cheap: O(input size);
   * the proof DAG itself is only walked by [[Outcome.Success.reconstructKernelProof]]).
   *
   * @param sequents   the clause set, one sequent per clause.
   * @param maxGiven   given-clause budget: how many clauses may be activated before the search gives up.
   * @param maxMillis  wall-clock budget, checked once per given clause.
   * @param opts       every search knob, in one value; see [[SearchOptions]].
   * @param symbolVars schematic symbol variables: kernel `Variable`s to be treated as **symbols** by the prover
   *                   rather than as clause variables, and rebuilt as variables in reconstruction.
   *                   Empty for pure first order clausal input.
   * @param discharge  abstraction discharge: each symbol `F` ↦ its closed value `λfv. e`. When non-empty,
   *                   reconstruction inlines `F` back to `e`, so the proof carries the original subterms.
   * @param goal       indices (into `sequents`) of the goal input clauses, the negated conjecture, for
   *                   goal-directed clause selection. Goal-ness propagates through inferences; empty means no
   *                   goal bias, as for a conjecture-free problem.
   * @param onStats    loop instrumentation sink, invoked with the loop's [[Discount.LoopStats]] after
   *                   saturation, for any outcome. Default no-op.
   */
  def solve(
      sequents: Iterable[K.Sequent],
      maxGiven: Int = Int.MaxValue,
      maxMillis: Long = Long.MaxValue,
      opts: SearchOptions = SearchOptions(),
      symbolVars: Set[K.Variable] = Set.empty,
      discharge: Map[K.Variable, K.Expression] = Map.empty,
      goal: Set[Int] = Set.empty,
      onStats: Discount.LoopStats => Unit = _ => ()): Outcome =
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
    val result = discount.saturate(maxGiven, maxMillis)
    onStats(discount.loopStats)
    result match
      case Discount.Result.Refutation(empty) => Outcome.Success(empty, bank, inputs, schematicIds, discharge)
      case Discount.Result.Saturated => Outcome.Saturated
      case Discount.Result.Unknown => Outcome.Timeout

  /** [[solve]] on a [[lisa.tptp.Problem]] whose formulas are each a pure clause (e.g. a TPTP `cnf`
   *  problem): converts it to clause-sequents and hands them to [[solve]]. `opts` is forwarded whole, never
   *  unpacked; see [[SearchOptions]]. */
  def solveTPTPProblem(
      problem: Problem,
      maxGiven: Int = Int.MaxValue,
      maxMillis: Long = Long.MaxValue,
      opts: SearchOptions = SearchOptions(),
      onStats: Discount.LoopStats => Unit = _ => ()): Outcome =
    solve(problemSequents(problem), maxGiven, maxMillis, opts, onStats = onStats)

  private def problemSequents(problem: Problem): Seq[K.Sequent] =
    problem.formulas.map {
      case s: AnnotatedSequent => s.sequent
      case f: AnnotatedFormula => formulaToSequent(f.formula)
    }

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


  /** A clause formula `∀…(l₁ ∨ … ∨ lₙ)` as a sequent: negative literals on the left, positive on the right.
    *
    * η-expanded first, because [[stripForall]] matches an explicit `Lambda`: an η-reduced `∀(p)` would not be
    * stripped, and would reach [[atomTerm]] as an opaque atom headed by `∀`, interned as an ordinary unary
    * predicate. This is the third of the three entry points that establish that invariant; see
    * [[lisa.automation.clausification.Clausification.etaExpandQuantifiers]]. Expected to be a no-op here (TPTP
    * input is parsed to explicit binders, and a `cnf` clause has none at all), which is exactly why it is applied
    * rather than assumed: it is idempotent and costs one traversal of an already-clausal formula. */
  private def formulaToSequent(formula: K.Expression): K.Sequent =
    val body: K.Expression = stripForall(Clausification.etaExpandQuantifiers(formula))
    val polarised: List[(K.Expression, Boolean)] =
      if body == K.bot then Nil // ⊥ is the empty clause
      else disjuncts(body).map(polarity)
    K.Sequent(
      polarised.collect { case (atom, false) => atom }.toSet,
      polarised.collect { case (atom, true) => atom }.toSet
    )

  /** Peel leading `¬`s off a literal, returning its atom and final polarity (`true` = positive). */
  private def polarity(f: K.Expression): (K.Expression, Boolean) = f match
    case K.Application(n, inner) if n == K.neg =>
      val (atom, p) = polarity(inner); (atom, !p)
    case _ => (f, true)

  /** Strip leading universal quantifiers `∀x. …` (their bodies are the clause's literals). */
  private def stripForall(e: K.Expression): K.Expression = e match
    case K.Application(q, K.Lambda(_, body)) if q == K.forall => stripForall(body)
    case _ => e

  /** Flatten a right-associated `∨` chain into its disjuncts (a single non-`∨` is one disjunct). */
  private def disjuncts(e: K.Expression): List[K.Expression] = e match
    case K.Application(K.Application(K.or, l), r) => disjuncts(l) ::: disjuncts(r)
    case _ => List(e)

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
