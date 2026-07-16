package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K
import lisa.tptp.{Problem, AnnotatedStatement, AnnotatedFormula, AnnotatedSequent}

import Core.*

/**
 * Entry points that run the superposition prover on problems expressed in Lisa's **kernel** syntax,
 * and the bridge that converts kernel first-order logic into the internal clause representation.
 *
 * A clause (a disjunction of literals) is represented as a kernel [[lisa.utils.K.Sequent]] in the
 * standard way: a sequent `a₁, …, aₘ ⊢ b₁, …, bₙ` denotes the clause
 * `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ`. So formulas on the **left** become **negative** literals and those
 * on the **right** become **positive** literals; the empty sequent `⊢` is the empty clause `□`.
 *
 * The entry point is [[solve]]: it runs the saturation **once** and returns an [[Outcome]] — a
 * [[Outcome.Success]] carrying the empty clause `□` and everything needed to reconstruct a proof (the
 * [[TermBank]] and the per-input variable maps), [[Outcome.Saturated]] (no `□`: the set is satisfiable),
 * or [[Outcome.Timeout]] (a budget was hit before deciding). [[solveTPTPProblem]] is the same for a
 * [[lisa.tptp.Problem]] (it converts then solves), and
 * `success.reconstructKernelProof` turns a `Success` into a kernel proof. With an
 * unbounded budget the search is a semi-decision procedure: it may not terminate on a satisfiable
 * first-order set. The loop uses [[CompleteBestLiteralSelector]] (Vampire's complete default selector)
 * so resolution is refutation-complete (equality is treated as an ordinary predicate for now — no
 * paramodulation until Phase 3).
 */
object Bridge:

  /**
   * The result of a [[solve]] run: a [[Outcome.Success]] (the empty clause `□` was derived) carrying
   * everything needed to reconstruct a kernel proof, [[Outcome.Saturated]] (the passive set was
   * exhausted without `□` — the clause set is satisfiable, a genuine decision), or [[Outcome.Timeout]]
   * (a budget was hit before deciding — the set's status is unknown).
   */
  sealed trait Outcome:
    /** Whether the set was refuted (`□` derived). */
    def refuted: Boolean = this match
      case _: Outcome.Success => true
      case Outcome.Saturated | Outcome.Timeout => false

  object Outcome:
    /**
     * A refutation. Holds the empty clause `empty` and the run's [[TermBank]] plus the per-input-clause
     * variable maps (`inputs`) — the context [[reconstructKernelProof]] needs to rebuild the proof.
     */
    final case class Success(
        empty: Clause,
        bank: TermBank,
        inputs: collection.Map[Int, Reconstruction.InputInfo],
        schematicNames: Set[String] = Set.empty,
        discharge: Map[K.Variable, K.Expression] = Map.empty) extends Outcome:
      /**
       * Reconstruct a kernel [[lisa.utils.K.SCProof]] from this refutation: its imports are the input
       * clause-sequents and its conclusion is the empty sequent `⊢`. Uses the bank and per-input data
       * carried here — no re-solving. `schematicNames` (Phase-3 abstraction symbols) are rebuilt as kernel
       * variables; when `discharge` maps them to their `λfv. e` values, they are instead inlined back to the
       * original (ε-)terms so the proof is free of the abstraction symbols. See [[Reconstruction]].
       */
      def reconstructKernelProof: K.SCProof = Reconstruction.reconstruct(empty, bank, inputs, schematicNames, discharge)

    /** The passive set was exhausted without deriving `□`: the clause set is satisfiable (a decision). */
    case object Saturated extends Outcome

    /** A budget — the `maxGiven` given-clause count or the `maxMillis` wall-clock limit — was hit before
     *  the search could decide. Not a decision: the set's status is unknown. */
    case object Timeout extends Outcome

  /**
   * Run the saturation **once** on a clause set (kernel sequents `left ⊢ right` = the clause
   * `¬left ∨ right`). Builds a fresh bank + complete selector, converts each sequent in that bank, and
   * saturates within the `maxGiven` given-clause and `maxMillis` wall-clock budgets. Returns
   * [[Outcome.Success]] with the empty clause (and the context to reconstruct it) iff `□` is derived,
   * else [[Outcome.Saturated]] (passive exhausted) or [[Outcome.Timeout]] (budget hit). The per-input
   * variable maps are always recorded so a `Success` can be reconstructed later (cheap: O(input size);
   * the proof DAG itself is only walked by [[Outcome.Success.reconstructKernelProof]]).
   */
  def solve(
      sequents: Iterable[K.Sequent],
      maxGiven: Int = Int.MaxValue,
      maxMillis: Long = Long.MaxValue,
      forwardSubsumption: Boolean = true,
      backwardSubsumption: Boolean = true,
      forwardUnitDeletion: Boolean = true,
      backwardUnitDeletion: Boolean = true,
      forwardSubsumptionResolution: Boolean = false,
      backwardSubsumptionResolution: Boolean = false,
      condensation: Boolean = false,
      forwardSimplifyAtGeneration: Boolean = false,
      // Master equality switch: when off, all equality inferences (superposition, equality resolution/factoring,
      // demodulation) are skipped, leaving pure ordered resolution + factoring. Use for equality-free problems.
      equality: Boolean = true,
      // Term indexing (Phase 5): find superposition partners via a fingerprint index over the active set rather
      // than the linear scan. Same inferences (so the proof is unchanged); kept as a flag for A/B benchmarking.
      fingerprintIndexing: Boolean = true,
      // Schematic symbol variables: kernel `Variable`s that are to be treated as **symbols** by the prover
      // (not clause variables) and rebuilt as variables in reconstruction. Dispatched by position: a symbol
      // variable in a literal-head position is a **predicate** symbol, in a term position a **function**
      // symbol (Phase-3 ε-abstractions `F`, and clausifier Tseitin atoms `tsᵢ`). Empty for ordinary input.
      symbolVars: Set[K.Variable] = Set.empty,
      // Phase-3 discharge: each abstraction symbol `F` ↦ its closed value `λfv. e`; when non-empty,
      // reconstruction inlines `F` back to `e` so the produced proof contains the original (ε-)terms, not `F`.
      discharge: Map[K.Variable, K.Expression] = Map.empty): Outcome =
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)
    bank.selector = new CompleteBestLiteralSelector(bank.order)
    val inputs = mutable.Map.empty[Int, Reconstruction.InputInfo]
    val clauses: Seq[Clause] = sequents.iterator.map { s =>
      val vars = mutable.HashMap.empty[K.Variable, Int]
      val c = clauseOfSequent(bank, s, vars, symbolVars)
      inputs(c.id) = (s, vars.iterator.map((kv, n) => n -> kv).toMap)
      c
    }.toSeq
    val schematicNames: Set[String] = symbolVars.map(_.id.toString)
    new Discount(
      bank,
      trail,
      forwardSubsumption = forwardSubsumption,
      backwardSubsumption = backwardSubsumption,
      forwardUnitDeletion = forwardUnitDeletion,
      backwardUnitDeletion = backwardUnitDeletion,
      forwardSubsumptionResolution = forwardSubsumptionResolution,
      backwardSubsumptionResolution = backwardSubsumptionResolution,
      condensation = condensation,
      forwardSimplifyAtGeneration = forwardSimplifyAtGeneration,
      equality = equality,
      fingerprintIndexing = fingerprintIndexing
    ).saturate(clauses, maxGiven, maxMillis) match
      case Discount.Result.Refutation(empty) => Outcome.Success(empty, bank, inputs, schematicNames, discharge)
      case Discount.Result.Saturated => Outcome.Saturated
      case Discount.Result.Unknown => Outcome.Timeout

  /** [[solve]] on a [[lisa.tptp.Problem]] whose formulas are each a pure clause (e.g. a TPTP `cnf`
   *  problem): converts it to clause-sequents and hands them to [[solve]]. */
  def solveTPTPProblem(
      problem: Problem,
      maxGiven: Int = Int.MaxValue,
      maxMillis: Long = Long.MaxValue,
      forwardSubsumption: Boolean = true,
      backwardSubsumption: Boolean = true,
      forwardUnitDeletion: Boolean = true,
      backwardUnitDeletion: Boolean = true,
      forwardSubsumptionResolution: Boolean = false,
      backwardSubsumptionResolution: Boolean = false,
      condensation: Boolean = false,
      forwardSimplifyAtGeneration: Boolean = false,
      equality: Boolean = true,
      fingerprintIndexing: Boolean = true): Outcome =
    solve(
      problemSequents(problem), maxGiven, maxMillis, forwardSubsumption, backwardSubsumption,
      forwardUnitDeletion, backwardUnitDeletion, forwardSubsumptionResolution, backwardSubsumptionResolution,
      condensation, forwardSimplifyAtGeneration, equality = equality, fingerprintIndexing = fingerprintIndexing
    )

  /** Convert a [[lisa.tptp.Problem]] of pure clauses (e.g. a TPTP `cnf` problem) to clause-sequents. */
  private def problemSequents(problem: Problem): Seq[K.Sequent] =
    problem.formulas.map {
      case s: AnnotatedSequent => s.sequent
      case f: AnnotatedFormula => formulaToSequent(f.formula)
    }

  // -----------------------------------------------------------------------------------------
  // Kernel FOL -> internal clause conversion
  //
  // Function/predicate symbols are interned by (full identifier, arity) into the shared signature (so
  // they are consistent across clauses); equality "=" lands on the reserved [[EqualitySymbol]]. The
  // intern key is the identifier's *whole* string `id.toString` -- NOT `id.name` -- because the kernel
  // stores a trailing numeric suffix as the counter index `id.no` (e.g. `e_1` is `Identifier("e", 1)`,
  // so `e_1` and `e_2` share the name `"e"` and differ only in `no`). Keying on `name` alone would
  // collapse them into one constant (silently corrupting the problem); `toString` is injective here,
  // since sanitised identifier names never contain the counter separator `_`. Each clause has its own
  // variable numbering (0, 1, …), since clause variables are independent.
  // -----------------------------------------------------------------------------------------

  private def clauseOfSequent(bank: TermBank, seq: K.Sequent): Clause =
    clauseOfSequent(bank, seq, mutable.HashMap.empty[K.Variable, Int], Set.empty)

  /** As above, but threads a caller-owned variable map (kernel variable → internal number) for reconstruction
   *  and the set of `symbolVars` (schematic variables treated as predicate/function symbols, not variables). */
  private def clauseOfSequent(bank: TermBank, seq: K.Sequent, vars: mutable.HashMap[K.Variable, Int], symbolVars: Set[K.Variable]): Clause =
    val lits: List[Literal] =
      seq.left.toList.map(f => literal(bank, vars, f, positive = false, symbolVars)) :::
        seq.right.toList.map(f => literal(bank, vars, f, positive = true, symbolVars))
    bank.mkClause(lits.toArray)


  /** A clause formula `∀…(l₁ ∨ … ∨ lₙ)` as a sequent: negative literals on the left, positive on the right. */
  private def formulaToSequent(formula: K.Expression): K.Sequent =
    val body: K.Expression = stripForall(formula)
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
   *  schematic **predicate** variable listed in `symbolVars` (a clausifier Tseitin atom `tsᵢ`, or a Lisa
   *  predicate variable) — interned as an (uninterpreted) predicate symbol. */
  private def atomTerm(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], f: K.Expression, symbolVars: Set[K.Variable]): Term =
    val (head, args) = headAndArgs(f)
    head match
      case c: K.Constant =>
        val sym: Symbol = bank.signature.intern(c.id.toString, args.size, isPredicate = true)
        bank.mkApp(sym, args.iterator.map(a => term(bank, vars, a, symbolVars)).toArray)
      case v: K.Variable if symbolVars.contains(v) =>
        val sym: Symbol = bank.signature.intern(v.id.toString, args.size, isPredicate = true)
        bank.mkApp(sym, args.iterator.map(a => term(bank, vars, a, symbolVars)).toArray)
      case other =>
        throw IllegalArgumentException(s"not a pure clause: literal head is not a predicate constant or symbol variable: $other")

  /** Build an internal term: a clause variable (renumbered per clause), a function/constant application, or a
   *  schematic **function** variable in `symbolVars` (a Phase-3 ε-abstraction `F`, or a Lisa function
   *  variable), interned as a function symbol (applied or bare-nullary) rather than treated as a clause variable. */
  private def term(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], t: K.Expression, symbolVars: Set[K.Variable]): Term =
    t match
      case v: K.Variable if symbolVars.contains(v) => // bare nullary function symbol
        bank.mkConst(bank.signature.intern(v.id.toString, 0, isPredicate = false))
      case v: K.Variable => bank.mkVar(Core.Variable(vars.getOrElseUpdate(v, vars.size)))
      case _ =>
        val (head, args) = headAndArgs(t)
        val sym: Symbol = head match
          case c: K.Constant => bank.signature.intern(c.id.toString, args.size, isPredicate = false)
          case v: K.Variable if symbolVars.contains(v) => // applied function symbol `F(fv…)`
            bank.signature.intern(v.id.toString, args.size, isPredicate = false)
          case other =>
            throw IllegalArgumentException(s"not first-order: term head is not a constant (applied variable?): $other")
        bank.mkApp(sym, args.iterator.map(a => term(bank, vars, a, symbolVars)).toArray)

  /** Decompose a curried application `f(a₁)…(aₙ)` into its head `f` and argument list `[a₁, …, aₙ]`. */
  private def headAndArgs(e: K.Expression): (K.Expression, List[K.Expression]) = e match
    case K.Application(f, arg) =>
      val (h, as) = headAndArgs(f)
      (h, as :+ arg)
    case _ => (e, Nil)
