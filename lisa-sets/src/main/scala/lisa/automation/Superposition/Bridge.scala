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
 * Both entry points return `true` iff the input clause set is refuted (the empty clause is derived,
 * i.e. the set is unsatisfiable), and `false` if the search saturates without `□` or hits the
 * `maxGiven` budget. With an unbounded `maxGiven` the search is a semi-decision procedure: it may not
 * terminate on a satisfiable first-order set. The loop uses [[CompleteBestLiteralSelector]] (Vampire's
 * complete default selector) so resolution is refutation-complete (equality is treated as an ordinary
 * predicate for now — no paramodulation until Phase 3).
 */
object Bridge:

  /**
   * Run the prover on a collection of clauses given as kernel sequents (`left ⊢ right` = the clause
   * `¬left ∨ right`). Builds a fresh bank + complete selector, converts each sequent in that bank, and
   * saturates. Returns `true` iff the set is refuted (the empty clause is derivable), `false` if the
   * search saturates without `□` or hits the `maxGiven` budget.
   */
  def solve(sequents: Iterable[K.Sequent], maxGiven: Int = Int.MaxValue): Boolean =
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)
    bank.selector = new CompleteBestLiteralSelector(new KBO(bank))
    val clauses: Seq[Clause] = sequents.iterator.map(s => clauseOfSequent(bank, s)).toSeq
    new Discount(bank, trail).saturate(clauses, maxGiven) match
      case Discount.Result.Refutation(_) => true
      case _ => false

  /**
   * Run the prover on a [[lisa.tptp.Problem]] whose formulas are each a pure clause (a possibly
   * universally-quantified disjunction of literals, e.g. a TPTP `cnf` problem). Returns `true` iff the
   * set is refuted.
   */
  def solveProblem(problem: Problem, maxGiven: Int = Int.MaxValue): Boolean =
    solve(problemSequents(problem), maxGiven)

  /**
   * Like [[solve]], but on a refutation reconstruct a kernel [[lisa.utils.K.SCProof]] whose imports are
   * the given sequents and whose conclusion is the empty sequent `⊢`. Returns `None` if no refutation
   * is found within `maxGiven`. See [[Reconstruction]].
   */
  def proveAndReconstruct(sequents: Iterable[K.Sequent], maxGiven: Int = Int.MaxValue): Option[K.SCProof] =
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val trail: Trail = new Trail(bank)
    bank.selector = new CompleteBestLiteralSelector(new KBO(bank))
    val inputs = mutable.Map.empty[Int, Reconstruction.InputInfo]
    val clauses: Seq[Clause] = sequents.iterator.map { s =>
      val vars = mutable.HashMap.empty[K.Variable, Int]
      val c = clauseOfSequent(bank, s, vars)
      inputs(c.id) = (s, vars.iterator.map((kv, n) => n -> kv).toMap)
      c
    }.toSeq
    new Discount(bank, trail).saturate(clauses, maxGiven) match
      case Discount.Result.Refutation(empty) => Some(Reconstruction.reconstruct(empty, bank, inputs))
      case _ => None

  /** [[proveAndReconstruct]] for a [[lisa.tptp.Problem]] of pure clauses. */
  def proveAndReconstructProblem(problem: Problem, maxGiven: Int = Int.MaxValue): Option[K.SCProof] =
    proveAndReconstruct(problemSequents(problem), maxGiven)

  private def problemSequents(problem: Problem): Seq[K.Sequent] =
    problem.formulas.map {
      case s: AnnotatedSequent => s.sequent
      case f: AnnotatedFormula => formulaToSequent(f.formula)
    }

  // -----------------------------------------------------------------------------------------
  // Kernel FOL -> internal clause conversion
  //
  // Function/predicate symbols are interned by (name, arity) into the shared signature (so they are
  // consistent across clauses); equality "=" lands on the reserved [[EqualitySymbol]]. Each clause has
  // its own variable numbering (0, 1, …), since clause variables are independent.
  // -----------------------------------------------------------------------------------------

  private def clauseOfSequent(bank: TermBank, seq: K.Sequent): Clause =
    clauseOfSequent(bank, seq, mutable.HashMap.empty[K.Variable, Int])

  /** As above, but threads a caller-owned variable map (kernel variable → internal number) for reconstruction. */
  private def clauseOfSequent(bank: TermBank, seq: K.Sequent, vars: mutable.HashMap[K.Variable, Int]): Clause =
    val lits: List[Literal] =
      seq.left.toList.map(f => literal(bank, vars, f, positive = false)) :::
        seq.right.toList.map(f => literal(bank, vars, f, positive = true))
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
  private def literal(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], f: K.Expression, positive: Boolean): Literal =
    f match
      case K.Application(n, inner) if n == K.neg => literal(bank, vars, inner, !positive)
      case _ => bank.mkLiteral(atomTerm(bank, vars, f), positive)

  /** Build the internal atom term for a predicate application (head must be a predicate constant). */
  private def atomTerm(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], f: K.Expression): Term =
    val (head, args) = headAndArgs(f)
    head match
      case c: K.Constant =>
        val sym: Symbol = bank.signature.intern(c.id.name, args.size, isPredicate = true)
        bank.mkApp(sym, args.iterator.map(a => term(bank, vars, a)).toArray)
      case other =>
        throw IllegalArgumentException(s"not a pure clause: literal head is not a predicate constant: $other")

  /** Build an internal term: a variable (renumbered per clause), or a function/constant application. */
  private def term(bank: TermBank, vars: mutable.HashMap[K.Variable, Int], t: K.Expression): Term =
    t match
      case v: K.Variable => bank.mkVar(Core.Variable(vars.getOrElseUpdate(v, vars.size)))
      case _ =>
        val (head, args) = headAndArgs(t)
        head match
          case c: K.Constant =>
            val sym: Symbol = bank.signature.intern(c.id.name, args.size, isPredicate = false)
            bank.mkApp(sym, args.iterator.map(a => term(bank, vars, a)).toArray)
          case other =>
            throw IllegalArgumentException(s"not first-order: term head is not a constant (applied variable?): $other")

  /** Decompose a curried application `f(a₁)…(aₙ)` into its head `f` and argument list `[a₁, …, aₙ]`. */
  private def headAndArgs(e: K.Expression): (K.Expression, List[K.Expression]) = e match
    case K.Application(f, arg) =>
      val (h, as) = headAndArgs(f)
      (h, as :+ arg)
    case _ => (e, Nil)
