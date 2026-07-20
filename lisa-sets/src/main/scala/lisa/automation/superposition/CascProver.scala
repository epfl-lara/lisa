package lisa.automation.superposition

import java.io.File
import scala.util.{Try, Success, Failure}

import lisa.utils.K
import lisa.tptp.{AnnotatedFormula, AnnotatedStatement}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.clausification.{Clausification, UncertifiedClausification}

/**
 * CASC-compatible command-line entry point (see the [[https://tptp.org/CASC/J13/Design.html CASC J13 design]]
 * and the [[https://tptp.org/UserDocs/SZSOntology/ SZS ontology]]).
 *
 * Given a single TPTP problem file it parses the problem, clausifies it with the **fast, non-certifying**
 * clausifier ([[UncertifiedClausification]]/`FastClausify`), runs the superposition prover
 * ([[Clausal.solveOutcome]] — the raw [[Bridge.Outcome]] path, so it never builds a Lisa/kernel proof), and
 * writes an SZS status line to stdout:
 * {{{
 *   % SZS status Theorem for SYN075+1.p
 * }}}
 * On a refutation it also emits the solution, delimited per the SZS standard:
 * {{{
 *   % SZS output start CNFRefutation for SYN075+1.p
 *   fof(ax1, axiom, ...).                                              % the input formulas (leaves)
 *   cnf(c0, plain, ..., inference(clausification, [status(esa)], [ax1])).   % one clause per source formula
 *   ...                                                               % (the refutation body is not emitted yet)
 *   % SZS output end CNFRefutation for SYN075+1.p
 * }}}
 * The clausification part is complete: each clause records the single input formula it was derived from
 * (`inference(clausification, [status(esa)], [<origin>])`). The refutation body (the derivation of `$false`
 * from the clauses) is still a placeholder — the plan is to print the prover's own derivation of the empty
 * clause directly from the [[Bridge.Outcome.Success]], without going through the Lisa kernel representation.
 *
 * Usage: `CascProver [-t <seconds>] <problem.p>`. The wall-clock budget defaults to 300 s; the prover is given
 * slightly less so the status line is printed before an external CASC wrapper's hard limit fires. Equality
 * inferences are auto-enabled only when the clause set actually contains `=` (handled in [[Bridge]]).
 */
object CascProver:

  private val DefaultLimitSeconds = 300L
  private val OutputMarginMillis  = 2000L // reserve time to print the answer before an external hard kill

  /** Parsed command line: the problem file, the wall-clock budget, and the search strategy (one portfolio slice). */
  private final case class Cli(problem: File, limitSeconds: Long, strategy: Strategy)

  private def parseCli(args: List[String], acc: Cli): Cli = args match
    case ("-t" | "--cpu-limit" | "--wc-limit") :: n :: rest => parseCli(rest, acc.copy(limitSeconds = n.toLong))
    case "--strategy" :: n :: rest                          =>
      Strategy.byName(n) match
        case Some(s) => parseCli(rest, acc.copy(strategy = s))
        case None =>
          Console.err.println(s"unknown strategy '$n'; available: ${Strategy.portfolio.map(_.name).mkString(", ")}")
          sys.exit(2)
    case flag :: rest if flag.startsWith("-")               => parseCli(rest, acc) // ignore unknown flags
    case file :: rest                                       => parseCli(rest, acc.copy(problem = new File(file)))
    case Nil                                                => acc

  /** The SZS status for an outcome. Deliberately conservative: a refutation (empty clause) is `Theorem` with a
   *  conjecture and `Unsatisfiable` without; a saturation is `GaveUp` (we never claim (Counter)Satisfiable, so an
   *  incomplete run — e.g. after SInE pruning — can never yield a wrong verdict); a timeout is `Timeout`.
   *  A parse/solve failure is reported as `Error` at the call sites. */
  private def szsStatus(hasConjecture: Boolean, outcome: Bridge.Outcome): String = outcome match
    case _: Bridge.Outcome.Success => if hasConjecture then "Theorem" else "Unsatisfiable"
    case Bridge.Outcome.Saturated  => "GaveUp"
    case Bridge.Outcome.Timeout    => "Timeout"

  def main(args: Array[String]): Unit =
    val cli = parseCli(args.toList, Cli(null, DefaultLimitSeconds, Strategy.balanced))
    if cli.problem == null then
      Console.err.println("usage: CascProver [-t <seconds>] [--strategy <name>] <problem.p>")
      sys.exit(2)
    val name = cli.problem.getName
    val budgetMillis = math.max(1000L, cli.limitSeconds * 1000L - OutputMarginMillis)

    Try(problemToKernel(cli.problem)(using (strictMapAtom, strictMapTerm, strictMapVariable))) match
      case Failure(e) =>
        // Includes are resolved by the TPTP parser; a parse/processing failure is reported as an SZS Error.
        println(s"% SZS status Error for $name")
        Console.err.println(s"parse error: $e")
      case Success(parsed) =>
        // Input formulas, uniformly as AnnotatedFormula (a cnf clause becomes its disjunction formula), keeping
        // names/roles. `origins` from clausalFormWithOrigins index into `axiomLike ++ [conjecture]`, in this order.
        val axiomLike0: IndexedSeq[AnnotatedFormula] = parsed.formulas.collect {
          case s: AnnotatedStatement if axiomLikeRoles.contains(s.role) => s.toFormula
        }.toIndexedSeq
        val conjecture: Option[AnnotatedFormula] = parsed.formulas.collectFirst {
          case s: AnnotatedStatement if s.role == "conjecture" => s.toFormula
        }
        // SInE axiom selection (this strategy's config, if any): prune the annotated axioms *before* clausification,
        // keeping names aligned so the derivation's `c<idx>` leaves still refer to the surviving axioms. The filter
        // fires only if `SinePolicy`'s gates pass on this actual problem (large + genuinely prunable); otherwise the
        // strategy runs unfiltered. Decided independently, here, in this single invocation — nothing is shared.
        val axiomLike: IndexedSeq[AnnotatedFormula] = (cli.strategy.sine, conjecture) match
          case (Some(cfg), Some(c)) if SinePolicy.shouldFilter(axiomLike0.map(_.formula), c.formula) =>
            val keep = Sine.selectIndices(axiomLike0.map(_.formula), c.formula, cfg)
            val kept = axiomLike0.zipWithIndex.collect { case (f, i) if keep(i) => f }
            Console.err.println(s"% SInE: kept ${kept.size} of ${axiomLike0.size} axioms (tolerance ${cfg.tolerance}, depth ${cfg.depth})")
            kept
          case (Some(_), _) =>
            Console.err.println("% SInE: gates not met — running unfiltered")
            axiomLike0
          case _ => axiomLike0
        val cprob = Clausification.Problem(
          axiomLike.map(f => K.Sequent(Set.empty, Set(f.formula))),
          conjecture.map(c => K.Sequent(Set.empty, Set(c.formula)))
        )
        Try {
          val clauses0 = UncertifiedClausification.clausalFormWithOrigins(cprob, orthologic = cli.strategy.orthologic) // fast, non-certifying
          // After clausification, before solving: append the TPTP distinct-object distinctness axioms (`$da ≠ $db`).
          // They carry origin -1 (no source formula), printed later with `inference(distinct, …, [])`.
          val distinct = Clausal.distinctObjectAxioms(clauses0.map(_._1))
          val clauses = clauses0 ++ distinct.map(s => (s, -1))
          val clausal = Clausification.Problem(clauses.map(_._1).toList, None)
          // Goal-directed selection: clauses clausified from the negated conjecture (origin index == #axioms) are
          // the goal; goal-ness then propagates through the derivation (see Bridge/Discount `nonGoalWeightCoefficient`).
          val goal = clauses.iterator.zipWithIndex.collect { case ((_, origin), i) if origin == axiomLike.size => i }.toSet
          (clauses, cli.strategy.solveOutcome(clausal, maxMillis = budgetMillis, goal = goal))
        } match
          case Failure(e) =>
            println(s"% SZS status Error for $name")
            Console.err.println(s"solve error: $e")
          case Success((clauses, outcome)) =>
            println(s"% SZS status ${szsStatus(conjecture.isDefined, outcome)} for $name")
            outcome match
              case s: Bridge.Outcome.Success => printRefutation(name, axiomLike, conjecture, clauses, s, isCnf = parsed.spc.exists(_.contains("CNF")))
              case _                         => () // Saturated/Timeout: no CNFRefutation
    Console.out.flush()

  /** Emit the CNFRefutation: the input formulas as leaves, the negated conjecture as an intermediate step, one
   *  clause per source formula (`inference(clausification, [status(esa)], [<origin>])`), and finally the prover's
   *  own derivation of `$false` from those clauses. */
  private def printRefutation(
      name: String,
      axiomLike: IndexedSeq[AnnotatedFormula],
      conjecture: Option[AnnotatedFormula],
      clauses: IndexedSeq[(K.Sequent, Int)],
      refutation: Bridge.Outcome.Success,
      isCnf: Boolean // input is CNF ⇒ leaves are `cnf` (never introduce the more expressive `fof`; TPTP rule)
  ): Unit =
    println(s"% SZS output start CNFRefutation for $name")
    // Print only the **cone of □** — the input clauses (and the source formulas they came from) actually used in
    // the refutation, not the whole clausification. `inCone(idx)` tests the idx-th input clause (its bank id is the
    // idx-th, since clauses are fed in order); `usedOrigins` are the source-formula indices they draw from
    // (`axiomLike.size` = the negated conjecture).
    val cone: Set[Int] = coneIds(refutation.empty)
    val inputIds: IndexedSeq[Int] = refutation.inputs.keys.toIndexedSeq.sorted
    def inCone(idx: Int): Boolean = inputIds.lift(idx).exists(cone.contains)
    val usedOrigins: Set[Int] = clauses.iterator.zipWithIndex.collect { case ((_, o), idx) if inCone(idx) => o }.toSet
    // Every generated step name (`negated_conjecture`, input clauses `<cPrefix><idx>`, derived `<dPrefix><k>`) must
    // avoid the input formula names — two statements sharing a name is illegal TPTP. A fresh prefix is one no input
    // name uses as `<prefix><digits>`, so `<prefix><n>` can never collide.
    val taken: Set[String] = axiomLike.map(_.name).toSet ++ conjecture.map(_.name)
    def freshPrefix(base: String): String =
      Iterator.iterate(base)(_ + "_").find(p => !taken.exists(n => n.length > p.length && n.startsWith(p) && n.substring(p.length).forall(_.isDigit))).get
    val cPrefix = freshPrefix("c")
    val dPrefix = freshPrefix("d")
    // Leaves: only the source formulas whose clauses reach □. Match the problem's language — `cnf` for a CNF
    // problem (variables implicitly universal, so strip the closure), `fof` otherwise.
    for (f, i) <- axiomLike.zipWithIndex if usedOrigins.contains(i) do
      if isCnf then println(s"cnf(${f.name}, ${f.role}, ${Tptp.cnfClause(f.formula)}).")
      else println(s"fof(${f.name}, ${f.role}, ${Tptp.formula(f.formula)}).")
    // The conjecture + its negation, printed only if the negated conjecture is actually used.
    val negatedConjectureName: Option[String] = conjecture.filter(_ => usedOrigins.contains(axiomLike.size)).map { c =>
      println(s"fof(${c.name}, conjecture, ${Tptp.formula(c.formula)}).")
      val nn = ("negated_conjecture" #:: LazyList.from(1).map("negated_conjecture" + _)).find(!taken(_)).get
      println(s"fof($nn, negated_conjecture, ${Tptp.formula(K.neg(c.formula))}, inference(negate_conjecture, [status(cth)], [${c.name}])).")
      nn
    }
    def originName(i: Int): String =
      if i < axiomLike.size then axiomLike(i).name else negatedConjectureName.getOrElse("negated_conjecture")
    // One `cnf` clause per in-cone input clause (origin index `axiomLike.size` is the negated conjecture).
    for (((clause, origin), idx) <- clauses.zipWithIndex if inCone(idx))
      if origin < 0 then // a distinct-object distinctness axiom: no parent, inference `distinct` (see Clausal.distinctObjectAxioms)
        println(s"cnf($cPrefix$idx, axiom, ${Tptp.clause(clause)}, inference(distinct, [status(thm)], [])).")
      else
        println(s"cnf($cPrefix$idx, plain, ${Tptp.clause(clause)}, inference(clausification, [status(esa)], [${originName(origin)}])).")
    printDerivation(refutation, cPrefix, dPrefix)
    println(s"% SZS output end CNFRefutation for $name")

  /** Reverse [[lisa.tptp.KernelParser]]'s Fix-B mangling for proof output: a `$d`-prefixed constant prints as a
   *  double-quoted TPTP distinct object `"…"`, a `$n`-prefixed one as a bare numeral; the rest yield `None`.
   *  (`$u`/`$s` are un-`sanitize`d back to `_`/space first.) */
  private def unmangleSpecial(nm: String): Option[String] =
    def unsan(s: String): String = s.replace("$u", "_").replace("$s", " ")
    if nm.startsWith("$d") then Some("\"" + unsan(nm.drop(2)).replace("\\", "\\\\").replace("\"", "\\\"") + "\"")
    else if nm.startsWith("$n") then Some(unsan(nm.drop(2)))
    else None

  // ── proof-DAG navigation (shared by the cone computation and the derivation printer) ──
  // Sort/dedup canonicalization is a logical no-op on a set-of-literals clause — alias it to its parent so it does
  // not appear as a step (matching the kernel reconstruction, which treats it as a pass-through).
  private def deref(c: Core.Clause): Core.Clause =
    import Core.Justification
    c.justification match
      case Justification.Canonicalization(p) => deref(p)
      case _                                 => c
  private def parents(c: Core.Clause): List[Core.Clause] =
    import Core.Justification
    (c.justification match
      case Justification.Input                            => Nil
      case Justification.Resolution(l, _, r, _)           => List(l, r)
      case Justification.Factoring(p, _, _)               => List(p)
      case Justification.Canonicalization(p)              => List(p)
      case Justification.Superposition(f, _, _, i, _, _)  => List(f, i)
      case Justification.EqualityResolution(p, _)         => List(p)
      case Justification.EqualityFactoring(p, _, _, _, _) => List(p)
      case Justification.Demodulation(t, _, _, r, _)      => List(t, r)
    ).map(deref)

  /** The clause ids in the **cone** of `□` — everything reachable via [[parents]]. That is the proof (the clauses
   *  actually used), as opposed to the whole saturation; input clauses / source formulas outside it are not printed. */
  private def coneIds(empty: Core.Clause): Set[Int] =
    val cone  = scala.collection.mutable.HashSet.empty[Int]
    val stack = scala.collection.mutable.Stack(deref(empty))
    while stack.nonEmpty do
      val c = stack.pop()
      if cone.add(c.id) then parents(c).foreach(stack.push)
    cone.toSet

  /** Emit the prover's derivation of `$false`, printed directly from the [[Bridge.Outcome.Success]] (no kernel
   *  proof). Only the clauses reachable from `□` through the [[Core.Justification]] DAG — the proof, not the search
   *  space — are visited, in topological order (parents before children, `□` last) via an **iterative** post-order
   *  so a deep derivation cannot overflow the stack. Input clauses reuse the `<cPrefix><idx>` names printed above;
   *  each derived clause gets a fresh `<dPrefix><k>` (both prefixes chosen collision-free by [[printRefutation]]). */
  private def printDerivation(s: Bridge.Outcome.Success, cPrefix: String, dPrefix: String): Unit =
    import Core.*
    val bank = s.bank
    val sig  = bank.signature
    // `deref`/`parents` are the shared object-level DAG helpers (above).
    def ruleName(c: Clause): String = c.justification match
      case Justification.Resolution(_, _, _, _)          => "resolution"
      case Justification.Factoring(_, _, _)              => "factoring"
      case Justification.Superposition(_, _, _, _, _, _) => "superposition"
      case Justification.EqualityResolution(_, _)        => "equality_resolution"
      case Justification.EqualityFactoring(_, _, _, _, _) => "equality_factoring"
      case Justification.Demodulation(_, _, _, _, _)     => "demodulation"
      case Justification.Input | Justification.Canonicalization(_) => "clausification"

    // ── prover-term → TPTP (variables are clause-local, densely numbered ⇒ `X<n>`) ──
    def functor(nm: String): String =
      unmangleSpecial(nm).getOrElse(
        if nm.nonEmpty && nm.matches("[a-z][a-zA-Z0-9_]*") then nm
        else "'" + nm.replace("\\", "\\\\").replace("'", "\\'") + "'"
      )
    def term(t: Term): String =
      if bank.isVar(t) then "X" + bank.varNum(t).num
      else
        val nm = functor(sig.info(bank.headSymbol(t)).name)
        val n  = bank.arity(t)
        if n == 0 then nm else s"$nm(${(0 until n).map(i => term(bank.arg(t, i))).mkString(",")})"
    def literal(l: Literal): String =
      val atom = bank.atomOf(l)
      if bank.headSymbol(atom) == EqualitySymbol then
        val (a, b) = (term(bank.arg(atom, 0)), term(bank.arg(atom, 1)))
        if bank.isPositive(l) then s"$a = $b" else s"$a != $b"
      else if bank.isPositive(l) then term(atom) else s"~${term(atom)}"
    def clauseStr(c: Clause): String =
      if c.literals.isEmpty then "$false" else c.literals.iterator.map(literal).mkString(" | ")

    // Input clause ids, in creation order (= clausification order), give the `c<idx>` names printed above.
    val nameOf = scala.collection.mutable.HashMap.empty[Int, String]
    for ((id, k) <- s.inputs.keys.toSeq.sorted.zipWithIndex) nameOf(id) = s"$cPrefix$k"

    // Iterative post-order over the proof DAG from `□`; input clauses are already printed, derived clauses get `d<k>`.
    val visited = scala.collection.mutable.HashSet.empty[Int]
    val stack   = scala.collection.mutable.Stack.empty[(Clause, Boolean)]
    var dcount  = 0
    stack.push((deref(s.empty), false))
    while stack.nonEmpty do
      val (c, emit) = stack.pop()
      if emit then
        c.justification match
          case Justification.Input => () // already emitted as its `c<idx>` clausification clause
          case _ =>
            val nm = s"$dPrefix$dcount"; dcount += 1; nameOf(c.id) = nm
            val ps = parents(c).map(p => nameOf(p.id)).mkString(",")
            println(s"cnf($nm, plain, ${clauseStr(c)}, inference(${ruleName(c)}, [status(thm)], [$ps])).")
      else if !visited(c.id) then
        visited += c.id
        stack.push((c, true))
        parents(c).foreach(p => stack.push((p, false)))

  /** Minimal TPTP printer for the first-order fragment the clausifier emits (no `λ` except under quantifiers). */
  private object Tptp:
    import lisa.utils.K.*

    /** A valid TPTP `atomic_word`: a `$d`/`$n` distinct-object/numeral un-mangled to its source form, a lower-word
     *  verbatim, anything else single-quoted (fresh Skolem/naming symbols such as `sK0`, `Ts0`). */
    private def functor(nm: String): String =
      unmangleSpecial(nm).getOrElse(
        if nm.nonEmpty && nm.matches("[a-z][a-zA-Z0-9_]*") then nm
        else "'" + nm.replace("\\", "\\\\").replace("'", "\\'") + "'"
      )

    /** Flatten a curried application `f(a)(b)…` into `(head, [a, b, …])`. */
    private def flatten(e: Expression): (Expression, List[Expression]) =
      def go(e: Expression, acc: List[Expression]): (Expression, List[Expression]) = e match
        case Application(f, a) => go(f, a :: acc)
        case head              => (head, acc)
      go(e, Nil)

    /** Render `e`, drawing TPTP variable names (uppercase) from the shared `vnames` map so that a clause's
     *  literals — and a formula's binders and their occurrences — agree on names. */
    private def render(e: Expression, vnames: scala.collection.mutable.LinkedHashMap[Variable, String]): String =
      def vname(v: Variable): String = vnames.getOrElseUpdate(v, "X" + vnames.size)
      def symbol(head: Expression): String = head match
        case v: Variable => vname(v) // only reached for a genuine Ind variable; predicate/function heads are constants
        case c: Constant => functor(c.id.name)
        case _           => functor(head.toString)
      def applied(e: Expression): String =
        val (head, args) = flatten(e)
        val h = head match { case c: Constant => functor(c.id.name); case _ => symbol(head) }
        if args.isEmpty then h else s"$h(${args.map(term).mkString(",")})"
      def term(t: Expression): String = t match
        case v: Variable => vname(v)
        case _           => applied(t)
      def atomic(e: Expression): String = e match // wrap binary connectives in parens where needed
        case And(_, _) | Or(_, _) | Implies(_, _) | Iff(_, _) => s"(${go(e)})"
        case _                                                => go(e)
      def go(e: Expression): String = e match
        case `top`         => "$true"
        case `bot`         => "$false"
        case Neg(Application(Application(eq, l), r)) if eq == equality => s"${term(l)} != ${term(r)}" // TPTP negated equality
        case Neg(g)        => s"~${atomic(g)}"
        case And(g, h)     => s"(${go(g)} & ${go(h)})"
        case Or(g, h)      => s"(${go(g)} | ${go(h)})"
        case Implies(g, h) => s"(${go(g)} => ${go(h)})"
        case Iff(g, h)     => s"(${go(g)} <=> ${go(h)})"
        case Forall(x, b)  => s"! [${vname(x)}] : ${atomic(b)}"
        case Exists(x, b)  => s"? [${vname(x)}] : ${atomic(b)}"
        case Application(Application(eq, l), r) if eq == equality => s"${term(l)} = ${term(r)}"
        case _             => applied(e) // predicate atom
      go(e)

    /** A full input formula. */
    def formula(e: Expression): String = render(e, scala.collection.mutable.LinkedHashMap.empty)

    /** A (universally-closed) clause formula as a bare TPTP CNF disjunction — leading `∀`s stripped, since a
     *  `cnf` statement's variables are implicitly universally quantified. */
    def cnfClause(e: Expression): String =
      def strip(e: Expression): Expression = e match { case Forall(_, b) => strip(b); case _ => e }
      render(strip(e), scala.collection.mutable.LinkedHashMap.empty)

    /** A clause `Sequent(∅, {literals})` as a TPTP CNF disjunction (variables shared across its literals). */
    def clause(seq: Sequent): String =
      val vnames = scala.collection.mutable.LinkedHashMap.empty[Variable, String]
      val lits = seq.right.toSeq
      if lits.isEmpty then "$false" else lits.map(l => render(l, vnames)).mkString(" | ")
