package lisa.automation.superposition

import java.io.File
import scala.util.{Try, Success, Failure}

import lisa.utils.K
import lisa.tptp.{AnnotatedFormula, AnnotatedStatement, ProofPrinter}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable, unsanitize}
import lisa.automation.clausification.Clausification

/** CASC-compatible command-line entry point (see the [[https://tptp.org/CASC/J13/Design.html CASC J13 design]]
  * and the [[https://tptp.org/UserDocs/SZSOntology/ SZS ontology]]).
  *
  * Parses one TPTP problem file, clausifies it without producing a proof, runs [[Clausal.solveOutcome]] and
  * writes an SZS status line. On a refutation it also prints the derivation as the standard requires: one
  * clause per source formula, attributed to it, then the derivation of `$false`. Both come straight from the
  * [[Bridge.Outcome]], never through a kernel proof.
  *
  * Usage: `CascProver [-t <seconds>] <problem.p>`. The prover is given slightly less than the budget, so that
  * the status line is printed before an external wrapper's hard limit fires. */
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
   *  incomplete run, e.g. after SInE pruning, can never yield a wrong verdict); a timeout is `Timeout`.
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
        // Input formulas as AnnotatedFormula (a cnf clause becomes its disjunction), keeping names/roles.
        // `clausalFormWithOrigins`' origins index into `axiomLike ++ [conjecture]`, in that order.
        val axiomLike0: IndexedSeq[AnnotatedFormula] = parsed.formulas.collect {
          case s: AnnotatedStatement if axiomLikeRoles.contains(s.role) => s.toFormula
        }.toIndexedSeq
        val conjecture: Option[AnnotatedFormula] = parsed.formulas.collectFirst {
          case s: AnnotatedStatement if s.role == "conjecture" => s.toFormula
        }
        // SInE axiom selection, pruning the annotated axioms *before* clausification and keeping names aligned
        // so the derivation's `c<idx>` leaves still refer to the survivors. It fires only if this problem passes
        // [[Sine.shouldFilter]]'s gates; decided here, per invocation, sharing nothing.
        val axiomLike: IndexedSeq[AnnotatedFormula] = (cli.strategy.sine, conjecture) match
          case (Some(cfg), Some(c)) if Sine.shouldFilter(axiomLike0.map(_.formula), c.formula) =>
            val keep = Sine.selectIndices(axiomLike0.map(_.formula), c.formula, cfg)
            val kept = axiomLike0.zipWithIndex.collect { case (f, i) if keep(i) => f }
            Console.err.println(s"% SInE: kept ${kept.size} of ${axiomLike0.size} axioms (tolerance ${cfg.tolerance}, depth ${cfg.depth})")
            kept
          case (Some(_), _) =>
            Console.err.println("% SInE: gates not met, running unfiltered")
            axiomLike0
          case _ => axiomLike0
        val cprob = Clausification.Problem(
          axiomLike.map(f => K.Sequent(Set.empty, Set(f.formula))),
          conjecture.map(c => K.Sequent(Set.empty, Set(c.formula)))
        )
        Try {
          // Uncertified clausify + distinct-object axioms + goal-clause indices. Shared with StrategyEvaluation.
          val (clauses, clausal, goal) = Clausal.cascSetup(cprob, orthologic = cli.strategy.orthologic)
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

  /** A first-order input formula as a TPTP `fof` body, via the shared [[lisa.tptp.ProofPrinter]] (`strict` =
   *  real un-sanitized names). [[Tptp]] below renders `cnf` clause bodies instead, which need dense `X<n>`
   *  variables and `!=` literals that the FOF printer is not meant to produce. */
  private def fofFormula(e: K.Expression): String =
    ProofPrinter.formulaToFOFFormula(e, Set.empty, strict = true).pretty

  /** Emit the CNFRefutation: the input formulas as leaves, the negated conjecture as an intermediate step, one
   *  clause per source formula (`inference(clausification, [status(esa)], [<origin>])`), and finally the prover's
   *  own derivation of `$false` from those clauses.
   *
   *  '''Precondition:''' the input clauses hold the *first* bank ids, in `clauses` order, which is how
   *  [[Bridge.solve]] builds them and what the naming and the cone test both index on. */
  private def printRefutation(
      name: String,
      axiomLike: IndexedSeq[AnnotatedFormula],
      conjecture: Option[AnnotatedFormula],
      clauses: IndexedSeq[(K.Sequent, Int)],
      refutation: Bridge.Outcome.Success,
      isCnf: Boolean // input is CNF ⇒ leaves are `cnf` (never introduce the more expressive `fof`; TPTP rule)
  ): Unit =
    println(s"% SZS output start CNFRefutation for $name")
    // Print only the **cone of □**: the clauses actually used, not the whole clausification. `inCone(idx)` tests
    // the idx-th input clause (its bank id is the idx-th, clauses being fed in order); `usedOrigins` are the
    // source formulas they draw from, where `axiomLike.size` is the negated conjecture.
    val cone: Set[Int] = coneIds(refutation.empty)
    val inputIds: IndexedSeq[Int] = refutation.inputs.keys.toIndexedSeq.sorted
    def inCone(idx: Int): Boolean = inputIds.lift(idx).exists(cone.contains)
    val usedOrigins: Set[Int] = clauses.iterator.zipWithIndex.collect { case ((_, o), idx) if inCone(idx) => o }.toSet
    // Two TPTP statements sharing a name is illegal, so every generated step name must avoid the input names. A
    // fresh prefix is one no input name uses as `<prefix><digits>`, so `<prefix><n>` cannot collide.
    val taken: Set[String] = axiomLike.map(_.name).toSet ++ conjecture.map(_.name)
    def freshPrefix(base: String): String =
      Iterator.iterate(base)(_ + "_").find(p => !taken.exists(n => n.length > p.length && n.startsWith(p) && n.substring(p.length).forall(_.isDigit))).get
    val cPrefix = freshPrefix("c")
    val dPrefix = freshPrefix("d")
    // Leaves: only the source formulas whose clauses reach □, in the problem's own language -- `cnf` for a CNF
    // problem, whose variables are implicitly universal, so the closure is stripped; `fof` otherwise.
    for (f, i) <- axiomLike.zipWithIndex if usedOrigins.contains(i) do
      if isCnf then println(s"cnf(${f.name}, ${f.role}, ${Tptp.cnfClause(f.formula)}).")
      else println(s"fof(${f.name}, ${f.role}, ${fofFormula(f.formula)}).")
    // The conjecture + its negation, printed only if the negated conjecture is actually used.
    val negatedConjectureName: Option[String] = conjecture.filter(_ => usedOrigins.contains(axiomLike.size)).map { c =>
      println(s"fof(${c.name}, conjecture, ${fofFormula(c.formula)}).")
      val nn = ("negated_conjecture" #:: LazyList.from(1).map("negated_conjecture" + _)).find(!taken(_)).get
      println(s"fof($nn, negated_conjecture, ${fofFormula(K.neg(c.formula))}, inference(negate_conjecture, [status(cth)], [${c.name}])).")
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
    def unsan(s: String): String = unsanitize(s, 0) // shared `lisa.tptp` decode: $u→_, $s→space
    if nm.startsWith("$d") then Some("\"" + unsan(nm.drop(2)).replace("\\", "\\\\").replace("\"", "\\\"") + "\"")
    else if nm.startsWith("$n") then Some(unsan(nm.drop(2)))
    else None

  /** An interned symbol name `nm` as a valid TPTP `atomic_word`: a `$d`/`$n` distinct-object/numeral un-mangled
   *  to its source form ([[unmangleSpecial]]), a lower-word verbatim (our lowercase-prefixed fresh symbols such
   *  as `sk`, `sk_1`, `nm` included), anything else single-quoted. Reverses `KernelParser.sanitize` ($u→_,
   *  $s→space) so the output echoes the input's real names (e.g. `accept_team`, not `accept$uteam`), the exact
   *  inverse of the parser's encode. Shared by the flat-CNF renderer ([[Tptp]]) and the derivation printer. */
  private def functor(nm: String): String =
    unmangleSpecial(nm).getOrElse {
      val u = unsanitize(nm, 0)
      if u.nonEmpty && u.matches("[a-z][a-zA-Z0-9_]*") then u
      else "'" + u.replace("\\", "\\\\").replace("'", "\\'") + "'"
    }

  // ── proof-DAG navigation (shared by the cone computation and the derivation printer) ──
  // Sort/dedup canonicalization is a logical no-op on a set-of-literals clause, so alias it to its parent so that it does
  // not appear as a step (matching the kernel reconstruction, which treats it as a pass-through).
  private def deref(c: Core.Clause): Core.Clause =
    import Core.Justification
    c.justification match
      case Justification.Canonicalization(p) => deref(p)
      case _                                 => c
  private def parents(c: Core.Clause): List[Core.Clause] = c.justification.premises.map(deref)

  /** The clause ids in the **cone** of `□`, everything reachable via [[parents]]. That is the proof (the clauses
   *  actually used), as opposed to the whole saturation; input clauses / source formulas outside it are not printed. */
  private def coneIds(empty: Core.Clause): Set[Int] =
    val cone  = scala.collection.mutable.HashSet.empty[Int]
    val stack = scala.collection.mutable.Stack(deref(empty))
    while stack.nonEmpty do
      val c = stack.pop()
      if cone.add(c.id) then parents(c).foreach(stack.push)
    cone.toSet

  /** Emit the prover's derivation of `$false`, printed directly from the [[Bridge.Outcome.Success]] (no kernel
   *  proof). Only the clauses reachable from `□` through the [[Core.Justification]] DAG, i.e. the proof rather than the search
   *  space, are visited in topological order (parents before children, `□` last) via an **iterative** post-order
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

    // ── prover-term → TPTP (variables are clause-local, densely numbered ⇒ `X<n>`); `functor` is the shared helper ──
    def term(t: Term): String =
      if bank.isVar(t) then "X" + bank.varNum(t).num
      else
        // Reassemble the identifier from its two parts: `info.name` alone prints `sk` for every `sk_i`.
        val info = sig.info(bank.headSymbol(t))
        val nm = functor(K.Identifier(info.name, info.no).toString)
        val n  = bank.arity(t)
        if n == 0 then nm else s"$nm(${(0 until n).map(i => term(bank.arg(t, i))).mkString(",")})"
    def literal(l: Literal): String =
      val atom = bank.atomOf(l)
      if bank.isEqualityAtom(atom) then
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

    private def flatten(e: Expression): (Expression, List[Expression]) = Bridge.headAndArgs(e)

    /** Render `e`, drawing TPTP variable names (uppercase) from the shared `vnames` map so that a clause's
     *  literals, and a formula's binders and their occurrences, agree on names. */
    private def render(e: Expression, vnames: scala.collection.mutable.LinkedHashMap[Variable, String]): String =
      def vname(v: Variable): String = vnames.getOrElseUpdate(v, "X" + vnames.size)
      // `id.toString`, never `id.name`: the counter is part of the identity. Skolem constants are minted `sk`,
      // `sk_1`, `sk_2`, … all sharing the name `sk`, so dropping it collapses distinct symbols into one -- and
      // `printDerivation` keys on the full identifier, so the two halves of the proof would then disagree.
      def functorOf(id: Identifier): String = functor(id.toString)
      // Only an `Ind`-sorted variable is a TPTP variable; a `Variable` at any other sort is a *symbol* here (the
      // definitional naming atoms, and `ScreenPhase`'s `usr…` predicate variables). Printing those with `vname`
      // gives invalid TPTP when applied (`X0(X1)`) and a silently *weaker* clause when nullary.
      def symbol(head: Expression): String = head match
        case v: Variable if v.sort == Ind => vname(v)
        case v: Variable                  => functorOf(v.id)
        case c: Constant                  => functorOf(c.id)
        case _                            => functor(head.toString)
      def applied(e: Expression): String =
        val (head, args) = flatten(e)
        val h = symbol(head)
        if args.isEmpty then h else s"$h(${args.map(term).mkString(",")})"
      def term(t: Expression): String = t match
        case v: Variable => symbol(v) // via `symbol`, so the sort rule above applies in term position too
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

    /** A (universally-closed) clause formula as a bare TPTP CNF disjunction, with leading `∀`s stripped, since a
     *  `cnf` statement's variables are implicitly universally quantified.
     *
     *  η-expanded first for the same reason as [[Bridge.formulaToSequent]]: `strip` needs the explicit `Lambda`,
     *  and an unstripped quantifier would print as the functor `'∀'(p)`: well-formed TPTP, but a quantifier is
     *  not legal in a `cnf` body, so the emitted proof would be rejected. */
    def cnfClause(e: Expression): String =
      def strip(e: Expression): Expression = e match { case Forall(_, b) => strip(b); case _ => e }
      render(strip(lisa.automation.clausification.Clausification.etaExpandQuantifiers(e)), scala.collection.mutable.LinkedHashMap.empty)

    /** A clause sequent as a TPTP CNF disjunction (variables shared across its literals). Both sides are read:
      * a clause is `a₁, …, aₘ ⊢ b₁, …, bₙ` for `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ`, so each left formula prints
      * negated. Reading only the right side would silently drop every negative literal. */
    def clause(seq: Sequent): String =
      val vnames = scala.collection.mutable.LinkedHashMap.empty[Variable, String]
      val lits = seq.left.toSeq.map(neg(_)) ++ seq.right.toSeq
      if lits.isEmpty then "$false" else lits.map(l => render(l, vnames)).mkString(" | ")
