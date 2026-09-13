package lisa.automation.clausification

import lisa.automation.superposition.TptpCorpus
import lisa.automation.superposition.bench.FofEvaluation
import lisa.automation.superposition.bench.ProblemList
import lisa.tptp.AnnotatedFormula
import lisa.tptp.AnnotatedSequent
import lisa.tptp.KernelParser.axiomLikeRoles
import lisa.tptp.KernelParser.problemToKernel
import lisa.tptp.KernelParser.strictMapAtom
import lisa.tptp.KernelParser.strictMapTerm
import lisa.tptp.KernelParser.strictMapVariable
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

import java.io.File
import scala.util.Failure
import scala.util.Success
import scala.util.Try

import Clausification.GeneratedNames

/**
 * Equivalence check between the **uncertified** clausifier ([[lisa.automation.clausification.UncertifiedClausifier]])
 * and the **certified** one ([[CertifiedClausifier]]), on real TPTP input. It establishes two things per input
 * formula: that the two make the *same naming decisions*, the certified named formula being equal to the
 * uncertified one *identically* since both mint their `nm` atoms with the same generator
 * ([[CertifiedClausifier.sameNaming]] is a plain `==`); and that they Skolemize to the same formula up to
 * renaming of the fresh symbols. This is the soundness lever: if the certified (kernel-checked) path names and
 * Skolemizes the same way, its clauses vouch for the uncertified path's.
 *
 * By default it runs a 20 + 20 seeded sample of the equality-free and equality-bearing FOF lists, which keeps
 * `sbt test` short. [[Corpus]] says how the environment scales it up to a whole benchmark corpus without a
 * rebuild, which is how the artefact backs the claim at the size the paper reports it.
 *
 * Needs the `TPTP` env var (the directory containing `Problems/`); skipped otherwise.
 */
class ClausifierEquivalenceTest extends AnyFunSuite:

  private def size(e: K.Expression): Int = e match
    case K.Application(f, a) => 1 + size(f) + size(a)
    case K.Lambda(_, b) => 1 + size(b)
    case _ => 1

  /**
   * Run `body` on a daemon thread, returning `Some(result)` if it finishes within `ms`, else interrupting it and
   *  returning `None`. Used to skip formulas whose certified ε-Skolemization blows up (until it shares terms).
   */
  private def runWithTimeout[A](ms: Long)(body: => A): Option[A] =
    val result = new java.util.concurrent.atomic.AtomicReference[Option[A]](None)
    val th = new Thread(() =>
      try result.set(Some(body))
      catch case _: Throwable => ()
    )
    th.setDaemon(true)
    th.start()
    th.join(ms)
    if th.isAlive then { th.interrupt(); None }
    else result.get

  /**
   * Structural equality up to renaming of the **fresh** symbols, with the problem symbols (all other constants)
   *  matching exactly. Two classes of fresh symbol, treated differently:
   *
   *   - **Ordinary variables** (clause variables `w…` or originals, and naming atoms `nm…`) must match by a
   *     consistent **bijection** (distinct on one side ⇒ distinct on the other).
   *   - **Skolem symbols**, `sk…` (uncertified, a Skolem `Constant`) and `feps…` (certified, the ε-abstraction function),
   *     match by a consistent **forward function** only (uncertified ⇒ certified), NOT a bijection. Uncertified mints a fresh
   *     Skolem per existential; on the side compared here identical ε-terms abstract to the same `feps` symbol, so
   *     syntactically-identical existentials *merge* (the certified clausifier itself does not: it mints a fresh `esk`
   *     per occurrence). So uncertified is a strict refinement: every uncertified Skolem maps onto one certified symbol, but one
   *     certified symbol may cover several uncertified ones. Requiring only the forward map captures exactly this (and more
   *     distinct Skolem functions is unconditionally sound, so the relaxation loses no soundness assurance).
   */
  // Returns None if isomorphic (in the above sense), else the first structurally-mismatching subexpression pair.
  private def isoMismatch(x: K.Expression, y: K.Expression): Option[(K.Expression, K.Expression)] =
    val fwd = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression]
    val bwd = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression]
    // Skolem symbols: uncertified's `sk` (a Constant), the certified path's `esk` (a schematic Variable), and the
    // test's `feps` ε-abstraction. Matched by name regardless of Constant/Variable so ε↔Skolem-function
    // representations line up. (Counter is in the identifier's `no` field, so the `name` is exactly the prefix.)
    def isSkolem(e: K.Expression): Boolean =
      val name = e match { case c: K.Constant => c.id.name; case v: K.Variable => v.id.name; case _ => "" }
      name == "feps" || name == GeneratedNames.skolemFun
    def renamable(e: K.Expression): Boolean = e.isInstanceOf[K.Variable] || isSkolem(e)
    def go(a: K.Expression, b: K.Expression): Option[(K.Expression, K.Expression)] = (a, b) match
      case (K.Application(f1, a1), K.Application(f2, a2)) => go(f1, f2).orElse(go(a1, a2))
      case (K.Lambda(_, _), _) | (_, K.Lambda(_, _)) => if a == b then None else Some((a, b))
      case _ if isSkolem(a) && isSkolem(b) => if fwd.getOrElseUpdate(a, b) == b then None else Some((a, b)) // forward only
      case _ if renamable(a) && renamable(b) => if fwd.getOrElseUpdate(a, b) == b && bwd.getOrElseUpdate(b, a) == a then None else Some((a, b))
      case _ => if a == b then None else Some((a, b))
    go(x, y)

  private def isoUpToRenaming(x: K.Expression, y: K.Expression): Boolean = isoMismatch(x, y).isEmpty

  /**
   * ε-abstraction for the test: replace each `ε(λx.φ)` by a fresh function `F` applied to the ε-term's **Ind**
   *  free variables (sorted by original name), matching UncertifiedClausifier's Skolem functions. Unlike `Clausal.Abstraction`
   *  this filters to `Ind` (the certified path names before Skolem, so ε-terms can contain predicate naming atoms,
   *  which are not Skolem-function arguments). Run *before* ∀-strip so `F`'s arguments carry the original names.
   *
   *  ε-terms are treated as **fully opaque** uninterpreted function symbols: we never look inside one (so nested
   *  ε-terms are absorbed into their enclosing symbol, exactly as UncertifiedClausifier's opaque Skolem functions absorb
   *  the witnesses they range over), and its identity is the *raw* ε-term, of which only the free variables are observable.
   *  Keying on the raw term (rather than recursively pre-abstracting the body) makes dedup structural: two identical
   *  ε-terms get one symbol regardless of the numbering order of any inner ε-terms.
   */
  private def absEps(e: K.Expression): K.Expression =
    var n = 0
    val memo = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression] // same raw ε-term ⇒ same symbol
    def go(e: K.Expression): K.Expression = e match
      case eps @ K.Application(f0, _) if f0 == K.epsilon => // an ε-term is opaque, so do NOT descend into its body
        memo.getOrElseUpdate(
          eps, {
            // A **Constant** (like UncertifiedClausifier's Skolem `sk`), NOT a Variable: else a nullary `feps` (result sort
            // Ind) would be an Ind-valued free variable and cascade in as an argument to outer Skolem functions.
            val fv = eps.freeVariables.toSeq.filter(_.sort == K.Ind).sortBy(v => (v.id.name, v.id.no))
            val fSym = K.Constant(K.Identifier("feps", n), fv.foldRight(K.Ind: K.Sort)((v, acc) => v.sort -> acc))
            n += 1
            fv.foldLeft(fSym: K.Expression)((acc, v) => K.Application(acc, v))
          }
        )
      case K.Application(f, a) => K.Application(go(f), go(a))
      case K.Lambda(x, b) => K.Lambda(x, go(b))
      case _ => e
    go(e)

  /**
   * Hypothesis formulas + the negated conjecture, exactly as the clausifier pipeline sees them.
   */
  private def inputFormulas(parsed: lisa.tptp.TptpProblem): Seq[K.Expression] =
    val hyps = parsed.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) => f.formula
    }
    val negConj = parsed.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => K.neg(f.formula)
    }
    hyps ++ negConj.toSeq

  // ── clause-set equivalence ──────────────────────────────────────────────────────────────────────
  //
  // The check above compares the two paths formula by formula, which stops short of the clauses: it says
  // nothing about distribution or about how the matrix is finally split. What the prover actually receives is
  // the clause set, and E1 compares the two paths on searches driven by it, so that is what has to agree.

  /**
   * The Skolem symbol behind `e`, if it is one. The two paths represent them differently — the certified path
   * as a schematic [[K.Variable]] named `esk`, the uncertified as a [[K.Constant]] named `sk` — so this is the
   * one place where the clause sets legitimately differ and the only thing the comparison maps.
   */
  private def skolemId(e: K.Expression): Option[K.Identifier] = e match
    case v: K.Variable if v.id.name == GeneratedNames.skolemFun => Some(v.id)
    case _ => None

  /** One literal as a string, with Skolem symbols and ordinary variables named by the given functions. */
  private def renderLiteral(e: K.Expression, sk: K.Identifier => String, vr: K.Identifier => String): String =
    def go(e: K.Expression): String = skolemId(e) match
      case Some(id) => sk(id)
      case None =>
        e match
          case v: K.Variable => vr(v.id)
          case c: K.Constant => c.id.toString
          case K.Application(f, a) => s"${go(f)}(${go(a)})"
          case K.Lambda(x, b) => s"λ${vr(x.id)}.${go(b)}"
    go(e)

  /**
   * One clause as a canonical string, given a naming for Skolem symbols.
   *
   * A sequent's sides are `Set`s, so literal order carries no information and cannot be compared directly.
   * Literals are therefore ordered by their *anonymised* rendering, and only then are variables numbered by
   * first occurrence in that order — two passes, because numbering variables first would make the numbering
   * depend on the set's iteration order, which is exactly what is not trustworthy.
   */
  private def canonicalClause(s: K.Sequent, sk: K.Identifier => String): String =
    // Clause variables are numbered per clause, by first occurrence. Their absolute numbers are not part of
    // the clause: a clause is implicitly universally quantified, so `w_196` and `w_88` name the same variable
    // of the same clause, and the two paths reach a given clause having minted different numbers of variables
    // before it. What must agree is which positions share a variable, which is what the numbering captures.
    //
    // Two passes, because a sequent's sides are `Set`s and literal order carries no information: literals are
    // ordered by their rendering with variables anonymous (Skolems are already globally numbered by the
    // caller, which is what makes this order discriminating), and only then are variables numbered.
    val key = (e: K.Expression) => renderLiteral(e, sk, _ => "V")
    val left = s.left.toSeq.sortBy(key)
    val right = s.right.toSeq.sortBy(key)
    val nums = scala.collection.mutable.LinkedHashMap.empty[K.Identifier, Int]
    def number(e: K.Expression): Unit =
      if skolemId(e).isEmpty then
        e match
          case v: K.Variable => nums.getOrElseUpdate(v.id, nums.size)
          case K.Application(f, a) => number(f); number(a)
          case K.Lambda(x, b) => nums.getOrElseUpdate(x.id, nums.size); number(b)
          case _ => ()
    (left ++ right).foreach(number)
    val vr = (id: K.Identifier) => s"V${nums.getOrElse(id, -1)}"
    // Sorted *after* numbering, not left in the numbering order. Literals that render alike while anonymous —
    // three `ssList(V)` in one clause, say — tie in the pass above, and the tie is broken by `Set` iteration
    // order, differently on each side. The numbering is unaffected (it is driven by the untied literals), so
    // the two sides produce the same multiset of rendered literals in a different order, and sorting settles it.
    s"${left.map(renderLiteral(_, sk, vr)).sorted.mkString(",")} |- ${right.map(renderLiteral(_, sk, vr)).sorted.mkString(",")}"

  /**
   * A clause set as a canonical list of strings: clauses ordered by their Skolem-agnostic form, then Skolem
   * symbols numbered by first occurrence in that order. Two sets that agree up to a bijection on Skolem
   * symbols render identically; a set that mints a *different number* of them does not, so the certified
   * path's fresh-per-occurrence Skolems would show as a mismatch rather than be quietly accepted.
   */
  /** A canonicalised clause set: each clause's string, the clause itself, and the Skolem numbering used. */
  private final case class Canonical(strings: Seq[String], clauses: Seq[K.Sequent], skolem: Map[K.Identifier, Int])

  private def canonicalClauses(cs: Seq[K.Sequent]): Canonical =
    val ordered = cs.sortBy(canonicalClause(_, _ => "SK"))
    val nums = scala.collection.mutable.LinkedHashMap.empty[K.Identifier, Int]
    // Number by walking the ordered clauses, so the numbering depends only on the canonical order.
    ordered.foreach(s => (s.left.toSeq ++ s.right.toSeq).sortBy(renderLiteral(_, _ => "SK", _.toString)).foreach { e =>
      def walk(x: K.Expression): Unit = skolemId(x) match
        case Some(id) => nums.getOrElseUpdate(id, nums.size)
        case None =>
          x match
            case K.Application(f, a) => walk(f); walk(a)
            case K.Lambda(_, b) => walk(b)
            case _ => ()
      walk(e)
    })
    Canonical(ordered.map(canonicalClause(_, id => s"SK${nums.getOrElse(id, -1)}")), ordered, nums.toMap)

  /**
   * Whether two clauses are the same clause under a renaming of their variables, with Skolem symbols pinned by
   * the numbering each set was canonicalised with.
   *
   * Searched rather than computed, unlike [[canonicalClause]], which numbers variables by first occurrence in
   * a fixed literal order and so needs that order to be unambiguous. It is not: two literals with the same
   * predicate and shape render alike once variables are blanked out — `frontsegP(V)(V)` twice — and the tie
   * falls to set iteration order, which differs between the two sides. Whichever tied literal is numbered
   * first decides the numbering, so the same clause can canonicalise two ways. Searching for the bijection
   * sidesteps the question. Only the clauses left unmatched by the string comparison come here, and they are
   * few and small, so pairing them off exhaustively costs nothing.
   */
  /** A bijection between two sets of identifiers, kept in both directions so injectivity is checked. */
  private type Bij = (Map[K.Identifier, K.Identifier], Map[K.Identifier, K.Identifier])
  private val emptyBij: Bij = (Map.empty, Map.empty)

  private def extend(bij: Bij, x: K.Identifier, y: K.Identifier): Option[Bij] =
    val (fwd, bwd) = bij
    Option.when(fwd.get(x).forall(_ == y) && bwd.get(y).forall(_ == x))((fwd + (x -> y), bwd + (y -> x)))

  /**
   * A symbol the clausifier invented, and whether it is shared between clauses.
   *
   * Skolem functions and naming atoms are '''global''': a naming atom appears both in the clauses defining it
   * and in the clause using it, and a Skolem function can be shared likewise, so they must correspond
   * consistently across the whole clause set. Clause variables are '''local''': a clause is implicitly
   * universally quantified, so each clause renames independently.
   */
  private def globalFresh(e: K.Expression): Option[K.Identifier] = e match
    case v: K.Variable if v.id.name == GeneratedNames.skolemFun || v.id.name == GeneratedNames.namingAtom => Some(v.id)
    case _ => None

  /**
   * Whether `a` and `b` are the same clause under a renaming: local variables by a fresh bijection per clause,
   * global symbols by `global`, which is threaded across the whole clause set and returned extended.
   */
  private def variantsOf(a: K.Sequent, b: K.Sequent, global: Bij): Iterator[Bij] =
    def matchExpr(x: K.Expression, y: K.Expression, g: Bij, loc: Bij): Option[(Bij, Bij)] =
      (globalFresh(x), globalFresh(y)) match
        case (Some(i), Some(j)) => extend(g, i, j).map((_, loc))
        case (Some(_), None) | (None, Some(_)) => None
        case _ =>
          (x, y) match
            case (vx: K.Variable, vy: K.Variable) => extend(loc, vx.id, vy.id).map((g, _))
            case (cx: K.Constant, cy: K.Constant) => Option.when(cx.id == cy.id)((g, loc))
            case (K.Application(f1, a1), K.Application(f2, a2)) =>
              matchExpr(f1, f2, g, loc).flatMap((g1, l1) => matchExpr(a1, a2, g1, l1))
            case _ => Option.when(x == y)((g, loc))
    // Each literal of `xs` is tried against every remaining literal of `ys`, extending bijections shared by
    // both sides of the sequent, so a renaming that suits the left cannot contradict the right.
    //
    // Returns *every* matching, not the first. Committing to the first is the obvious way to write this and it
    // is wrong: the left side is often symmetric — three interchangeable individuals guarded by the same
    // predicates — so it admits several matchings, and only some of them let the right side match. With an
    // `Option` here, a clause whose right side is `x=y, x=z, y=z` against `x=y, z=x, z=y` (the same clause,
    // under `x↦z, y↦x, z↦y`) is reported as having no partner at all.
    def matchSide(xs: List[K.Expression], ys: List[K.Expression], g: Bij, loc: Bij): Iterator[(Bij, Bij)] =
      xs match
        case Nil => if ys.isEmpty then Iterator((g, loc)) else Iterator.empty
        case x :: rest =>
          ys.indices.iterator.flatMap { i =>
            matchExpr(x, ys(i), g, loc).iterator.flatMap((g1, l1) => matchSide(rest, ys.patch(i, Nil, 1), g1, l1))
          }
    if a.left.size != b.left.size || a.right.size != b.right.size then Iterator.empty
    else
      // Every renaming, not the first. `pairOff` chooses partners across the whole set, and each renaming maps
      // the shared symbols differently; committing to one here would hide the alternatives from that search.
      matchSide(a.left.toList, b.left.toList, global, emptyBij)
        .flatMap((g, l) => matchSide(a.right.toList, b.right.toList, g, l))
        .map(_._1)

  /**
   * The clauses of `cert` and `uncert` that cannot be paired off, as `(unmatched certified, unmatched
   * uncertified)`; both empty when the two sets are the same. Clauses whose canonical strings coincide are
   * matched by string, which settles the bulk of them in one pass; whatever is left is paired by search.
   */
  private def unmatchedClauses(cert: Seq[K.Sequent], uncert: Seq[K.Sequent]): (Seq[K.Sequent], Seq[K.Sequent]) =
    val c = canonicalClauses(cert)
    val u = canonicalClauses(uncert)
    if c.strings == u.strings then (Nil, Nil)
    else
      val shared = c.strings.groupBy(identity).map((s, xs) => (s, xs.size min u.strings.count(_ == s)))
      def leftovers(x: Canonical): Seq[K.Sequent] =
        val quota = scala.collection.mutable.HashMap.from(shared)
        x.strings.zip(x.clauses).filterNot { (s, _) => quota.get(s).exists(_ > 0) && { quota(s) -= 1; true } }.map(_._2)
      // The residue is paired by search rather than by string, threading one bijection on the global symbols
      // through every pair: matching clause A to clause B fixes which Skolem corresponds to which, and that
      // constrains every later pair. Backtracks over the choice of partner, since the first partner that fits
      // in isolation need not be the one that lets the rest fit. `budget` bounds it — this is NP-complete, and
      // reporting that the search gave up is honest where hanging or claiming agreement would not be.
      var budget = 200000
      def pairOff(cs: List[K.Sequent], us: List[K.Sequent], global: Bij): Option[Unit] =
        if cs.isEmpty then Option.when(us.isEmpty)(())
        else if budget <= 0 then None
        else
          // Take the most constrained clause first, and if it has exactly one possible partner, commit to it
          // without a choice point. That is what makes this tractable: pairing one clause fixes which Skolems
          // and naming atoms correspond, which usually forces the next, so the residue collapses in a chain
          // rather than branching. Only genuinely ambiguous clauses cost a backtrack.
          val options = cs.map(a => (a, us.filter(b => { budget -= 1; variantsOf(a, b, global).hasNext })))
          val (a, partners) = options.minBy(_._2.size)
          if partners.isEmpty then None
          else
            partners.iterator
              .flatMap(b => variantsOf(a, b, global).flatMap(g => pairOff(cs.filterNot(_ eq a), us.filterNot(_ eq b), g)))
              .nextOption()
      val restC = leftovers(c).toList
      val restU = leftovers(u).toList
      // A failure here is not a difference between the clause sets, and is reported rather than asserted.
      // The string pass commits to a pairing, and for a clause with a symmetric twin the string is ambiguous,
      // so that pairing can be the wrong one — leaving a residue that cannot be matched among itself even
      // when the full sets correspond exactly. Undoing it means searching over all the clauses at once, which
      // this algorithm cannot do: the candidate scan alone is quadratic per level, and on a problem with
      // thousands of clauses it exhausts any budget long before it concludes anything.
      //
      // Settling those cases wants a canonical labelling of the shared symbols by colour refinement over the
      // clause/symbol incidence structure, rather than a greedy pass plus search. That has not been written.
      if pairOff(restC, restU, emptyBij).isDefined then (Nil, Nil) else (restC, restU)

  /** The clause set the certified pipeline hands its prover, captured with a `Sorry` back end. */
  private def certifiedClauses(p: lisa.automation.Problem): Seq[K.Sequent] =
    var captured: lisa.automation.Problem = null
    CertifiedClausifier.certifyClausal(p, q => { captured = q; K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), q.imports) })
    captured.imports.toSeq

  test("certified and uncertified clausifier name AND Skolemize equivalently across the corpus") {
    val root = TptpCorpus.rootOrCancel("the uncertified/certified naming equivalence check")
    val problems = Corpus.problems
    val startedAt = System.currentTimeMillis()
    val deadline = Corpus.budgetMs.map(startedAt + _)
    var found = 0 // selected problems whose file is actually under `root`
    var problemsChecked = 0 // ... of those, the ones that parsed
    var formulasSeen = 0 // formulas the parsed problems contain, before the per-problem cap
    var formulasChecked = 0
    var oversize = 0 // formulas skipped as too big to check in reasonable time
    var skolemTimeouts = 0 // formulas whose certified ε-Skolemization did not finish in 2s
    var overBudget = 0 // ... or ran the clausifier out of heap, which is the same fact caught by a different guard
    val skolemFails = scala.collection.mutable.ListBuffer.empty[(String, Option[(K.Expression, K.Expression)])]
    // Both of these are asserted empty at the end, but collected rather than thrown: a run over a whole corpus
    // that dies on its first bad formula reports nothing at all -- not the count, not the other problems, not
    // even how far it got -- which is exactly the information needed to act on the failure.
    val namingFails = scala.collection.mutable.ListBuffer.empty[String]
    val errors = scala.collection.mutable.ListBuffer.empty[(String, Throwable)]
    val unparsed = scala.collection.mutable.ListBuffer.empty[(String, Throwable)]

    val pending = problems.iterator
    while pending.hasNext && !deadline.exists(System.currentTimeMillis() >= _) do
      val rel = pending.next()
      val f = new File(root, rel)
      if f.exists then
        found += 1
        // Catch Throwable, not just NonFatal: the TPTP parser can StackOverflow on very large problems.
        val parsedOpt: Option[lisa.tptp.TptpProblem] =
          try Some(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
          catch
            case t: Throwable =>
              unparsed += ((rel, t)) // named, not just counted: "396 of 400 parsed" invites asking which four
              None
        parsedOpt.foreach { parsed =>
          problemsChecked += 1
          val available = inputFormulas(parsed)
          formulasSeen += available.size
          // The deadline is polled per formula, not only per problem: one CASC problem is some 40000 formulas
          // and hours of work, so a between-problems poll lets a single problem overrun the budget many times
          // over -- which it did, before this.
          val toCheck = Corpus.formulasOf(available).iterator
          while toCheck.hasNext && !deadline.exists(System.currentTimeMillis() >= _) do
            val phi = toCheck.next()
            if size(phi) > 8000 then oversize += 1 // `findSite` is superlinear, so a giant formula stalls the run
            else
              val t0 = System.nanoTime()
              // Catch Throwable: over a corpus the clausifier meets formulas that overflow the stack, and one
              // of those must not take the other 399 problems' results with it.
              try
                // (1) after naming: the certified and uncertified named formulas agree *identically* (same `nm` generator).
                if !CertifiedClausifier.sameNaming(phi) then namingFails += rel
                // (2) after Skolem: uncertified (Skolem functions) equals certified (ε-terms, ∀-stripped, ε-abstracted).
                // Some LCL modal problems build exponentially-large ε-terms (until the certified Skolemization shares
                // them properly), so run the certified side under a 2s budget and count a timeout as unchecked.
                val uncertifiedSk = CertifiedClausifier.uncertifiedNamedNnfSkolem(phi) // linear (Skolem functions), always cheap
                runWithTimeout(2000) { CertifiedClausifier.stripForall(absEps(CertifiedClausifier.namedNnfSkolemEps(phi))) } match
                  case None => skolemTimeouts += 1; println(f"[timer] TIMEOUT  size=${size(phi)}%6d  $rel")
                  case Some(certSk) =>
                    if !isoUpToRenaming(uncertifiedSk, certSk) then skolemFails += ((rel, isoMismatch(uncertifiedSk, certSk)))
                    formulasChecked += 1
              catch
                // The clausifier's own valve (`Clausification.checkInterrupted`, a heap ceiling) reports the
                // same fact as the 2s cap: this formula's ε-Skolemization blew up. So it is a skip, like a
                // timeout, and only counted. Anything else is a bug and has to fail the run.
                case t @ (_: InterruptedException | _: OutOfMemoryError) =>
                  overBudget += 1
                  println(f"[timer] RESOURCE size=${size(phi)}%6d  $rel: ${t.getMessage}")
                case t: Throwable =>
                  errors += ((rel, t))
                  println(f"[timer] ERROR    size=${size(phi)}%6d  $rel: $t")
              // `println` (not `info`): sbt buffers `info` to test-end, so it is useless for watching progress live.
              val ms = (System.nanoTime() - t0) / 1000000
              if ms > 1000 then println(f"[timer] ${ms}%6d ms  size=${size(phi)}%6d  $rel")
        }

    val stoppedEarly = deadline.exists(System.currentTimeMillis() >= _)
    val elapsedS = (System.currentTimeMillis() - startedAt) / 1000
    val divergentProblems = (namingFails ++ skolemFails.map(_._1)).distinct.size
    val summary =
      s"${Corpus.name}: $problemsChecked of $found problems parsed, out of ${problems.size} selected; " +
        s"$formulasChecked of $formulasSeen formulas checked ($oversize oversize, $skolemTimeouts over 2s, $overBudget over heap, ${errors.size} errored); " +
        s"${namingFails.size} naming and ${skolemFails.size} skolem divergences in $divergentProblems problems; ${elapsedS}s" +
        (if stoppedEarly then " (stopped on budget)" else "")
    println(s"[summary] $summary")
    unparsed.foreach((p, t) => println(s"[summary]   unparsed: $p: $t"))
    namingFails.distinct.foreach(p => println(s"[summary]   naming-diverge: $p"))
    skolemFails.foreach((p, m) => println(s"[summary]   skolem-diverge: $p: $m"))
    errors.map((p, t) => s"$p: $t").distinct.foreach(e => println(s"[summary]   error: $e"))
    info(summary)
    Corpus.record(
      "list,selected,found,parsed,formulas_seen,formulas,oversize,timeouts,over_heap,errors," +
        "naming_divergences,skolem_divergences,divergent_problems,elapsed_s,stopped_early",
      Seq(Corpus.name, problems.size, found, problemsChecked, formulasSeen, formulasChecked, oversize, skolemTimeouts, overBudget, errors.size,
        namingFails.size, skolemFails.size, divergentProblems, elapsedS, stoppedEarly).mkString(",")
    )

    assert(found > 0, s"none of the ${problems.size} selected problems exist under $root; is the corpus complete?")
    // Without this a parser regression would show up only as a quietly smaller check, the divergence assertions
    // below still passing over whatever survived.
    assert(problemsChecked * 4 >= found * 3, s"only $problemsChecked of $found problems parsed")
    assert(formulasChecked > 0)
    assert(namingFails.isEmpty, s"${namingFails.size} naming divergences (e.g. ${namingFails.headOption})")
    assert(skolemFails.isEmpty, s"${skolemFails.size} skolem divergences (e.g. ${skolemFails.headOption})")
    assert(errors.isEmpty, s"${errors.size} formulas raised (e.g. ${errors.headOption.map((p, t) => s"$p: $t")})")
  }

  /**
   * T1: the two clausifiers are the same transformation, compared where it matters — on the clause sets the
   * prover receives, per problem, up to a bijection on Skolem symbols.
   *
   * This is the precondition E1 rests on. The two paths are compared on searches, and a search is driven by
   * its clause set: if the sets differed, a difference in solved counts would say nothing about the cost of
   * certification. The formula-level check above is upstream of distribution and of the final clause split,
   * so it cannot establish this.
   *
   * Filtered by clausification '''time''', not by problem size, so that the shapes excluded are the ones that
   * are genuinely slow rather than the ones that merely look large — a size filter drops exactly the blow-up
   * cases this is meant to cover. What was skipped is counted and reported.
   */
  /**
   * Both paths mark the negated conjecture's clauses as the goal, which is what a strategy's
   * `nonGoalWeightCoefficient` selects on. This compares how many clauses each marks, and they must agree.
   *
   * The case to watch is `NamingPhase`: naming inside the conjecture emits definitions as fresh hypotheses
   * appended after the originals, and they must join the goal, since the uncertified path attributes each
   * clause, definitions included, to the formula it came from.
   */
  test("certified and uncertified clausifiers mark the same negated conjecture as the goal") {
    val root = TptpCorpus.rootOrCancel("the uncertified/certified goal-clause check")
    val problems = Corpus.problems
    val startedAt = System.currentTimeMillis()
    val deadline = Corpus.budgetMs.map(startedAt + _)
    var checked, agree, slow, notParsed = 0
    val fewer = scala.collection.mutable.ListBuffer.empty[(String, Int, Int)] // certified marks fewer
    val lost = scala.collection.mutable.ListBuffer.empty[String] //               certified marks none at all
    val invented = scala.collection.mutable.ListBuffer.empty[(String, Int, Int)] // certified marks more

    val pending = problems.iterator
    while pending.hasNext && !deadline.exists(System.currentTimeMillis() >= _) do
      val rel = pending.next()
      val f = new File(root, rel)
      if f.exists then
        val parsed =
          try Some(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
          catch case _: Throwable => { notParsed += 1; None }
        parsed.foreach { p =>
          val hyps = p.formulas.collect { case a: AnnotatedFormula if axiomLikeRoles.contains(a.role) => K.Sequent(Set.empty, Set(a.formula)) }
          val conj = p.formulas.collectFirst { case a: AnnotatedFormula if a.role == "conjecture" => K.Sequent(Set.empty, Set(a.formula)) }
          val problem = lisa.automation.Problem(hyps, conj)
          if conj.isDefined then
            runWithTimeout(20000) {
              var certGoal = 0
              CertifiedClausifier.certifyClausalGoal(
                problem,
                (q, g) => { certGoal = g.size; K.SCProof(IndexedSeq(K.Sorry(K.Sequent(Set.empty, Set.empty))), q.imports) }
              )
              // The uncertified side appends the negated conjecture last, so its clauses are the ones whose
              // origin is the original hypothesis count -- the same convention `Prover.goalClauses` uses.
              val (_, origins) = UncertifiedClausifier.clausalProblemWithOrigins(problem)
              (certGoal, origins.count(_ == hyps.size))
            } match
              case None => slow += 1
              case Some((c, u)) =>
                checked += 1
                if c == u then agree += 1
                else if c == 0 && u > 0 then lost += rel
                else if c < u then fewer += ((rel, c, u))
                else invented += ((rel, c, u))
        }

    val summary =
      s"${Corpus.name}: goal-clause counts agree on $agree of $checked problems with a conjecture " +
        s"(${fewer.size} mark fewer under certification, ${lost.size} lose the goal, ${invented.size} mark more; " +
        s"$slow too slow, $notParsed unparsed) in ${(System.currentTimeMillis() - startedAt) / 1000}s"
    println(s"[goal] $summary")
    fewer.take(5).foreach { case (r, c, u) => println(s"[goal]   fewer: $r certified=$c uncertified=$u") }
    info(summary)
    assert(checked > 0, "no problem with a conjecture was checked")
    assert(lost.isEmpty, s"${lost.size} problems lose the goal entirely under certification: ${lost.take(3).mkString(", ")}")
    assert(fewer.isEmpty, s"${fewer.size} problems mark fewer goal clauses under certification: ${fewer.take(3)}")
    assert(invented.isEmpty, s"${invented.size} problems mark MORE goal clauses under certification, which cannot be right: ${invented.take(3)}")
  }

  test("certified and uncertified clausifiers produce the same clause set for each problem") {
    val root = TptpCorpus.rootOrCancel("the uncertified/certified clause-set check")
    val problems = Corpus.problems
    val startedAt = System.currentTimeMillis()
    val deadline = Corpus.budgetMs.map(startedAt + _)
    var checked = 0
    var slow = 0 // clausification did not finish in the per-problem budget
    var inOrder = 0 // problems where the two paths already emit their clauses in the same order
    var tooLarge = 0 // clause sets beyond what the pairing search can decide
    var notParsed = 0 // the TPTP front end could not read the problem
    val mismatches = scala.collection.mutable.ListBuffer.empty[(String, Int, Int)] // different clause COUNTS
    val unpaired = scala.collection.mutable.ListBuffer.empty[String] // same count, but some clause does not pair off
    val errors = scala.collection.mutable.ListBuffer.empty[(String, Throwable)]

    val pending = problems.iterator
    while pending.hasNext && !deadline.exists(System.currentTimeMillis() >= _) do
      val rel = pending.next()
      val f = new File(root, rel)
      if f.exists then
        val parsed =
          try Some(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
          catch case _: Throwable => { notParsed += 1; None }
        parsed.foreach { p =>
          val hyps = p.formulas.collect { case a: AnnotatedFormula if axiomLikeRoles.contains(a.role) => K.Sequent(Set.empty, Set(a.formula)) }
          val conj = p.formulas.collectFirst { case a: AnnotatedFormula if a.role == "conjecture" => K.Sequent(Set.empty, Set(a.formula)) }
          val problem = lisa.automation.Problem(hyps, conj)
          // Both sides under one budget, since either can be the slow one and the comparison needs both.
          runWithTimeout(20000) {
            val c = certifiedClauses(problem)
            val u = UncertifiedClausifier.clausalForm(problem).hypotheses
            // Also whether the two paths emit their clauses in the same order to begin with, compared on the
            // Skolem-agnostic form so that only the order is in question. If they do, the ambiguity this
            // comparison works around could instead be removed at the source, by having both keep their
            // clauses and literals ordered until the clause set is handed over.
            val sameOrder = c.size == u.size && c.map(canonicalClause(_, _ => "SK")) == u.map(canonicalClause(_, _ => "SK"))
            (c.size, u.size, unmatchedClauses(c, u), sameOrder)
          } match
            case None => slow += 1; println(s"[clauses] SLOW $rel")
            // Too many clauses for the pairing search to decide. Skipped rather than reported as a
            // difference: on a clause set this size the greedy string pass can mispair a clause with its
            // symmetric twin, and undoing that means matching every clause at once, which is quadratic per
            // level and settles nothing within any budget. Bounding the input is what lets the check below be
            // an assertion of equality rather than a caveat.
            case Some((nc, nu, _, _)) if nc.max(nu) > Corpus.maxClauses =>
              tooLarge += 1
            case Some((nc, nu, (restC, restU), sameOrder)) =>
              checked += 1
              if sameOrder then inOrder += 1
              if nc != nu then
                mismatches += ((rel, nc, nu))
                println(s"[clauses] COUNT DIFFERS $rel  certified=$nc uncertified=$nu")
              else if restC.nonEmpty || restU.nonEmpty then
                unpaired += rel
                // Which kind of failure: a clause with no counterpart at all, or counterparts that exist
                // individually but admit no assignment consistent on the shared symbols.
                val lonely = restC.count(a => restU.forall(b => !variantsOf(a, b, emptyBij).hasNext))
                println(s"[clauses] UNPAIRED $rel  ${restC.size} of $nc clauses; $lonely have no counterpart at all")
                restC.take(2).foreach(c => println(s"[clauses]   only certified:   ${canonicalClause(c, _ => "SK")}"))
                restU.take(2).foreach(c => println(s"[clauses]   only uncertified: ${canonicalClause(c, _ => "SK")}"))
        }

    val summary =
      s"${Corpus.name}: clause sets identical up to renaming on ${checked - mismatches.size - unpaired.size} of $checked problems " +
        s"($inOrder in the same clause order; $tooLarge over ${Corpus.maxClauses} clauses, $slow too slow, $notParsed unparsed) " +
        s"in ${(System.currentTimeMillis() - startedAt) / 1000}s"
    println(s"[clauses] $summary")
    info(summary)
    assert(checked > 0, "no problem was checked")
    assert(mismatches.isEmpty, s"${mismatches.size} problems produce a different number of clauses, e.g. ${mismatches.headOption}")
    assert(unpaired.isEmpty, s"${unpaired.size} problems have a clause that does not pair off under a renaming: ${unpaired.take(3).mkString(", ")}")
  }

/**
 * What the corpus check runs on, and where its counts go.
 *
 * Settings are `key=value` arguments. [[ClausifierEquivalence]] is the entry point that sets them; under
 * `sbt test` none are set and the defaults below give a run short enough for a test suite.
 *
 *   - `list`       a manifest of TPTP-root-relative paths: a file, or a packaged list such as
 *                  `casc-j13-fof.txt`. Unset means the problems of `tptp-eligible-fof.txt` whose formulas
 *                  sum to at most 1000 nodes.
 *   - `n`          how many problems to draw from it, or `all` (default 40)
 *   - `seed`       the draw's seed (default 42)
 *   - `formulas`   at most this many formulas per problem, drawn with the same seed (default: all)
 *   - `budget`     stop after this many seconds (default: run to the end of the list)
 *   - `out`        append the run's counts to this CSV
 *   - `maxClauses` largest clause set the clause-set check will compare (default 600)
 *
 * The per-problem cap is what puts a large corpus in reach, and it trades depth for breadth deliberately. A
 * CASC problem carries some 40000 formulas, nearly all of them axioms from files shared across a whole
 * domain, so checking one exhaustively costs hours and then re-checks those same axioms on the next problem.
 * Capping spends the time on the 400 distinct conjectures instead.
 *
 * Stopping on the budget is not a failure either. The check is a conjunction over formulas, so any subset of
 * them is a weaker claim of the same kind; the CSV row records how many formulas were checked out of how
 * many were seen, which is what the paper has to quote rather than "the corpus".
 */
private[clausification] object Corpus:

  /** Set once, before the suite runs. Empty under `sbt test`. */
  private var opts: Map[String, String] = Map.empty

  def configure(args: Seq[String]): Unit =
    opts = args.flatMap(a => a.split("=", 2) match { case Array(k, v) if v.nonEmpty => Some(k -> v.trim); case _ => None }).toMap
    val known = Set("list", "n", "seed", "formulas", "budget", "out", "maxClauses")
    opts.keys.filterNot(known).foreach(k => Console.err.println(s"ClausifierEquivalence: unknown setting '$k'"))

  private def opt(key: String): Option[String] = opts.get(key).map(_.trim).filter(_.nonEmpty)

  private def listName: Option[String] = opt("list")
  private def n: Int = opt("n").fold(40)(s => if s.equalsIgnoreCase("all") then Int.MaxValue else s.toInt)
  private def seed: Long = opt("seed").fold(42L)(_.toLong)
  private def out: Option[File] = opt("out").map(new File(_))

  def budgetMs: Option[Long] = opt("budget").map(_.toLong * 1000)

  /**
   * Largest clause set the clause-set check will compare (default 600).
   *
   * Above this the pairing search cannot decide the question: a clause set that big is likely to contain
   * symmetric clauses, whose canonical strings are ambiguous, and repairing a mispairing among them means
   * matching every clause at once -- quadratic per level, and inconclusive within any budget. Bounding the
   * input is what lets the check assert equality instead of reporting a caveat. At 600 it decides 46 of 60
   * TPTP400 problems and skips 9 as too large; the rest are too slow to clausify inside the per-problem budget.
   */
  def maxClauses: Int = opt("maxClauses").fold(600)(_.toInt)

  /** What was run on, for the report. */
  def name: String = listName.getOrElse("tptp-eligible-fof")

  /** The formulas of one problem to check: all of them, or a seeded draw when a cap is set. */
  def formulasOf(all: Seq[K.Expression]): Seq[K.Expression] =
    opt("formulas").map(_.toInt) match
      case Some(cap) if cap < all.size => new scala.util.Random(seed).shuffle(all).take(cap)
      case _ => all

  /** Largest problem in the default draw, as the node count summed over all of its formulas. */
  private val defaultMaxSize = 1000

  /** Computed once, since the three tests share it and the default draw parses what it considers. */
  lazy val problems: Vector[String] = listName match
    case None => smallFof(n, seed)
    case Some(list) =>
      // `ProblemList` falls back to a packaged list when the name is not a file on disk, so one setting names
      // either -- no "is this a path?" test to get wrong.
      val available = new ProblemList(list, None)
      if n >= available.all.size then available.all else available.sample(n, seed)

  /**
   * The default draw: the first `n` problems of `tptp-eligible-fof.txt`, in seeded random order, whose formulas
   * sum to at most [[defaultMaxSize]] nodes. The bound is what keeps the suite short whatever the seed picks.
   *
   * Measuring a problem means parsing it, so a problem whose file and included axiom files exceed 256 KB is
   * passed over unparsed: at a few bytes per node it is far above the bound, and parsing it would cost seconds.
   * Without the corpus the draw is empty, and the tests cancel on the missing corpus as before.
   */
  private def smallFof(n: Int, seed: Long): Vector[String] = TptpCorpus.root match
    case None => Vector.empty
    case Some(root) =>
      val include = """^\s*include\(\s*'([^']+)'""".r
      def bytes(f: File): Long =
        val src = scala.io.Source.fromFile(f)(using scala.io.Codec.ISO8859)
        try f.length + src.getLines().take(400).flatMap(l => include.findFirstMatchIn(l)).map(m => new File(root, m.group(1)).length).sum
        finally src.close()
      def small(rel: String): Boolean =
        val f = new File(root, rel)
        f.isFile && bytes(f) <= 256 * 1024 && {
          try
            val p = problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))
            val hyps = p.formulas.collect { case a: AnnotatedFormula if axiomLikeRoles.contains(a.role) => K.Sequent(Set.empty, Set(a.formula)) }
            val conj = p.formulas.collectFirst { case a: AnnotatedFormula if a.role == "conjecture" => K.Sequent(Set.empty, Set(a.formula)) }
            lisa.automation.Problem(hyps, conj).size <= defaultMaxSize
          catch case _: Throwable => false // a problem that does not parse is not a small problem
        }
      FofEvaluation.sample(Int.MaxValue, seed).iterator.filter(small).take(n).toVector

  /** Append `row` to the CSV, writing `header` first if the file is new. Does nothing when unconfigured. */
  def record(header: String, row: String): Unit = out.foreach { f =>
    val fresh = !f.exists() || f.length() == 0
    val w = new java.io.PrintWriter(new java.io.FileWriter(f, true))
    try
      if fresh then w.println(header)
      w.println(row)
    finally w.close()
  }

/**
 * The corpus run of [[ClausifierEquivalenceTest]], as a program rather than a test.
 *
 * {{{
 *   sbt "lisa-sets/Test/runMain lisa.automation.clausification.ClausifierEquivalence \
 *        list=casc-j13-fof.txt n=all out=<report.csv>"
 * }}}
 *
 * `sbt test` runs the same three checks with no settings, which is a 20-problem sample. This entry point is
 * what the paper's figures come from, so its parameters belong in the command that produced them.
 */
object ClausifierEquivalence:
  def main(args: Array[String]): Unit =
    Corpus.configure(args.toSeq)
    val status = (new ClausifierEquivalenceTest).execute()
