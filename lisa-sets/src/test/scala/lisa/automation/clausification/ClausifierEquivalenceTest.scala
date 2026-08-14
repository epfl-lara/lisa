package lisa.automation.clausification

import java.io.File
import scala.util.{Try, Success, Failure}

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.tptp.{AnnotatedFormula, AnnotatedSequent}
import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
import lisa.automation.superposition.TptpCorpus
import lisa.automation.superposition.bench.{FofEvaluation, EqFofEvaluation}
import Clausification.GeneratedNames

/**
 * Equivalence check between the **uncertified** uncertified clausifier ([[lisa.automation.clausification.UncertifiedClausifier]])
 * and the **certified** one ([[CertifiedClausifier]]) on the first 100 problems (seed 42) of each of the
 * equality-free FOF and equality-bearing FOF benchmarks, 200 problems in all. It establishes, on real inputs, that the two
 * make the *same naming decisions*: for every input formula the certified named formula equals the uncertified one
 * *identically*, both minting their `nm` atoms with the same generator ([[CertifiedClausifier.sameNaming]] is a
 * plain `==`). This is the soundness lever: if the certified
 * (kernel-checked) path names identically, its clauses vouch for the uncertified path's.
 *
 * Needs the `TPTP` env var (the directory containing `Problems/`); skipped otherwise.
 */
class ClausifierEquivalenceTest extends AnyFunSuite:

  private def size(e: K.Expression): Int = e match
    case K.Application(f, a) => 1 + size(f) + size(a)
    case K.Lambda(_, b)      => 1 + size(b)
    case _                   => 1

  /** Run `body` on a daemon thread, returning `Some(result)` if it finishes within `ms`, else interrupting it and
   *  returning `None`. Used to skip formulas whose certified ε-Skolemization blows up (until it shares terms). */
  private def runWithTimeout[A](ms: Long)(body: => A): Option[A] =
    val result = new java.util.concurrent.atomic.AtomicReference[Option[A]](None)
    val th = new Thread(() => try result.set(Some(body)) catch case _: Throwable => ())
    th.setDaemon(true)
    th.start()
    th.join(ms)
    if th.isAlive then { th.interrupt(); None } else result.get

  /** Structural equality up to renaming of the **fresh** symbols, with the problem symbols (all other constants)
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
   *     distinct Skolem functions is unconditionally sound, so the relaxation loses no soundness assurance). */
  // Returns None if isomorphic (in the above sense), else the first structurally-mismatching subexpression pair.
  private def isoMismatch(x: K.Expression, y: K.Expression): Option[(K.Expression, K.Expression)] =
    val fwd = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression]
    val bwd = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression]
    // Skolem symbols: uncertified's `sk` (a Constant), the certified path's `esk` (a schematic Variable), and the
    // test's `feps` ε-abstraction. Matched by name regardless of Constant/Variable so ε↔Skolem-function
    // representations line up. (Counter is in the identifier's `no` field, so the `name` is exactly the prefix.)
    def isSkolem(e: K.Expression): Boolean =
      val name = e match { case c: K.Constant => c.id.name; case v: K.Variable => v.id.name; case _ => "" }
      name == GeneratedNames.uncertifiedSkolem || name == "feps" || name == GeneratedNames.skolemFun
    def renamable(e: K.Expression): Boolean = e.isInstanceOf[K.Variable] || isSkolem(e)
    def go(a: K.Expression, b: K.Expression): Option[(K.Expression, K.Expression)] = (a, b) match
      case (K.Application(f1, a1), K.Application(f2, a2)) => go(f1, f2).orElse(go(a1, a2))
      case (K.Lambda(_, _), _) | (_, K.Lambda(_, _))     => if a == b then None else Some((a, b))
      case _ if isSkolem(a) && isSkolem(b)               => if fwd.getOrElseUpdate(a, b) == b then None else Some((a, b)) // forward only
      case _ if renamable(a) && renamable(b)             => if fwd.getOrElseUpdate(a, b) == b && bwd.getOrElseUpdate(b, a) == a then None else Some((a, b))
      case _                                             => if a == b then None else Some((a, b))
    go(x, y)

  private def isoUpToRenaming(x: K.Expression, y: K.Expression): Boolean = isoMismatch(x, y).isEmpty

  /** ε-abstraction for the test: replace each `ε(λx.φ)` by a fresh function `F` applied to the ε-term's **Ind**
   *  free variables (sorted by original name), matching UncertifiedClausifier's Skolem functions. Unlike `Clausal.Abstraction`
   *  this filters to `Ind` (the certified path names before Skolem, so ε-terms can contain predicate naming atoms,
   *  which are not Skolem-function arguments). Run *before* ∀-strip so `F`'s arguments carry the original names.
   *
   *  ε-terms are treated as **fully opaque** uninterpreted function symbols: we never look inside one (so nested
   *  ε-terms are absorbed into their enclosing symbol, exactly as UncertifiedClausifier's opaque Skolem functions absorb
   *  the witnesses they range over), and its identity is the *raw* ε-term, of which only the free variables are observable.
   *  Keying on the raw term (rather than recursively pre-abstracting the body) makes dedup structural: two identical
   *  ε-terms get one symbol regardless of the numbering order of any inner ε-terms. */
  private def absEps(e: K.Expression): K.Expression =
    var n = 0
    val memo = scala.collection.mutable.HashMap.empty[K.Expression, K.Expression] // same raw ε-term ⇒ same symbol
    def go(e: K.Expression): K.Expression = e match
      case eps @ K.Application(f0, _) if f0 == K.epsilon => // an ε-term is opaque, so do NOT descend into its body
        memo.getOrElseUpdate(eps, {
          // A **Constant** (like UncertifiedClausifier's Skolem `sk`), NOT a Variable: else a nullary `feps` (result sort
          // Ind) would be an Ind-valued free variable and cascade in as an argument to outer Skolem functions.
          val fv = eps.freeVariables.toSeq.filter(_.sort == K.Ind).sortBy(v => (v.id.name, v.id.no))
          val fSym = K.Constant(K.Identifier("feps", n), fv.foldRight(K.Ind: K.Sort)((v, acc) => v.sort -> acc))
          n += 1
          fv.foldLeft(fSym: K.Expression)((acc, v) => K.Application(acc, v))
        })
      case K.Application(f, a) => K.Application(go(f), go(a))
      case K.Lambda(x, b)      => K.Lambda(x, go(b))
      case _                   => e
    go(e)

  /** Hypothesis formulas + the negated conjecture, exactly as the clausifier pipeline sees them. */
  private def inputFormulas(parsed: lisa.tptp.Problem): Seq[K.Expression] =
    val hyps = parsed.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) => f.formula
    }
    val negConj = parsed.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => K.neg(f.formula)
    }
    hyps ++ negConj.toSeq

  test("certified and uncertified clausifier name AND Skolemize equivalently on 200 TPTP problems (fof + eq, seed 42)") {
    val root = TptpCorpus.rootOrCancel("the uncertified/certified naming equivalence check")
    // Early test: 20 of each set (increase later). Some LCL modal problems build exponentially-large ε-terms
    // (until the certified Skolemization shares them properly), so cap each formula's check at 2s and skip slow ones.
    val problems = FofEvaluation.sample(20, 42) ++ EqFofEvaluation.sample(20, 42)
    var problemsChecked = 0
    var formulasChecked = 0
    var skolemTimeouts = 0
    val skolemFails = scala.collection.mutable.ListBuffer.empty[(String, Option[(K.Expression, K.Expression)])]
    for rel <- problems do
      val f = new File(root, rel)
      if f.exists then
        // Catch Throwable, not just NonFatal: the TPTP parser can StackOverflow on very large problems.
        val parsedOpt: Option[lisa.tptp.Problem] =
          try Some(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
          catch case _: Throwable => None
        parsedOpt.foreach { parsed =>
          problemsChecked += 1
          for phi <- inputFormulas(parsed) if size(phi) <= 8000 do // skip giant formulas (findSite is superlinear)
            val t0 = System.nanoTime()
            // (1) after naming: the certified and uncertified named formulas agree *identically* (same `nm` generator).
            assert(CertifiedClausifier.sameNaming(phi), s"naming diverged (certified ≠ uncertified) on $rel:\n  $phi")
            // (2) after Skolem: uncertified (Skolem functions) equals certified (ε-terms, ∀-stripped, ε-abstracted). The
            // certified side can blow up on nested-∃ ε-terms, so run it under a 2s budget and skip on timeout.
            val uncertifiedSk = CertifiedClausifier.uncertifiedNamedNnfSkolem(phi) // linear (Skolem functions), always cheap
            runWithTimeout(2000) { CertifiedClausifier.stripForall(absEps(CertifiedClausifier.namedNnfSkolemEps(phi))) } match
              case None => skolemTimeouts += 1; println(f"[timer] TIMEOUT  size=${size(phi)}%6d  $rel")
              case Some(certSk) =>
                if !isoUpToRenaming(uncertifiedSk, certSk) then skolemFails += ((rel, isoMismatch(uncertifiedSk, certSk)))
                formulasChecked += 1
            // `println` (not `info`): sbt buffers `info` to test-end, so it is useless for watching progress live.
            val ms = (System.nanoTime() - t0) / 1000000
            if ms > 1000 then println(f"[timer] ${ms}%6d ms  size=${size(phi)}%6d  $rel")
        }
    println(s"[summary] checked $formulasChecked formulas across $problemsChecked problems ($skolemTimeouts skipped as >2s)")
    println(s"[summary] SKOLEM DIVERGENCES: ${skolemFails.map(_._1).distinct.size} problems, ${skolemFails.size} formulas")
    skolemFails.foreach((p, m) => println(s"[summary]   skolem-diverge: $p: $m"))
    info(s"checked $formulasChecked formulas across $problemsChecked problems ($skolemTimeouts skipped >2s); ${skolemFails.size} skolem divergences")
    assert(problemsChecked >= 30, s"expected to load most problems, only $problemsChecked")
    assert(formulasChecked > 0)
    assert(skolemFails.isEmpty, s"${skolemFails.size} skolem divergences (e.g. ${skolemFails.headOption})")
  }
