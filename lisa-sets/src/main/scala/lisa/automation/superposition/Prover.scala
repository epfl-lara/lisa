package lisa.automation.superposition

import lisa.automation.Problem
import lisa.automation.clausification.CertifiedClausifier
import lisa.automation.clausification.Clausification
import lisa.automation.clausification.UncertifiedClausifier
import lisa.tptp.AnnotatedFormula
import lisa.tptp.AnnotatedSequent
import lisa.tptp.KernelParser.axiomLikeRoles
import lisa.tptp.TptpProblem
import lisa.utils.K

import scala.collection.mutable

/**
 * The solver's front end: three entry points, one problem representation, one difference between them.
 *
 * All three take an **unclausified** [[Problem]] — hypotheses plus an optional conjecture — and every parameter
 * beyond it lives in [[SearchOptions]]. What they differ in is the kind of justification asked for, which is
 * also what picks the clausifier:
 *
 *   - [[solve]] wants none, so it clausifies with [[UncertifiedClausifier]] and returns the verdict;
 *   - [[proveKernel]] wants a Lisa kernel proof, so it clausifies with [[CertifiedClausifier]], which builds
 *     the clausification half of the proof around the refutation;
 *   - [[proveTstp]] wants a TSTP derivation, which needs no kernel justification of the clausification, so it
 *     too clausifies uncertified and keeps the clause origins the derivation cites.
 *
 * ==The contract on a proof==
 * Both proving entry points return a proof of `problem`'s goal — the conjecture sequent, or `⊢` when there is
 * none — whose imports are `problem.hypotheses`, pointwise and in order, followed by
 * [[Clausification.libImports]]. A caller discharges the library tail against the real theorems; see
 * [[Superpose]].
 */
object Prover:

  /**
   * A refutation ready to be rendered as TSTP: the clausifier clauses, each tagged with the index of the input
   * formula it came from, and the prover's success, which carries the derivation. The clauses hold the *first*
   * bank ids, in this order, which is what the printed derivation's leaf naming indexes on.
   *
   * `axioms` are the hypotheses SInE kept, as indices into the *caller's* hypothesis list, in order. The
   * clause origins index into `axioms ++ [conjecture]`, so a printer maps an origin through it to name the
   * input formula a clause came from.
   */
  final case class TstpRefutation(clauses: IndexedSeq[(K.Sequent, Int)], success: Clausal.Outcome.Success, axioms: IndexedSeq[Int])

  /**
   * A parsed TPTP problem as a [[Problem]]: the axiom-like roles become LHS-free hypotheses and the
   * `conjecture`, if there is one, the conjecture. The single conversion from TPTP into the representation the
   * three entry points take.
   *
   * The problem's distinct objects are pairwise distinct by definition, and that is part of what the input
   * *says*, so their disequalities join the hypotheses here rather than being bolted on further down: they
   * then reach every entry point, get ordinary clause origins, and are clausified like anything else.
   * [[TptpProblem.distinctObjects]] is what the parser recorded; nothing here inspects a constant's name.
   */
  def fromTptp(p: TptpProblem): Problem =
    val hyps = p.formulas.collect {
      case f: AnnotatedFormula if axiomLikeRoles.contains(f.role) => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if axiomLikeRoles.contains(s.role) => s.sequent
    }
    val conj = p.formulas.collectFirst {
      case f: AnnotatedFormula if f.role == "conjecture" => K.Sequent(Set.empty, Set(f.formula))
      case s: AnnotatedSequent if s.role == "conjecture" => s.sequent
    }
    Problem(hyps ++ distinctnessAxioms(p.distinctObjects), conj)

  /**
   * `oᵢ ≠ oⱼ` for every pair of `objects`, as the sequent `oᵢ = oⱼ ⊢`. Quadratic in the number of distinct
   * objects, which is what pairwise distinctness costs; TPTP problems carrying many of them pay for it.
   */
  private def distinctnessAxioms(objects: IndexedSeq[K.Expression]): IndexedSeq[K.Sequent] =
    for i <- objects.indices; j <- (i + 1) until objects.size
    yield K.Sequent(Set(K.equality(objects(i))(objects(j))), Set.empty)

  /**
   * The verdict, with no proof of any kind built.
   */
  def solve(problem: Problem, opts: SearchOptions = SearchOptions()): Clausal.Outcome =
    sineSolve(problem, opts) { p1 =>
      olSolve(p1, opts) { p2 =>
        val (clausal, origins) = UncertifiedClausifier.clausalProblemWithOrigins(p2)
        Clausal.solve(clausal, opts, goalClauses(p2, origins))
      }
    }

  /**
   * A Lisa kernel proof of `problem`'s goal, or the verdict that stopped it. See the contract above.
   */
  def proveKernel(problem: Problem, opts: SearchOptions = SearchOptions()): Either[Clausal.Outcome, K.SCProof] =
    // `certifyClausal` calls the prover from *inside* the clausification pipeline, so a non-refutation cannot
    // be returned from there; it is thrown and caught here, which is the whole extent of the exception.
    try
      Right(sineKernel(problem, opts) { p1 =>
        olKernel(p1, opts) { p2 =>
          CertifiedClausifier.certifyClausal(
            p2,
            clausal =>
              Clausal.prove(clausal, opts) match
                case Right(proof) => proof
                case Left(outcome) => throw new NotRefuted(outcome)
          )
        }
      })
    catch case nr: NotRefuted => Left(nr.outcome)

  /**
   * A refutation in the form the TSTP printer needs, or the verdict that stopped it.
   */
  def proveTstp(problem: Problem, opts: SearchOptions = SearchOptions()): Either[Clausal.Outcome, TstpRefutation] =
    sineTstp(problem, opts) { p1 =>
      olTstp(p1, opts) { p2 =>
        val (clausal, origins) = UncertifiedClausifier.clausalProblemWithOrigins(p2)
        Clausal.solve(clausal, opts, goalClauses(p2, origins)) match
          case success: Clausal.Outcome.Success =>
            Right(TstpRefutation(clausal.hypotheses.toIndexedSeq.zip(origins), success, p2.hypotheses.indices.toIndexedSeq))
          case other => Left(other)
      }
    }

  /**
   * The clauses that came from the negated conjecture: their origin is the hypothesis count, since the
   * clausifier appends `¬conjecture` as the last hypothesis. Goal-directed clause selection biases toward
   * them; the set is empty for a conjecture-free problem.
   */
  private def goalClauses(problem: Problem, origins: IndexedSeq[Int]): Set[Int] =
    origins.zipWithIndex.collect { case (origin, i) if origin == problem.hypotheses.size => i }.toSet

  // ── preprocessing: SInE, then orthologic ───────────────────────────────────────────────────────────────
  //
  // Both run before clausification, and each is written once per entry point. The three copies differ only in
  // what they owe the caller afterwards -- nothing, a kernel proof, or a TSTP derivation.
  //
  // SInE only ever *removes* hypotheses, so it is justified by nothing at all: the kernel copy widens the
  // proof's import list back to the caller's, and the TSTP copy renumbers the surviving axioms. Orthologic
  // rewrites every formula to an OL-equal one, which `Restate` discharges, so its kernel copy is one step per
  // hypothesis plus one for the goal.

  /**
   * Which hypotheses SInE keeps, as ascending indices into `p.hypotheses`; all of them when it does not run.
   */
  private def sineKeep(p: Problem, opts: SearchOptions): IndexedSeq[Int] =
    val all = p.hypotheses.indices.toIndexedSeq
    opts.sine.flatMap(cfg => Sine.selection(p, cfg)) match
      case Some(keep) => all.filter(keep)
      case None => all

  private def prune(p: Problem, keep: IndexedSeq[Int]): Problem =
    val hyps = p.hypotheses.toIndexedSeq
    Problem(keep.map(hyps), p.conjecture, p.frozen)

  /**
   * `p` with every hypothesis and the conjecture replaced by its orthologic normal form. The clausifiers
   * η-expand their input, which is what `reducedNNFForm`'s η-contracted output needs downstream.
   */
  private def olNormalise(p: Problem): Problem =
    def ol(s: K.Sequent): K.Sequent = K.Sequent(s.left.map(K.reducedNNFForm), s.right.map(K.reducedNNFForm))
    Problem(p.hypotheses.map(ol), p.conjecture.map(ol), p.frozen)

  /**
   * The sequent a proof of `p` must conclude: its conjecture, or `⊢` when it has none.
   */
  private def goalSequent(p: Problem): K.Sequent =
    p.conjecture.getOrElse(K.Sequent(Set.empty, Set.empty))

  private def sineSolve(p: Problem, opts: SearchOptions)(next: Problem => Clausal.Outcome): Clausal.Outcome =
    next(prune(p, sineKeep(p, opts)))

  private def olSolve(p: Problem, opts: SearchOptions)(next: Problem => Clausal.Outcome): Clausal.Outcome =
    next(if opts.orthologic then olNormalise(p) else p)

  private def sineTstp(p: Problem, opts: SearchOptions)(next: Problem => Either[Clausal.Outcome, TstpRefutation]): Either[Clausal.Outcome, TstpRefutation] =
    val keep = sineKeep(p, opts)
    next(prune(p, keep)).map(r => r.copy(axioms = r.axioms.map(keep))) // renumber onto the caller's list

  private def olTstp(p: Problem, opts: SearchOptions)(next: Problem => Either[Clausal.Outcome, TstpRefutation]): Either[Clausal.Outcome, TstpRefutation] =
    // Nothing to record: a TSTP derivation cites clauses back to input formulas, and normalisation happens
    // between the two, exactly as it did when the clausifier applied it internally.
    next(if opts.orthologic then olNormalise(p) else p)

  private def sineKernel(p: Problem, opts: SearchOptions)(next: Problem => K.SCProof): K.SCProof =
    val keep = sineKeep(p, opts)
    if keep.size == p.hypotheses.size then next(p)
    else widenImports(next(prune(p, keep)), p.hypotheses.toIndexedSeq, keep)

  private def olKernel(p: Problem, opts: SearchOptions)(next: Problem => K.SCProof): K.SCProof =
    if !opts.orthologic then next(p)
    else
      val inner: K.SCProof = next(olNormalise(p))
      val n: Int = p.hypotheses.size
      val steps = scala.collection.mutable.ArrayBuffer.empty[K.SCProofStep]
      // Each normalised hypothesis is OL-equal to the original it replaced, which is exactly what `Restate`
      // checks; the library imports past `n` are untouched and pass straight through.
      val premises: Seq[Int] = inner.imports.indices.map { i =>
        if i >= n then -(i + 1)
        else { steps += K.Restate(inner.imports(i), -(i + 1)); steps.length - 1 }
      }
      steps += K.SCSubproof(inner, premises)
      steps += K.Restate(goalSequent(p), steps.length - 1) // the subproof concludes the *normalised* goal
      K.SCProof(steps.toIndexedSeq, p.hypotheses.toIndexedSeq ++ inner.imports.drop(n))

  /**
   * Present `inner`, whose imports are the SInE-kept hypotheses followed by the library ones, as a proof over
   * the caller's full hypothesis list `all`: one subproof, each premise naming the slot its import came from.
   * No step justifies anything — dropping a hypothesis needs none — so this only renumbers.
   */
  private[superposition] def widenImports(inner: K.SCProof, all: IndexedSeq[K.Sequent], keep: IndexedSeq[Int]): K.SCProof =
    val n: Int = keep.size
    val premises: Seq[Int] = inner.imports.indices.map { i =>
      if i < n then -(keep(i) + 1) //                  a kept hypothesis, at its slot in the full list
      else -(all.size + (i - n) + 1) //                a library import, after the hypotheses and in order
    }
    K.SCProof(IndexedSeq(K.SCSubproof(inner, premises)), all ++ inner.imports.drop(n))

  // ── internals ──────────────────────────────────────────────────────────────────────────────────────────

  /**
   * Thrown by the inner prover when the search does not refute, and caught by [[proveKernel]].
   */
  private final class NotRefuted(val outcome: Clausal.Outcome) extends RuntimeException(s"not refuted: $outcome")
