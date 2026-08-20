package lisa.automation.clausification

import lisa.utils.K.{_, given}
import lisa.automation.Problem
import Clausification.*

/**
 * Universal-quantifier stripping: replace each `∀x. …` by its body with `x` at a fresh clause variable `w`,
 * leaving [[DistributePhase]] a quantifier-free matrix. Quantifiers are not necessarily at the root
 * [[provePrenex]] applies `LeftForall` at each `∀` in place, walking the formula's
 * tree and mirroring its connectives, which costs a proof linear in `|φ|`.
 */
private[clausification] object PrenexPhase:

  /** For each axiom containing a `∀` anywhere in its tree, strip all universals, instantiating each at a fresh
    * clause variable `w` (pre-order) via `LeftForall`. Certifies the derivation of the quantifier-free matrix
    * via [[provePrenex]]. */
  def certifyPrenex(problem: Problem, prover: ClausificationProver): ClausificationProof = {
    require(problem.conjecture.isEmpty, "certifyPrenex expects a conjecture-free problem (consumed by certifyNegated)")
    val counter = Counter()
    val hypotheses = problem.hypotheses.toIndexedSeq
    val n = hypotheses.size

    val steps      = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val matrices   = scala.collection.mutable.ArrayBuffer.empty[Sequent]
    val matrixRefs = scala.collection.mutable.ArrayBuffer.empty[Int]
    for i <- 0 until n do
      checkInterrupted()
      val ax  = hypotheses(i)
      val phi = singleRightFormula(ax, "axiom")
      if !hasForall(phi) then
        matrices += ax
        matrixRefs += -(i + 1)
      else
        // The step derives `() ⊢ matrix` from the axiom import, instantiating each stripped `∀` at a fresh
        // clause variable `w`; the matrix it arrives at is the axiom handed downstream.
        val (sub, matrixAx) = provePrenex(ax, -(i + 1), counter)
        steps += sub
        matrices += matrixAx
        matrixRefs += steps.size - 1

    val newProblem = Problem(matrices.toList, None, problem.frozen)
    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    steps += ClausificationSubproof(downstream, matrixRefs.toIndexedSeq ++ libRefs(n))
    ClausificationProof(steps.toIndexedSeq, hypotheses ++ libImports)
  }

  def hasForall(f: Expression): Boolean = f match
    case Forall(_, _) => true
    case And(g, h)    => hasForall(g) || hasForall(h)
    case Or(g, h)     => hasForall(g) || hasForall(h)
    case Neg(g)       => hasForall(g)
    case _            => false

  /** Build a kernel proof of `() ⊢ matrix` from the imported `() ⊢ phi`, where `matrix` is `phi` with every
    * `∀x._` stripped and `x` replaced by a fresh clause variable `w` drawn from `counter`, and return it with
    * that matrix. Walks `phi`'s tree, mirroring its connectives and using `LeftForall` at each universal to
    * instantiate it, then `Cut`s against `imported`.
    *
    * Proof size is linear in `|phi|`. */
  def provePrenex(imported: Sequent, premise: Int, counter: Counter): (SCSubproof, Sequent) = {
    val phi = singleRightFormula(imported, "imported (prenex source)")

    val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
    def emit(s: SCProofStep): Int = { steps += s; steps.size - 1 }

    /** `Hypothesis(e ⊢ e)`, the derivation of a subformula whose matrix is itself. */
    def hypothesis(e: Expression): Int = emit(Hypothesis(e |- e, e))

    // Builds steps with conclusion `orig ⊢ matrixOf(orig)` and returns the step index, or `None` when `orig`
    // holds no ∀ and so needs no derivation at all: its matrix is itself, and the parent emits the one
    // `Hypothesis` where it needs an index.
    def go(orig: Expression): Option[Int] = orig match
      case Forall(x, body) =>
        val v = Variable(Identifier(GeneratedNames.clauseVar, counter.next()), Ind)
        val bodySub  = substituteVariablesOpti(body, Map(x -> v))
        val innerIdx = go(bodySub).getOrElse(hypothesis(bodySub))
        val innerM   = steps(innerIdx).bot.right.head
        // LeftForall(b, t1, phi, x, t): from `Γ, body[x:=v] ⊢ Δ` derive `Γ, ∀x.body ⊢ Δ`.
        Some(emit(LeftForall(orig |- innerM, innerIdx, body, x, v)))

      case And(g, h) =>
        (go(g), go(h)) match
          case (None, None) => None
          case (og, oh) =>
            val gIdx = og.getOrElse(hypothesis(g))
            val hIdx = oh.getOrElse(hypothesis(h))
            val mg = steps(gIdx).bot.right.head
            val mh = steps(hIdx).bot.right.head
            val mAnd = and(mg)(mh)
            val gWithAnd = emit(LeftAnd(orig |- mg, gIdx, g, h))
            val hWithAnd = emit(LeftAnd(orig |- mh, hIdx, g, h))
            Some(emit(RightAnd(orig |- mAnd, Seq(gWithAnd, hWithAnd), Seq(mg, mh))))

      case Or(g, h) =>
        (go(g), go(h)) match
          case (None, None) => None
          case (og, oh) =>
            val gIdx = og.getOrElse(hypothesis(g))
            val hIdx = oh.getOrElse(hypothesis(h))
            val mg = steps(gIdx).bot.right.head
            val mh = steps(hIdx).bot.right.head
            val mOr = or(mg)(mh)
            // RightOr lifts each branch to the disjunctive matrix; LeftOr combines them.
            val gWithOr = emit(RightOr(g |- mOr, gIdx, mg, mh))
            val hWithOr = emit(RightOr(h |- mOr, hIdx, mg, mh))
            Some(emit(LeftOr(orig |- mOr, Seq(gWithOr, hWithOr), Seq(g, h))))

      case _ => None // NNF leaves: atoms and negated atoms, which hold no ∀

    val phiToMatrixIdx = go(phi).getOrElse(hypothesis(phi))
    val matrix = steps(phiToMatrixIdx).bot.right.head
    // Cut: from `() ⊢ phi` (import 0) and `phi ⊢ matrix` derive `() ⊢ matrix`.
    emit(Cut(() |- matrix, -1, phiToMatrixIdx, phi))

    (SCSubproof(SCProof(steps.toIndexedSeq, IndexedSeq(imported)), IndexedSeq(premise)), () |- matrix)
  }
