package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

private[clausification] object NnfPhase:

  def certifyNnf(problem: Problem, prover: ClausificationProver): ClausificationProof = {
    val transformedHyps = problem.hypotheses.map { h =>
      checkInterrupted()
      onSingleRight(h, "hypothesis")(toNNF(_, negated = false))
    }
    val transformed = Problem(transformedHyps, None)
    val downstream = prover(transformed)
    require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

    val restateSteps: IndexedSeq[ClausificationProofStep] =
      transformedHyps.zipWithIndex.map { case (nnfHyp, i) =>
        KernelStep(Restate(nnfHyp, problem.hypIndex(i)))
      }.toIndexedSeq
    val subproof = ClausificationSubproof(
      downstream,
      restateSteps.indices.toIndexedSeq ++ libRefs(problem.imports.size)
    )
    ClausificationProof(restateSteps :+ subproof, problem.imports ++ libImports)
  }

  /** Smart `∧` applying the boolean-constant absorption laws `⊥∧_ = ⊥`, `⊤∧a = a`. */
  private def mkAnd(a: Expression, b: Expression): Expression =
    if a == bot || b == bot then bot
    else if a == top then b
    else if b == top then a
    else and(a)(b)

  /** Smart `∨` applying the boolean-constant absorption laws `⊤∨_ = ⊤`, `⊥∨a = a`. */
  private def mkOr(a: Expression, b: Expression): Expression =
    if a == top || b == top then top
    else if a == bot then b
    else if b == bot then a
    else or(a)(b)

  /**
   * Convert a formula to negation normal form, simplifying away the boolean constants `⊤`/`⊥` via the
   * absorption laws (`mkAnd`/`mkOr`). This keeps `$true`/`$false` (which TPTP problems use as padding, e.g.
   * the modal encodings in `LCL`) out of the clauses, where they would otherwise survive as uninterpreted
   * 0-ary atoms and block resolution. Every simplification is a propositional equivalence, so the `Restate`
   * bridging the original hypothesis to its NNF in [[certifyNnf]] still discharges it — no proof change.
   */
  def toNNF(f: Expression, negated: Boolean): Expression = f match
    case `top`          => if negated then bot else top
    case `bot`          => if negated then top else bot
    case Neg(g)         => toNNF(g, !negated)
    case And(g, h)      =>
      if negated then mkOr(toNNF(g, true), toNNF(h, true))
      else mkAnd(toNNF(g, false), toNNF(h, false))
    case Or(g, h)       =>
      if negated then mkAnd(toNNF(g, true), toNNF(h, true))
      else mkOr(toNNF(g, false), toNNF(h, false))
    case Implies(g, h)  => toNNF(or(neg(g))(h), negated)
    case Iff(g, h)      =>
      // Expand directly without going through Implies, to avoid rebuilding
      // intermediate implication nodes.  The result is:
      //   (g ⟺ h)  =  (¬g_nnf ∨ h_nnf) ∧ (g_nnf ∨ ¬h_nnf)
      //  ¬(g ⟺ h)  =  (g_nnf ∧ ¬h_nnf) ∨ (¬g_nnf ∧ h_nnf)
      val gPos = toNNF(g, negated = false); val gNeg = toNNF(g, negated = true)
      val hPos = toNNF(h, negated = false); val hNeg = toNNF(h, negated = true)
      if negated then mkOr(mkAnd(gPos, hNeg), mkAnd(gNeg, hPos))
      else mkAnd(mkOr(gNeg, hPos), mkOr(gPos, hNeg))
    case Forall(x, inner) =>
      if negated then exists(x, toNNF(inner, true))
      else forall(x, toNNF(inner, false))
    case Exists(x, inner) =>
      if negated then forall(x, toNNF(inner, true))
      else exists(x, toNNF(inner, false))
    case atom => if negated then neg(atom) else atom
