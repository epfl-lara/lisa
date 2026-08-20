package lisa.automation.superposition

import lisa.automation.Problem
import lisa.automation.clausification.CertifiedClausifier
import lisa.automation.clausification.Clausification
import lisa.maths.Quantifiers
import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._

/**
 * Discharges a first-order goal through [[Prover.proveKernel]], which clausifies it with
 * [[CertifiedClausifier.certifyClausal]], refutes the clauses and reconstructs a kernel proof. It supplies
 * [[lisa.maths.Quantifiers.existsEpsilonIff]], the clausifier's one library import, so that the sub-proof is
 * discharged against the real theorem.
 *
 * Accepts any sequent shape, either side possibly empty. The clausifier takes a single formula, so `Γ ⊢ Δ`
 * is passed as `⋀Γ ⟹ ⋁Δ` and restated back, which the kernel accepts because `isSameSequent` compares
 * exactly those two images. Cited facts fold in the same way, and free variables are implicitly universally
 * quantified, as elsewhere in Lisa.
 */
object Superpose extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic:

  /**
   * Cooperative wall-clock budget for the search, in milliseconds.
   */
  val timeoutMs: Long = 10000L

  /**
   * Given-clause cap for the search.
   */
  val maxGiven: Int = 100000

  /**
   * The library lemmas whose statements are exactly [[Clausification.libImports]], in that order.
   *  Cast to `proof.Fact` at each use; they are genuine `SetTheoryLibrary` justifications at runtime.
   */
  private def libraryLemmas = Seq(Quantifiers.existsEpsilonIff)

  /**
   * Signals a non-refutation (saturation/timeout) from the clausal prover, so `certifyClausal` unwinds.
   */
  private class NotRefuted(val reason: String) extends RuntimeException(reason)

  /**
   * Build the certified kernel proof of `⊢ sequentToFormula(goal)` from the hypothesis formulas `hypForms`
   * (each fed as an axiom `⊢ hyp`), or a failure message. The returned proof's imports are
   * `[⊢ hyp₁, …, ⊢ hypₙ] ++ Clausification.libImports` (the schematic library statement).
   */
  private def runProver(hypForms: Seq[Expression], goal: Sequent): Either[String, SCProof] =
    val conjectureFormula: Expression = sequentToFormula(goal) // `⋀Γ ⟹ ⋁Δ`, or just `⋁Δ` when `Γ` is empty
    val problem = Problem(
      hypotheses = hypForms.map(h => Sequent(Set.empty, Set(h))),
      conjecture = Some(Sequent(Set.empty, Set(conjectureFormula)))
    )
    try
      Prover.proveKernel(problem, SearchOptions(maxGiven = maxGiven, maxMillis = timeoutMs)) match
        case Right(pr) => Right(pr)
        case Left(outcome) => Left(s"Superpose could not refute the goal ($outcome).")
    catch case e: Throwable => Left(s"Superpose failed: ${e.getClass.getSimpleName}: ${e.getMessage}")

  /**
   * `Superpose(Γ ⊢ Δ)`: prove a valid first-order sequent with no cited hypothesis.
   */
  def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
    from(using lib, proof)()(bot)

  /**
   * `Superpose.from(f)(Γ ⊢ Δ)`: single cited hypothesis.
   */
  def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
    from(using lib, proof)(premise)(bot)

  /**
   * `Superpose.from(f₁, …, fₙ)(Γ ⊢ Δ)`: the cited facts are the clause set's axioms.
   */
  def from(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement =
    val botK = bot.underlying
    val hypForms: Seq[Expression] = premises.map(p => sequentToFormula(proof.getSequent(p).underlying))
    runProver(hypForms, botK) match
      case Left(msg) => proof.InvalidProofTactic(msg)
      case Right(pk) =>
        val n = premises.length
        val lemmas: Seq[proof.Fact] = libraryLemmas.asInstanceOf[Seq[proof.Fact]]
        val allImports: Seq[proof.Fact] = premises ++ lemmas
        // pk.imports = [⊢ hyp₁, …, ⊢ hypₙ] ++ libImports. Restate each cited fact (import -(i+1)) to its formula
        // `⊢ hypᵢ` (steps 0..n-1) to fill the hypothesis slots. This is where a `Γᵢ ⊢ Δᵢ` fact is folded into one
        // axiom; the library slot comes from import -(n+1). The closing `Restate` unfolds the proved
        // `⊢ ⋀Γ ⟹ ⋁Δ` back into the goal `Γ ⊢ Δ`: both sides have the same `sequentToFormula`, so it is trivial.
        val restates: Seq[SCProofStep] = hypForms.zipWithIndex.map((f, i) => Restate(Sequent(Set.empty, Set(f)), -(i + 1)))
        val subPremises: Seq[Int] = (0 until n) ++ lemmas.indices.map(j => -(n + j + 1))
        val sub = SCSubproof(pk, subPremises)
        val steps = (restates :+ sub :+ Restate(botK, n)).toIndexedSeq
        proof.ValidProofTactic(bot, steps, allImports)
