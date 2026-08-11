package lisa.automation.superposition

import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib.*

import lisa.automation.clausification.{Clausification, CertifiedClausifier}
import lisa.maths.Quantifiers

/**
 * The `Superpose` proof tactic: discharge a first-order goal with the certified superposition prover.
 *
 * It clausifies the goal (negate → NNF → Skolemize → prenex → distribute) with
 * [[CertifiedClausifier.certifyClausal]], refutes the clause set with the DISCOUNT superposition loop
 * ([[Clausal.proveOutcome]]), and reconstructs a kernel proof of the goal. The reconstruction leans on five
 * library lemmas — [[lisa.maths.Quantifiers.existsEpsilonIff]] and the four `forall{And,Or}{Left,Right}`
 * prenex laws — whose schematic statements are exactly the clausifier's [[Clausification.libImports]]; the
 * tactic supplies them as the sub-proof's imports, so they are discharged against the real theorems.
 *
 * ==Scope==
 * Any sequent shape, `Γ ⊢ Δ`, both sides possibly empty. The clausifier takes a single conjecture *formula*,
 * so the goal is passed through [[sequentToFormula]] (`⋀Γ ⟹ ⋁Δ`, and just `⋁Δ` when `Γ` is empty) and the
 * proof of `⊢ ⋀Γ ⟹ ⋁Δ` is turned back into `Γ ⊢ Δ` by one closing `Restate` — trivially valid, since the
 * kernel's `isSameSequent` compares exactly these two sequents' `sequentToFormula` images, which are the
 * same expression. Cited facts (`Superpose.from(f₁, …, fₙ)`) are folded the same way, so a hypothesis of any
 * shape becomes one axiom of the clause set. Free variables are implicitly universally quantified, as
 * everywhere in Lisa: the clausifier closes them before negating and reinstantiates them at the end.
 */
object Superpose extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic:

  /** Cooperative wall-clock budget for the search, in milliseconds. */
  val timeoutMs: Long = 10000L

  /** Given-clause cap for the search. */
  val maxGiven: Int = 100000

  /** The five library lemmas whose statements are exactly [[Clausification.libImports]], in that order.
   *  Cast to `proof.Fact` at each use — they are genuine `SetTheoryLibrary` justifications at runtime. */
  private def libraryLemmas = Seq(
    Quantifiers.existsEpsilonIff,
    Quantifiers.forallAndLeft, Quantifiers.forallAndRight,
    Quantifiers.forallOrLeft, Quantifiers.forallOrRight)

  /** Signals a non-refutation (saturation/timeout) from the clausal prover, so `certifyClausal` unwinds. */
  private class NotRefuted(val reason: String) extends RuntimeException(reason)

  /**
   * Build the certified kernel proof of `⊢ sequentToFormula(goal)` from the hypothesis formulas `hypForms`
   * (each fed as an axiom `⊢ hyp`), or a failure message. The returned proof's imports are
   * `[⊢ hyp₁, …, ⊢ hypₙ] ++ Clausification.libImports` (the five schematic library statements).
   */
  private def runProver(hypForms: Seq[Expression], goal: Sequent): Either[String, SCProof] =
    val conjectureFormula: Expression = sequentToFormula(goal) // `⋀Γ ⟹ ⋁Δ`, or just `⋁Δ` when `Γ` is empty
    val problem = Clausification.Problem(
      hypotheses = hypForms.map(h => Sequent(Set.empty, Set(h))),
      conjecture = Some(Sequent(Set.empty, Set(conjectureFormula)))
    )
    val prover: Clausification.Problem => SCProof = p =>
      Clausal.proveOutcome(p, maxGiven = maxGiven, maxMillis = timeoutMs) match
        case Right(pr)     => pr
        case Left(outcome) => throw new NotRefuted(outcome.toString)
    try Right(CertifiedClausifier.certifyClausal(problem, prover))
    catch
      case nr: NotRefuted => Left(s"Superpose could not refute the goal (${nr.reason}).")
      case e: Throwable   => Left(s"Superpose failed: ${e.getClass.getSimpleName}: ${e.getMessage}")

  /** `Superpose(Γ ⊢ Δ)`: prove a valid first-order sequent with no cited hypothesis. */
  def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
    from(using lib, proof)()(bot)

  /** `Superpose.from(f)(Γ ⊢ Δ)`: single cited hypothesis. */
  def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
    from(using lib, proof)(premise)(bot)

  /** `Superpose.from(f₁, …, fₙ)(Γ ⊢ Δ)`: the cited facts are the clause set's axioms. */
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
        // `⊢ hypᵢ` (steps 0..n-1) to fill the hypothesis slots — this is where a `Γᵢ ⊢ Δᵢ` fact is folded into one
        // axiom; the library slots come from imports -(n+1)..-(n+5). The closing `Restate` unfolds the proved
        // `⊢ ⋀Γ ⟹ ⋁Δ` back into the goal `Γ ⊢ Δ`: both sides have the same `sequentToFormula`, so it is trivial.
        val restates: Seq[SCProofStep] = hypForms.zipWithIndex.map((f, i) => Restate(Sequent(Set.empty, Set(f)), -(i + 1)))
        val subPremises: Seq[Int] = (0 until n) ++ lemmas.indices.map(j => -(n + j + 1))
        val sub = SCSubproof(pk, subPremises)
        val steps = (restates :+ sub :+ Restate(botK, n)).toIndexedSeq
        proof.ValidProofTactic(bot, steps, allImports)
