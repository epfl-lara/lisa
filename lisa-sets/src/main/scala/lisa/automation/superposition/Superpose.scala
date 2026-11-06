package lisa.automation.superposition

import lisa.automation.Problem
import lisa.maths.Quantifiers
import lisa.kernel.proof as Kernel
import lisa.utils.K
import lisa.utils.fol.{FOL => F}
import lisa.utils.kernel.ProofCertificate
import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofHelpers.{SequentTactic, PremiseSequentTactic}

import scala.util.control.NonFatal

/** Reconstruct a linear certificate, check it, then discharge its imports against the cited facts. */
object Superpose extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  val timeoutMs: Long = 10000L
  val maxGiven: Int = 100000

  private def runProver(hypotheses: Seq[K.Expression], goal: K.Sequent): Either[String, ProofCertificate] =
    val problem = Problem(
      hypotheses.map(formula => K.Sequent(Set.empty, Set(formula))),
      Some(K.Sequent(Set.empty, Set(K.sequentToFormula(goal))))
    )
    try
      Prover.proveKernel(problem, SearchOptions(maxGiven = maxGiven, maxMillis = timeoutMs))
        .left.map(outcome => s"Superpose could not refute the goal ($outcome).")
    catch case NonFatal(error) => Left(s"Superpose failed: ${error.getClass.getSimpleName}: ${error.getMessage}")

  protected def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(
      conclusion: F.Sequent,
      premises: Seq[Thm]
  ): ProofJudgement =
    given Kernel.Theory = library.theory
    val hypotheses = premises.map(p => K.sequentToFormula(p.kernel.statement))
    val imports = premises.map(_.kernel) :+ Quantifiers.existsEpsilonIff.kernel
    val result = runProver(hypotheses, conclusion.underlying).flatMap: certificate =>
      if certificate.imports.size != imports.size then Left("Superpose produced an unexpected import list.")
      else
        certificate.check.left.map(_.toString).flatMap: checked =>
          certificate.imports.zip(imports).foldLeft(Right(checked): Either[String, Kernel.Thm]):
            case (result, (expected, actual)) =>
              result.flatMap: current =>
                Kernel.Restate(expected, actual).left.map(_.toString)
                  .flatMap(justification => Kernel.Discharge(current, justification).left.map(_.toString))
          .flatMap: discharged =>
            if discharged.assumptions.nonEmpty then Left("Superpose left unresolved certificate imports.")
            else Kernel.Restate(conclusion.underlying, discharged).left.map(_.toString)
    result match
      case Right(theorem) => ProofJudgement(Thm(conclusion, theorem))
      case Left(message) => ProofCarrier(Set(SoftError(message, file, line)), conclusion, None, ())
