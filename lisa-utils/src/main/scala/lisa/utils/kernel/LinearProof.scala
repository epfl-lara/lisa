package lisa.utils.kernel

import lisa.kernel.proof.Sequent
import lisa.kernel.proof.Thm

sealed trait CheckError extends Exception
case object EmptyProofError extends CheckError
case class ForwardReferenceError(idx: Int) extends CheckError
case class InvalidImportError(idx: Int) extends CheckError

case class LinearProof(
  steps: Array[ProofStep],
  imports: Array[Sequent]
):
  val importSteps: Array[ProofStep] = imports.map(Assume(_))

  def check: Either[CheckError, Thm] = 
    var idx = 0
    var lastError: CheckError = null
    var last: Thm = null

    val checked = new Array[Thm](steps.length)

    while idx < steps.length do
      val step = steps(idx)
      val result = checkOne(step, idx, checked, imports)

      result match
        case Left(error) =>
          lastError = error
          last = null
        case Right(thm) =>
          lastError = null
          last = thm
          checked(idx) = thm

      idx += 1

    if last eq null then
      Left(EmptyProofError)
    else if lastError ne null then
      Left(lastError)
    else
      Right(last)

  extension (idx: Int) private def asImport: Int = -idx - 1

  private def checkOne(
    step: ProofStep,
    idx: Int,
    checked: Array[Thm],
    imports: Array[Sequent]
  ): Either[CheckError, Thm] = 
    val fwdRef = step.premises.find(p => p >= idx)
    val invalidImport = step.premises.find(p => p.asImport >= imports.length)

    if fwdRef.isDefined then
      Left(ForwardReferenceError(fwdRef.get))
    else if invalidImport.isDefined then
      Left(InvalidImportError(invalidImport.get))
    else
      step match
        case _ => ???
