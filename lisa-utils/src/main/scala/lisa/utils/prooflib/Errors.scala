package lisa.utils.prooflib

sealed trait ProofError:
  def message: String
  def file: sourcecode.File
  def line: sourcecode.Line

case class SoftError(message: String, file: sourcecode.File, line: sourcecode.Line) extends ProofError
case class FatalError(message: String, file: sourcecode.File, line: sourcecode.Line) extends ProofError
