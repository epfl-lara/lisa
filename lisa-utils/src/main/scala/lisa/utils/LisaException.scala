package lisa.utils

/**
 * A Lisa exception with a source location and a user-facing diagnostic.
 */
abstract class LisaException(val message: String)(using val line: sourcecode.Line, val file: sourcecode.File) extends Exception(message):
  /**
   * Explains the error for proof diagnostics.
   */
  def showError: String

/**
 * A mistake in user code, with an overridable user-facing diagnostic.
 */
abstract class UserLisaException(message: String)(using sourcecode.Line, sourcecode.File) extends LisaException(message):
  /**
   * Displays the supplied message unless a subclass provides richer context.
   */
  def showError: String = message

/**
 * Exceptions for incorrect uses of frontend operations.
 */
object UserLisaException:
  /**
   * An invalid use of a frontend proof operation.
   */
  class InvalidProofOperationException(message: String)(using sourcecode.Line, sourcecode.File) extends UserLisaException(message)
