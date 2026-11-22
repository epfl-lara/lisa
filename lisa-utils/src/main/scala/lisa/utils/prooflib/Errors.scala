package lisa.utils.prooflib

import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.fol.FOL.Sequent

import java.io.IOException
import java.nio.file.InvalidPathException
import java.nio.file.Path
import java.util.IdentityHashMap
import scala.io.Source
import scala.util.Using

/**
 * An expected tactic failure committed by extracting its theorem or payload.
 */
class TacticFailureException(message: String)(using sourcecode.Line, sourcecode.File) extends UserLisaException(message)

/**
 * A bug encountered during tactic execution, retaining the original exception when available.
 */
class TacticException(message: String, cause: Throwable = null)(using sourcecode.Line, sourcecode.File) extends LisaException(message):
  if cause != null then initCause(cause)
  def showError: String = s"A tactic encountered an internal error: $message"

/**
 * A theorem body that did not produce a proof.
 */
class UnimplementedProof(val name: String, val statement: Sequent)(using sourcecode.Line, sourcecode.File) extends UserLisaException("Unimplemented theorem"):
  override def showError: String = s"Theorem $name: $statement\n$message"

/**
 * A rejected definition of a user-declared symbol.
 */
class UserInvalidDefinitionException(val symbol: String, message: String)(using sourcecode.Line, sourcecode.File) extends UserLisaException(message)

/**
 * An exception recovered at a user step, with its location and admitted conclusion.
 */
case class ProofDiagnostic(exception: Exception, file: sourcecode.File, line: sourcecode.Line, conclusion: Sequent):
  /**
   * The original exception's diagnostic, without changing its classification or trace.
   */
  def message: String = exception match
    case error: LisaException => error.showError
    case error => Option(error.getMessage).getOrElse(error.getClass.getName)

  /**
   * Formats proof errors concisely and includes exception traces for internal errors.
   */
  def format: String =
    val recovery = sourceLocation(file.value, line.value)
    val cause = exception match
      case error: LisaException => sourceLocation(error.file.value, error.line.value)
      case error =>
        // A stack frame supplies only a file name. Resolve it only against the known proof source,
        // and never mistake a caller outside the recovery boundary for the cause.
        recovery.flatMap { (path, _) =>
          error.getStackTrace.iterator
            .takeWhile(frame => frame.getClassName != classOf[ProofBuilder].getName || frame.getMethodName != "recover")
            .find(frame => frame.getFileName == path.getFileName.toString && frame.getLineNumber > 0)
            .map(frame => (path, frame.getLineNumber))
        }
    val heading = exception match
      case _: UserLisaException => "Proof error"
      case _: TacticException => "Internal tactic error"
      case _ => exception.getClass.getSimpleName
    val title = s"-- $heading${cause.fold("")(location => s": ${displayLocation(location)}")} "
    val result = new StringBuilder(title + "-" * math.max(3, 80 - title.length) + "\n")
    val width = cause.fold(1)(_._2.toString.length)
    val gutter = " " * width + " |"
    cause.foreach { (path, number) =>
      readSourceLine(path, number).foreach(text => result.append(s"$number |$text\n"))
    }
    result.append(s"$gutter\n")
    message.linesIterator.foreach(text => result.append(s"$gutter $text\n"))
    if !exception.isInstanceOf[UserLisaException] then
      result.append(s"$gutter\n$gutter Trace:\n")
      val trace = new StringBuilder
      appendTrace(trace, recovery.map(_._1.getFileName.toString))
      trace.toString.linesIterator.foreach(text => result.append(s"$gutter $text\n"))
    result.toString.stripTrailing()

  private def sourceLocation(file: String, line: Int): Option[(Path, Int)] =
    if file.isEmpty || line <= 0 then None
    else
      try Some((Path.of(file).toAbsolutePath.normalize(), line))
      catch case _: InvalidPathException | _: SecurityException => None

  private def displayLocation(location: (Path, Int)): String =
    val (path, number) = location
    val displayPath =
      try
        val cwd = Path.of("").toAbsolutePath.normalize()
        if path.startsWith(cwd) then cwd.relativize(path).toString else path.toString
      catch case _: SecurityException => path.toString
    s"$displayPath:$number"

  private def readSourceLine(path: Path, line: Int): Option[String] =
    try Using.resource(Source.fromFile(path.toFile, "UTF-8"))(_.getLines().drop(line - 1).nextOption())
    catch case _: IOException | _: SecurityException => None

  private def appendTrace(result: StringBuilder, recoveryFile: Option[String]): Unit =
    val seen = new IdentityHashMap[Throwable, java.lang.Boolean]()
    def append(error: Throwable, indent: String, caption: String): Unit =
      if seen.put(error, java.lang.Boolean.TRUE) != null then result.append(s"$indent$caption[Circular reference: $error]\n")
      else
        if caption.nonEmpty then result.append(s"$indent$caption$error\n")
        val stack = error.getStackTrace
        // Stack frames contain only a file name. If no recovery frame matches, retain the full trace.
        val recovery = stack.indexWhere(frame => recoveryFile.contains(frame.getFileName) && frame.getLineNumber == line.value)
        val visible = if recovery < 0 then stack else stack.take(recovery + 1)
        visible.foreach(frame => result.append(s"$indent  at $frame\n"))
        if visible.length < stack.length then result.append(s"$indent  ... ${stack.length - visible.length} outer frames omitted\n")
        error.getSuppressed.foreach(suppressed => append(suppressed, indent + "  ", "Suppressed: "))
        Option(error.getCause).foreach(cause => append(cause, indent, "Caused by: "))
    exception match
      case error: TacticException if error.getCause != null =>
        // The wrapper marks the tactic boundary; its cause contains the actual failure trace.
        seen.put(error, java.lang.Boolean.TRUE)
        append(error.getCause, "", "Caused by: ")
        error.getSuppressed.foreach(suppressed => append(suppressed, "  ", "Suppressed: "))
      case error: TacticException =>
        result.append(s"$error\n")
        append(error, "", "")
      case error => append(error, "", "")
