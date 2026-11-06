package lisa.hol.extractor

import java.io.{ByteArrayOutputStream, File}
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.charset.{Charset, StandardCharsets}
import java.nio.file.StandardOpenOption.READ
import scala.util.Using
import scala.util.control.NonFatal

/**
 * Read and skip lines by byte offset, decoding UTF-8 only when a line is requested.
 */
private[extractor] final class TraceReader(path: File, bufferSize: Int = 64 * 1024) extends AutoCloseable:
  require(bufferSize > 0)

  private val file = FileChannel.open(path.toPath, READ)
  private val buffer = ByteBuffer.allocate(bufferSize)
  buffer.limit(0)
  private var bufferStart = 0L
  private var readBytes = 0L

  // Traces are immutable while open, so the file size also determines EOF.
  val length: Long = file.size()

  /**
   * Count bytes fetched into the buffer, including read-ahead and rereads.
   */
  def bytesRead: Long = readBytes

  /**
   * Return the byte offset of the next unread byte.
   */
  def position: Long = bufferStart + buffer.position()

  /**
   * Resume at a byte offset, reusing buffered bytes when possible.
   */
  def seek(position: Long): Unit =
    require(position >= 0 && position <= length, s"Invalid trace offset: $position")
    if position >= bufferStart && position <= bufferStart + buffer.limit() then buffer.position((position - bufferStart).toInt)
    else
      bufferStart = position
      buffer.limit(0)

  private def hasByte: Boolean =
    if !buffer.hasRemaining && position < length then
      bufferStart = position
      buffer.clear()
      val count = file.read(buffer, bufferStart)
      buffer.flip()
      if count > 0 then readBytes += count
    buffer.hasRemaining

  private[extractor] def peekByte: Int = if hasByte then buffer.get(buffer.position()) & 0xff else -1

  private[extractor] def readByte(): Int =
    if hasByte then buffer.get() & 0xff else -1

  /**
   * Consume at most the requested bytes, stopping before the line terminator.
   */
  private def consumeLine(output: Option[ByteArrayOutputStream], maxBytes: Long = Long.MaxValue): Unit =
    var remaining = maxBytes
    while remaining > 0 && hasByte do
      val start = buffer.position()
      val limit = start + math.min(remaining, buffer.remaining().toLong).toInt
      var end = start
      while end < limit && buffer.get(end) != '\n' && buffer.get(end) != '\r' do end += 1
      output.foreach(_.write(buffer.array(), start, end - start))
      buffer.position(end)
      remaining -= end - start
      if end < limit then return

  private def collectLine(maxBytes: Long, charset: Charset): String =
    val output = new ByteArrayOutputStream
    consumeLine(Some(output), maxBytes)
    output.toString(charset)

  private def skipTerminator(): Unit =
    if readByte() == '\r' && peekByte == '\n' then readByte()

  /**
   * Skip the remaining line without decoding or retaining its payload.
   */
  def skipLine(): Unit =
    consumeLine(None)
    skipTerminator()

  /**
   * Read an ASCII header fragment, leaving any line terminator unconsumed.
   */
  private[extractor] def readPrefix(maxBytes: Int): String =
    require(maxBytes > 0)
    collectLine(maxBytes, StandardCharsets.US_ASCII)

  /**
   * Seek to the first complete line beginning at or after a byte offset.
   */
  def seekLine(position: Long): Unit =
    require(position >= 0 && position <= length, s"Invalid trace offset: $position")
    if position == 0 then seek(0)
    else
      seek(position - 1)
      readByte() match
        case '\n' => ()
        case '\r' => if peekByte == '\n' then readByte()
        case _ => skipLine()

  /**
   * Read a line without its LF, CRLF, or CR terminator; return None at EOF.
   */
  def readLine(): Option[String] =
    if !hasByte then None
    else
      val line = collectLine(Long.MaxValue, StandardCharsets.UTF_8)
      skipTerminator()
      Some(line)

  /**
   * Close the underlying file.
   */
  def close(): Unit = file.close()

private[extractor] object TraceReader:
  /**
   * Open two readers; close the first if opening the second fails.
   */
  def openPair(first: File, second: File): (TraceReader, TraceReader) =
    val reader = new TraceReader(first)
    try reader -> new TraceReader(second)
    catch case NonFatal(error) => Using.resource(reader)(_ => throw error)
