package lisa.hol.extractor

import java.io.{ByteArrayOutputStream, File, RandomAccessFile}
import java.nio.charset.StandardCharsets.UTF_8

/** Read buffered UTF-8 lines while retaining exact byte offsets for random access. */
private[extractor] final class TraceReader(path: File, bufferSize: Int = 64 * 1024) extends AutoCloseable:
  require(bufferSize > 0)

  private val file = new RandomAccessFile(path, "r")
  private val buffer = new Array[Byte](bufferSize)
  private var next = 0
  private var limit = 0
  private var offset = 0L
  private var readBytes = 0L

  /** Count bytes fetched into the buffer, including read-ahead and rereads. */
  def bytesRead: Long = readBytes

  def length: Long = file.length()

  /** Return the byte offset of the next unread character. */
  def position: Long = offset

  /** Resume at a byte offset, reusing buffered bytes when possible. */
  def seek(position: Long): Unit =
    require(position >= 0 && position <= length, s"Invalid trace offset: $position")
    val start = offset - next
    if limit >= 0 && position >= start && position < start + limit then
      next = (position - start).toInt
      offset = position
    else
      file.seek(position)
      offset = position
      next = 0
      limit = 0

  private def hasByte: Boolean =
    if next == limit then
      limit = file.read(buffer)
      if limit > 0 then readBytes += limit
      next = 0
    next < limit

  private[extractor] def peekByte: Int = if hasByte then buffer(next) & 0xff else -1

  private[extractor] def readByte(): Int =
    val value = peekByte
    if value >= 0 then
      next += 1
      offset += 1
    value

  /** Skip the remaining line without decoding or retaining its payload. */
  def skipLine(): Unit =
    var ended = false
    while !ended && hasByte do
      val start = next
      while next < limit && buffer(next) != '\n' && buffer(next) != '\r' do next += 1
      offset += next - start
      if next < limit then
        val separator = readByte()
        if separator == '\r' && peekByte == '\n' then readByte()
        ended = true

  /** Seek to the first complete line beginning at or after a byte offset. */
  def seekLine(position: Long): Unit =
    if position == 0 then seek(0)
    else
      seek(position - 1)
      readByte() match
        case 10 => ()
        case 13 => if peekByte == '\n' then readByte()
        case _ => skipLine()

  /** Read a line without its LF, CRLF, or CR terminator; return None at EOF. */
  def readLine(): Option[String] =
    if !hasByte then None
    else
      val line = new ByteArrayOutputStream
      var ended = false
      while !ended && hasByte do
        val start = next
        while next < limit && buffer(next) != '\n' && buffer(next) != '\r' do next += 1
        line.write(buffer, start, next - start)
        offset += next - start

        // Consume the terminator, including a CRLF split across buffer fills.
        if next < limit then
          val separator = buffer(next)
          next += 1
          offset += 1
          if separator == '\r' && hasByte && buffer(next) == '\n' then
            next += 1
            offset += 1
          ended = true

      Some(line.toString(UTF_8))

  /** Close the underlying file. */
  def close(): Unit = file.close()
