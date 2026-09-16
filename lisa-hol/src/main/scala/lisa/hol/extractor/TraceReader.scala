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

  /** Return the byte offset of the next unread character. */
  def position: Long = offset

  /** Resume reading at the given byte offset and discard buffered data. */
  def seek(position: Long): Unit =
    file.seek(position)
    offset = position
    next = 0
    limit = 0

  private def hasByte: Boolean =
    if next == limit then
      limit = file.read(buffer)
      next = 0
    next < limit

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
