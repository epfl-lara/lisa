package lisa.hol.extractor

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files
import org.scalatest.funsuite.AnyFunSuite

class TraceReaderSuite extends AnyFunSuite:
  test("preserve byte positions across UTF-8 characters and every line ending"):
    val lines = Seq("" -> "\n", "α😀" -> "\r\n", "longer line" -> "\r", "終" -> "\n", "last" -> "")
    val text = lines.map((line, ending) => line + ending).mkString
    val offsets = lines.scanLeft(0L)((offset, entry) => offset + (entry._1 + entry._2).getBytes(UTF_8).length)
    val path = Files.createTempFile("lisa-trace-reader", ".json")
    try
      Files.writeString(path, text, UTF_8)
      for size <- 1 to 9 do
        val reader = new TraceReader(path.toFile, size)
        try
          for ((line, _), index) <- lines.zipWithIndex do
            assert(reader.position == offsets(index))
            assert(reader.readLine().contains(line))
            assert(reader.position == offsets(index + 1))
          assert(reader.readLine().isEmpty)
          assert(reader.readLine().isEmpty)

          // Seek backward after EOF, then resume at a later saved position.
          reader.seek(offsets(1))
          assert(reader.readLine().contains("α😀"))
          reader.seek(offsets(4))
          assert(reader.readLine().contains("last"))
          assert(reader.position == offsets.last)
        finally reader.close()
    finally Files.deleteIfExists(path)

  test("read lines larger than the buffer and do not invent a line after a final CRLF"):
    val path = Files.createTempFile("lisa-trace-reader", ".json")
    val line = "a" * (128 * 1024) + "λ"
    try
      Files.writeString(path, line + "\r\n", UTF_8)
      val reader = new TraceReader(path.toFile)
      try
        assert(reader.readLine().contains(line))
        assert(reader.position == Files.size(path))
        assert(reader.readLine().isEmpty)
      finally reader.close()
    finally Files.deleteIfExists(path)

  test("read an empty file"):
    val path = Files.createTempFile("lisa-trace-reader", ".json")
    try
      val reader = new TraceReader(path.toFile)
      try
        assert(reader.readLine().isEmpty)
        assert(reader.position == 0)
      finally reader.close()
    finally Files.deleteIfExists(path)
