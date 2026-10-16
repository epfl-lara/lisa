package lisa.hol.extractor

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files
import org.scalatest.funsuite.AnyFunSuite
import scala.util.Using

class TraceReaderSuite extends AnyFunSuite:
  private def withReader(text: String, bufferSize: Int = 64 * 1024)(check: TraceReader => Unit): Unit =
    val path = Files.createTempFile("lisa-trace-prefix", ".json")
    try
      Files.writeString(path, text, UTF_8)
      Using.resource(new TraceReader(path.toFile, bufferSize))(check)
    finally Files.deleteIfExists(path)

  test("leave line terminators unread when collecting bounded prefixes"):
    for size <- 1 to 9; ending <- Seq("\n", "\r", "\r\n") do
      withReader("abcdefg" + ending + "終😀", size): reader =>
        assert(reader.readPrefix(3) == "abc")
        assert(reader.readPrefix(3) == "def")
        assert(reader.readPrefix(3) == "g")
        assert(reader.readPrefix(3).isEmpty)
        assert(reader.position == 7)
        reader.skipLine()
        assert(reader.readLine().contains("終😀"))
        assert(reader.readLine().isEmpty)

  test("parse headers across prefix and buffer boundaries without consuming the next line"):
    for padding <- Seq(0, 100, 127, 128, 255, 256, 8192); size <- Seq(1, 3, 64); quoted <- Seq(false, true) do
      val spaces = " " * padding
      val id = if quoted then s"\"${Long.MaxValue}\"" else Long.MaxValue.toString
      val proof = s"""$spaces{"id":$spaces$id,"pr":{$spaces"step":"TYPE_DEFINITION","term":"π😀"}}"""
      withReader(proof + "\r\nnext", size): reader =>
        val header = TraceHeader.readProof(reader).get
        assert(header.id == Long.MaxValue)
        assert(header.isDefinition)
        reader.skipLine()
        assert(reader.readLine().contains("next"))
      withReader(s"""$spaces{"id":$spaces$id,"th":{}}""" + "\nnext", size): reader =>
        assert(TraceHeader.readStatementId(reader).contains(Long.MaxValue))
        reader.skipLine()
        assert(reader.readLine().contains("next"))

  test("reject invalid or incomplete headers without reading into the following record"):
    val invalid = Seq(
      "",
      "{",
      "{\"id\":",
      "{\"id\":-1,",
      "{\"id\":+1,",
      "{\"id\":00,",
      "{\"id\":\"01\",",
      "{\"id\":9223372036854775808,\"pr\":{\"step\":\"REFL\",",
      "{\"id\":0,\"pr\":{\"step\":\"FUTURE_RULE\",",
      "{\"id\":0,\"pr\":{\"step\":\"refl\","
    )
    val valid = """{"id":7,"pr":{"step":"REFL","term":"ignored"}}"""
    for text <- invalid do
      withReader(text + "\n" + valid, 3): reader =>
        assertThrows[IllegalArgumentException](TraceHeader.readProof(reader))
        reader.skipLine()
        assert(TraceHeader.readProof(reader).contains(TraceHeader.Header(7, "REFL")))

  test("reject invalid seek offsets without moving the cursor"):
    withReader("first\nlast", 3): reader =>
      reader.seek(2)
      for invalid <- Seq(-1L, Long.MinValue, reader.length + 1, Long.MaxValue) do
        assertThrows[IllegalArgumentException](reader.seek(invalid))
        assertThrows[IllegalArgumentException](reader.seekLine(invalid))
        assert(reader.position == 2)

  test("align arbitrary byte positions without decoding partial UTF-8 or splitting CRLF"):
    val text = "α😀\r\nβ\r終\nlast"
    val bytes = text.getBytes(UTF_8)
    val starts = Seq(
      0L,
      "α😀\r\n".getBytes(UTF_8).length.toLong,
      "α😀\r\nβ\r".getBytes(UTF_8).length.toLong,
      "α😀\r\nβ\r終\n".getBytes(UTF_8).length.toLong,
      bytes.length.toLong
    )
    val path = Files.createTempFile("lisa-trace-seek", ".json")
    try
      Files.write(path, bytes)
      for size <- 1 to 9 do
        val reader = new TraceReader(path.toFile, size)
        try
          for position <- 0 to bytes.length do
            reader.seekLine(position)
            assert(reader.position == starts.find(_ >= position).get, s"buffer=$size, byte=$position")
          reader.seek(0)
          reader.skipLine()
          assert(reader.readLine().contains("β"))
          reader.skipLine()
          assert(reader.readLine().contains("last"))
        finally reader.close()
    finally Files.deleteIfExists(path)

  test("keep the offset cache bounded while sparse anchors cover a large scan"):
    val path = Files.createTempFile("lisa-proof-index", ".proofs")
    try
      Files.writeString(path, (0 until 1000).map(i => s"""{"id":${i * 7},"pr":{"step":"REFL","term":"ignored"}}""").mkString("\n"))
      val index = new ProofIndex(path.toFile, blockSize = 16, cachedBlocks = 2)
      try
        index.through(Long.MaxValue)
        assert(index.records == 1000)
        assert(index.anchorCount == 63)
        for id <- Seq(0L, 3500L, 693L, 6993L) do
          assert(index.offset(id) >= 0)
          assert(index.cachedOffsets <= 48)
        assertThrows[NoSuchElementException](index.offset(1))
      finally index.close()
    finally Files.deleteIfExists(path)

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
