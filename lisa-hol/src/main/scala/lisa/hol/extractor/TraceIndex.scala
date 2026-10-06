package lisa.hol.extractor

import java.io.File
import scala.collection.mutable

/** Read only the fixed leading fields emitted by ProofTrace, leaving the payload unread. */
private[extractor] object TraceHeader:
  final case class Header(id: Long, rule: String)
  private val rules = Set("REFL", "TRANS", "MK_COMB", "ABS", "BETA", "ASSUME", "EQ_MP", "DEDUCT_ANTISYM_RULE", "INST", "INST_TYPE", "AXIOM", "DEFINITION", "TYPE_DEFINITION")

  def read(reader: TraceReader, proof: Boolean): Option[Header] =
    if reader.peekByte < 0 then None
    else
      val start = reader.position
      def fail(): Nothing = throw new IllegalArgumentException(s"Invalid ${if proof then "proof" else "statement"} header at byte $start; expected ordered ProofTrace fields.")
      def spaces(): Unit =
        while reader.peekByte == ' ' || reader.peekByte == '\t' do reader.readByte()
      def token(text: String): Unit =
        spaces()
        text.foreach(c => if reader.readByte() != c then fail())
      token("{")
      token("\"id\"")
      token(":")
      spaces()
      // uPickle quotes large Long values; HOL's exporter writes decimal numbers.
      val quoted = reader.peekByte == '"'
      if quoted then reader.readByte()
      val digits = new StringBuilder
      while reader.peekByte >= '0' && reader.peekByte <= '9' do
        if digits.length == 19 then fail()
        digits.append(reader.readByte().toChar)
      if digits.isEmpty || (digits.length > 1 && digits.head == '0') then fail()
      val id = try digits.toString.toLong catch case _: NumberFormatException => fail()
      if quoted then token("\"")
      token(",")
      token(if proof then "\"pr\"" else "\"th\"")
      token(":")
      token("{")
      val rule = if !proof then "" else
        token("\"step\"")
        token(":")
        token("\"")
        val name = new StringBuilder
        while reader.peekByte != '"' do
          val c = reader.readByte()
          if name.length >= 32 || !(c == '_' || c >= 'A' && c <= 'Z') then fail()
          name.append(c.toChar)
        token("\"")
        token(",")
        if !rules(name.toString) then fail()
        name.toString
      Some(Header(id, rule))

/** Index sparse proof IDs by blocks; retain offsets, never ordinary proof payloads. */
private[extractor] final class ProofIndex(path: File, blockSize: Int = 256, cachedBlocks: Int = 8) extends AutoCloseable:
  require(blockSize > 0 && cachedBlocks > 0)
  private val scan = new TraceReader(path)
  private val lookup = new TraceReader(path)
  private val anchors = mutable.ArrayBuffer.empty[(Long, Long)]
  private val definitions = mutable.ArrayBuffer.empty[(Long, Long)]
  private val blocks = mutable.LinkedHashMap.empty[Int, Vector[(Long, Long)]]
  private var current = Vector.empty[(Long, Long)]
  private var last = -1L
  private var ended = false
  private var count = 0L
  private var failure = Option.empty[Exception]

  def records: Long = count
  def bytesRead: Long = scan.bytesRead + lookup.bytesRead
  def anchorCount: Int = anchors.size
  def cachedOffsets: Int = current.size + blocks.valuesIterator.map(_.size).sum

  private def retain(block: Int, offsets: Vector[(Long, Long)]): Unit =
    blocks.remove(block)
    blocks(block) = offsets
    if blocks.size > cachedBlocks then blocks.remove(blocks.head._1)

  /** Skim headers through the requested ID; validate strict ordering, not payloads. */
  def through(id: Long): Unit =
    failure.foreach(throw _)
    try scanThrough(id)
    catch
      case error: Exception =>
        failure = Some(error)
        throw error

  private def scanThrough(id: Long): Unit =
    while !ended && last < id do
      val offset = scan.position
      TraceHeader.read(scan, true) match
        case None => ended = true
        case Some(header) =>
          require(header.id > last, s"Non-increasing proof ID ${header.id} after $last at byte $offset.")
          if current.isEmpty then anchors += header.id -> offset
          current :+= header.id -> offset
          if header.rule == "DEFINITION" || header.rule == "TYPE_DEFINITION" then definitions += header.id -> offset
          scan.skipLine()
          last = header.id
          count += 1
          if current.size == blockSize then
            retain(anchors.size - 1, current)
            current = Vector.empty

  private def blockFor(id: Long): Int =
    var low = 0
    var high = anchors.size
    while low < high do
      val mid = low + (high - low) / 2
      if anchors(mid)._1 <= id then low = mid + 1 else high = mid
    low - 1

  private def offsets(block: Int): Vector[(Long, Long)] =
    if block == anchors.size - 1 && current.nonEmpty then current
    else blocks.get(block) match
      case Some(entries) =>
        retain(block, entries)
        entries
      case None =>
        lookup.seek(anchors(block)._2)
        val entries = Vector.fill(blockSize):
          val offset = lookup.position
          val header = TraceHeader.read(lookup, true).getOrElse(throw ExtractorEndedException)
          lookup.skipLine()
          header.id -> offset
        retain(block, entries)
        entries

  def offset(id: Long): Long =
    through(id)
    val block = blockFor(id)
    if block < 0 then throw new NoSuchElementException(s"Missing proof $id")
    offsets(block).find(_._1 == id).map(_._2).getOrElse(throw new NoSuchElementException(s"Missing proof $id"))

  def definitionOffsets(from: Long, to: Long): Iterator[(Long, Long)] =
    through(to)
    definitions.iterator.dropWhile(_._1 <= from).takeWhile(_._1 <= to)

  def allIds: Iterator[Long] =
    through(Long.MaxValue)
    anchors.indices.iterator.flatMap(block => offsets(block).iterator.map(_._1))

  def close(): Unit = try scan.close() finally lookup.close()

/** Seek a statement by ID without cataloguing or decoding preceding statements. */
private[extractor] object StatementSearch:
  def offset(reader: TraceReader, id: Long): Long =
    var low = 0L
    var high = reader.length
    while low < high do
      val mid = low + (high - low) / 2
      reader.seekLine(mid)
      val start = reader.position
      if start >= high then high = mid
      else TraceHeader.read(reader, false) match
        case None => high = mid
        case Some(header) =>
          if header.id == id then return start
          else if header.id > id then high = mid
          else
            reader.skipLine()
            low = reader.position
    throw new NoSuchElementException(s"Missing statement $id")
