package lisa.hol.extractor

import java.io.File
import fastparse.*
import fastparse.NoWhitespace.*
import scala.annotation.tailrec
import scala.collection.Searching.{Found, InsertionPoint}
import scala.collection.mutable
import scala.util.Using

/**
 * Recognize ProofTrace's leading fields without parsing or retaining whole payloads.
 */
private[extractor] object TraceHeader:
  final case class Header(id: Long, rule: String):
    def isDefinition: Boolean = rule == "DEFINITION" || rule == "TYPE_DEFINITION"

  private val rules = Set("REFL", "TRANS", "MK_COMB", "ABS", "BETA", "ASSUME", "EQ_MP", "DEDUCT_ANTISYM_RULE", "INST", "INST_TYPE", "AXIOM", "DEFINITION", "TYPE_DEFINITION")

  private def token[$: P](text: String): P[Unit] = P(CharsWhileIn(" \t", 0) ~ text)
  private def field[$: P](name: String): P[Unit] = P(token(s"\"$name\"") ~ token(":"))

  private def decimal[$: P]: P[Long] =
    P(("0" | CharIn("1-9") ~ CharIn("0-9").rep(max = 18)).!)
      .map(_.toLongOption)
      .filter(_.nonEmpty)
      .map(_.get)

  // HOL emits decimal IDs; uPickle quotes large Long values. Neither passes through Double.
  private def idPrefix[$: P]: P[Long] =
    P(token("{") ~/ field("id") ~ CharsWhileIn(" \t", 0) ~ ("\"" ~/ decimal ~ token("\"") | decimal) ~ token(","))

  private def proofHeader[$: P]: P[Header] =
    P(idPrefix ~ field("pr") ~ token("{") ~ field("step") ~ token("\"") ~ CharIn("A-Z_").rep(min = 1, max = 32).! ~ "\"" ~ token(","))
      .filter((_, rule) => rules(rule))
      .map((id, rule) => Header(id, rule))

  private def statementHeader[$: P]: P[Long] = P(idPrefix ~ field("th") ~ token("{"))

  private def read[T](reader: TraceReader, parser: P[?] => P[T], kind: String): Option[T] =
    val start = reader.position
    if reader.peekByte < 0 then None
    else
      val prefix = reader.readPrefix(128)
      // Most headers fit in one fragment; stream only when more input may be needed.
      val parsed = fastparse.parse(prefix, parser) match
        case _: Parsed.Failure if prefix.length == 128 =>
          val chunks = Iterator.single(prefix) ++ Iterator.continually(reader.readPrefix(128)).takeWhile(_.nonEmpty)
          fastparse.parse(IteratorParserInput(chunks), parser)
        case result => result
      parsed match
        case Parsed.Success(header, _) => Some(header)
        case _: Parsed.Failure =>
          throw new IllegalArgumentException(s"Invalid $kind header at byte $start; expected ordered ProofTrace fields.")

  def readProof(reader: TraceReader): Option[Header] =
    read(reader, proofHeader(using _), "proof")

  def readStatementId(reader: TraceReader): Option[Long] =
    read(reader, statementHeader(using _), "statement")

/**
 * Index sparse proof IDs by blocks; retain offsets, never ordinary proof payloads.
 */
private[extractor] final class ProofIndex(path: File, blockSize: Int = 256, cachedBlocks: Int = 8) extends AutoCloseable:
  require(blockSize > 0 && cachedBlocks > 0)
  private val (scan, lookup) = TraceReader.openPair(path, path)
  private val anchors = mutable.ArrayBuffer.empty[(Long, Long)]
  private val definitions = mutable.ArrayBuffer.empty[(Long, Long)]
  private val blocks = mutable.LinkedHashMap.empty[Int, Vector[(Long, Long)]]
  private var current = Vector.empty[(Long, Long)]
  private var last = -1L
  private var ended = false
  private var count = 0L
  private var failure = Option.empty[Exception]
  private val byId: Ordering[(Long, Long)] = Ordering.by(_._1)

  def records: Long = count
  def bytesRead: Long = scan.bytesRead + lookup.bytesRead
  def anchorCount: Int = anchors.size
  def cachedOffsets: Int = current.size + blocks.valuesIterator.map(_.size).sum

  private def retain(block: Int, offsets: Vector[(Long, Long)]): Vector[(Long, Long)] =
    blocks.remove(block)
    blocks(block) = offsets
    if blocks.size > cachedBlocks then blocks.remove(blocks.head._1)
    offsets

  /**
   * Skim headers through the requested ID; validate strict ordering, not payloads.
   */
  def through(id: Long): Unit =
    // A failed scan may have consumed part of a record; it cannot safely resume.
    failure.foreach(throw _)
    try scanThrough(id)
    catch
      case error: Exception =>
        failure = Some(error)
        throw error

  private def scanThrough(id: Long): Unit =
    // Long.MaxValue also requests exhaustive validation, including any trailing records.
    while !ended && (last < id || id == Long.MaxValue) do
      val offset = scan.position
      TraceHeader.readProof(scan) match
        case None => ended = true
        case Some(header) =>
          require(header.id > last, s"Non-increasing proof ID ${header.id} after $last at byte $offset.")
          if current.isEmpty then anchors += header.id -> offset
          current :+= header.id -> offset
          if header.isDefinition then definitions += header.id -> offset
          scan.skipLine()
          last = header.id
          count += 1
          if current.size == blockSize then
            retain(anchors.size - 1, current)
            current = Vector.empty

  private def blockFor(id: Long): Int =
    anchors.search(id -> 0L)(using byId) match
      case Found(block) => block
      case InsertionPoint(next) => next - 1

  private def readBlock(block: Int): Vector[(Long, Long)] =
    lookup.seek(anchors(block)._2)
    Vector.fill(blockSize):
      val offset = lookup.position
      val header = TraceHeader.readProof(lookup).getOrElse(throw ExtractorEndedException)
      lookup.skipLine()
      header.id -> offset

  private def offsets(block: Int): Vector[(Long, Long)] =
    if block == anchors.size - 1 && current.nonEmpty then current
    else retain(block, blocks.getOrElse(block, readBlock(block)))

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

  def close(): Unit = Using.resources(scan, lookup)((_, _) => ())

/**
 * Seek a statement by ID without cataloguing or decoding preceding statements.
 */
private[extractor] object StatementSearch:
  def offset(reader: TraceReader, id: Long): Long =
    @tailrec def search(low: Long, high: Long): Long =
      if low >= high then throw new NoSuchElementException(s"Missing statement $id")
      val mid = low + (high - low) / 2
      reader.seekLine(mid)
      val start = reader.position
      if start >= high then search(low, mid)
      else
        TraceHeader.readStatementId(reader) match
          case Some(found) if found == id => start
          case Some(found) if found < id =>
            reader.skipLine()
            search(reader.position, high)
          case _ => search(low, mid)

    search(0, reader.length)
