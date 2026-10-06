package lisa
package hol
package extractor

import lisa.hol.core._
import upickle.default
import upickle.default.{ReadWriter => RW, _}
import upickle.implicits.key

import java.io.File
import scala.collection.mutable

import Parser._

sealed trait ExtractorException extends Exception
case class UnknownProofStepException(name: String) extends ExtractorException
case class CouldNotParseException(msg: String, next: String) extends Exception(s"Could not parse\n\tMessage: $msg\n\tNext: $next") with ExtractorException
case object UnreachableCaseException extends ExtractorException
case object ExtractorEndedException extends Exception("No more proof steps or theorems to read") with ExtractorException

extension [T](res: fastparse.Parsed[T])
  def getDone =
    res match
      case fastparse.Parsed.Success(out, _) => out
      case failure: fastparse.Parsed.Failure =>
        throw CouldNotParseException(failure.trace().longAggregateMsg, s"offset ${failure.index}")

private def parseTerm(str: String): Term = parseAll(str, term(using _)).getDone

private def parseVar(str: String): Variable = parseAll(str, variable(using _)).getDone

private def parseTypeVar(str: String): TypeVariable = parseAll(str, typeVariable(using _)).getDone

private def parseType(str: String): Type = parseAll(str, typ(using _)).getDone

// Structures as used in the HOL Light ProofTrace export
// Reflects the JSON encoding of proof steps

// map (x |-> t)
// {"from": "...", "to": "..."}
case class InstPair(from: String, to: String) derives RW:
  def toTermPair: (Variable, Term) = parseVar(from) -> parseTerm(to)
  def toTypePair: (TypeVariable, Type) = parseTypeVar(from) -> parseType(to)

// Use "step" as the ADT tag (instead of "$type")
@key("step")
sealed trait RawStep derives RW:
  def extract: ProofStep =
    this match
      case REFL(term) => core.REFL(parseTerm(term))
      case TRANS(pred1, pred2) => core.TRANS(pred1, pred2)
      case MK_COMB(pred1, pred2) => core.MK_COMB(pred1, pred2)
      case ABS(pred, term) => core.ABS(parseVar(term), pred)
      case BETA(term) => core.BETA(parseTerm(term))
      case ASSUME(term) => core.ASSUME(parseTerm(term))
      case EQ_MP(pred1, pred2) => core.EQ_MP(pred1, pred2)
      case DEDUCT_ANTISYM_RULE(pred1, pred2) => core.DEDUCT_ANTISYM_RULE(pred1, pred2)
      case INST(pred, insts) => core.INST(pred, insts.map(_.toTermPair).toMap)
      case INST_TYPE(pred, insts) => core.INST_TYPE(pred, insts.map(_.toTypePair).toMap)
      case AXIOM(term) => core.AXIOM(parseTerm(term))
      case DEFINITION(term, name) => core.DEFINITION(name, parseTerm(term))
      case TYPE_DEFINITION(pred, term, name) => core.TYPE_DEFINITION(name, parseTerm(term), pred)

// Step variants (JSON uses "step": "REFL", etc. for variants)
// example: {"step": "REFL", "term": "p"}
// example: {"step": "EQ_MP", "pred1": 1, "pred2": 2}
// see tests for more examples
case class REFL(term: String) extends RawStep
case class TRANS(pred1: Long, pred2: Long) extends RawStep
case class MK_COMB(pred1: Long, pred2: Long) extends RawStep
case class ABS(pred: Long, term: String) extends RawStep
case class BETA(term: String) extends RawStep
case class ASSUME(term: String) extends RawStep
case class EQ_MP(pred1: Long, pred2: Long) extends RawStep
case class DEDUCT_ANTISYM_RULE(pred1: Long, pred2: Long) extends RawStep

case class INST(pred: Long, insts: List[InstPair]) extends RawStep
case class INST_TYPE(pred: Long, insts: List[InstPair]) extends RawStep

case class AXIOM(term: String) extends RawStep
case class DEFINITION(term: String, name: String) extends RawStep
case class TYPE_DEFINITION(pred: Long, term: String, name: String) extends RawStep

/**
 * A single line in the proof output.
 *
 * @example `{"id": 3, "pr": {...}}`
 */
case class ProofLine(id: Long, @key("pr") step: RawStep) derives RW

/**
 * A raw sequent as represented in the JSON output.
 *
 * @example `{"hy": ["p"], "cc": "p"}`
 */
case class RawSequent(@key("hy") hypotheses: List[String], @key("cc") conclusion: String) derives RW:
  def extract: HOLSequent =
    HOLSequent(
      hypotheses.map(parseTerm),
      parseTerm(conclusion)
    )

/**
 * A theorem statement as represented in the JSON output, with a unique ID and
 * a sequent. The proof ID corresponds to the proof step of the same ID.
 *
 * @example `{"id": 3, "th": {"hy": ["p"], "cc": "p"}}`
 */
case class TheoremStatement(id: Long, @key("th") sequent: RawSequent) derives RW

/**
 * A theorem reference is a name assignment to a unique ID, which coresponds to
 * the "proof step" of the same ID.
 */
case class TheoremRef(id: Long, @key("nm") name: String) derives RW

case class JustifiedTheorem(statement: HOLSequent, proof: ProofStep)

private trait ExtractorData extends AutoCloseable:
  def statistics: ReaderStatistics = ReaderStatistics()
  def readTill(idx: Long): Unit
  def readAll(): Unit
  def getKnown(idx: Long): JustifiedTheorem
  def getKnownStatement(idx: Long): HOLSequent
  def getKnownProof(idx: Long): ProofStep
  def getKnownDefinition(idx: Long): Option[ProofStep]
  def knownDefinitionsBetween(fromExclusive: Long, toInclusive: Long): Iterator[(Long, ProofStep)]
  def knownTheorems: collection.MapView[Long, JustifiedTheorem]

private final class IteratorExtractorData(
    proofIterator: Iterator[ProofLine],
    theoremIterator: Iterator[TheoremStatement]
) extends ExtractorData:
  private var maxRead: Long = -1L
  private val stepMap: mutable.Map[Long, JustifiedTheorem] = mutable.Map.empty
  private val definitions = mutable.ArrayBuffer.empty[(Long, ProofStep)]

  private def readNext(): Unit =
    require(proofIterator.hasNext == theoremIterator.hasNext, "Proof and statement traces have different lengths.")
    if !proofIterator.hasNext then throw ExtractorEndedException

    val proofLine = proofIterator.next()
    val theoremRef = theoremIterator.next()
    require(proofLine.id > maxRead, s"Non-increasing proof ID ${proofLine.id} after $maxRead.")
    require(proofLine.id == theoremRef.id, s"Proof step ${proofLine.id} is paired with theorem statement ${theoremRef.id}.")
    val proof = proofLine.step.extract
    val theorem = JustifiedTheorem(theoremRef.sequent.extract, proof)

    maxRead = proofLine.id
    stepMap(proofLine.id) = theorem
    proof match
      case _: core.DEFINITION | _: core.TYPE_DEFINITION => definitions += proofLine.id -> proof
      case _ => ()

  def readTill(idx: Long): Unit =
    while maxRead < idx do readNext()

  def readAll(): Unit =
    while proofIterator.hasNext || theoremIterator.hasNext do readNext()

  def getKnown(idx: Long): JustifiedTheorem = stepMap(idx)

  def getKnownStatement(idx: Long): HOLSequent = getKnown(idx).statement

  def getKnownProof(idx: Long): ProofStep = getKnown(idx).proof

  def getKnownDefinition(idx: Long): Option[ProofStep] =
    getKnownProof(idx) match
      case definition: core.DEFINITION => Some(definition)
      case definition: core.TYPE_DEFINITION => Some(definition)
      case _ => None

  def knownDefinitionsBetween(fromExclusive: Long, toInclusive: Long): Iterator[(Long, ProofStep)] =
    definitions.iterator.filter((idx, _) => fromExclusive < idx && idx <= toInclusive)

  def knownTheorems: collection.MapView[Long, JustifiedTheorem] = stepMap.view

  def close(): Unit = ()

/** Report buffered file reads separately from parsed records. */
final case class ReaderStatistics(proofHeaders: Long = 0, proofRecords: Long = 0, statementRecords: Long = 0, proofBytes: Long = 0, statementBytes: Long = 0):
  def -(previous: ReaderStatistics): ReaderStatistics = ReaderStatistics(
    proofHeaders - previous.proofHeaders, proofRecords - previous.proofRecords, statementRecords - previous.statementRecords,
    proofBytes - previous.proofBytes, statementBytes - previous.statementBytes
  )

private final class FileExtractorData(proofFile: File, theoremFile: File) extends ExtractorData:
  private val index = new ProofIndex(proofFile)
  private val proofs = new TraceReader(proofFile)
  private val theorems = try new TraceReader(theoremFile) catch
    case error: Exception =>
      index.close()
      proofs.close()
      throw error
  private var proofRecords = 0L
  private var statementRecords = 0L

  override def statistics: ReaderStatistics =
    ReaderStatistics(index.records, proofRecords, statementRecords, index.bytesRead + proofs.bytesRead, theorems.bytesRead)

  private def proofAt(id: Long, offset: Long): RawStep =
    proofs.seek(offset)
    val line = read[ProofLine](proofs.readLine().getOrElse(throw ExtractorEndedException), false)
    require(line.id == id, s"Expected proof $id, found ${line.id}.")
    proofRecords += 1
    line.step

  def readTill(idx: Long): Unit = index.through(idx)

  /** Check both complete ID sequences, including unmatched tails. */
  def readAll(): Unit =
    theorems.seek(0)
    index.allIds.foreach: id =>
      val header = TraceHeader.read(theorems, false).getOrElse(throw new IllegalArgumentException(s"Missing statement for proof $id."))
      require(header.id == id, s"Proof step $id is paired with theorem statement ${header.id}.")
      theorems.skipLine()
    require(theorems.peekByte < 0, "Statement trace has records without proofs.")

  def getKnown(idx: Long): JustifiedTheorem = JustifiedTheorem(getKnownStatement(idx), getKnownProof(idx))

  def getKnownStatement(idx: Long): HOLSequent =
    // Require the proof ID too, but do not demand unused statements during proof reconstruction.
    index.offset(idx)
    theorems.seek(StatementSearch.offset(theorems, idx))
    val line = read[TheoremStatement](theorems.readLine().getOrElse(throw ExtractorEndedException), false)
    require(line.id == idx, s"Expected statement $idx, found ${line.id}.")
    statementRecords += 1
    line.sequent.extract

  def getKnownProof(idx: Long): ProofStep = proofAt(idx, index.offset(idx)).extract

  def getKnownDefinition(idx: Long): Option[ProofStep] =
    proofAt(idx, index.offset(idx)) match
      case definition: DEFINITION => Some(definition.extract)
      case definition: TYPE_DEFINITION => Some(definition.extract)
      case _ => None

  def knownDefinitionsBetween(fromExclusive: Long, toInclusive: Long): Iterator[(Long, ProofStep)] =
    index.definitionOffsets(fromExclusive, toInclusive).map: (id, offset) =>
      id -> proofAt(id, offset).extract

  def knownTheorems: collection.MapView[Long, JustifiedTheorem] =
    index.allIds.map(id => id -> getKnown(id)).toMap.view

  def close(): Unit =
    try index.close()
    finally
      try proofs.close()
      finally theorems.close()

final class ExtractorContext private (
    private val data: ExtractorData
) extends AutoCloseable:
  /** Snapshot file-reader counters; iterator-backed contexts report zero. */
  def statistics: ReaderStatistics = data.statistics
  def this(proofIterator: Iterator[ProofLine], theoremIterator: Iterator[TheoremStatement]) =
    this(new IteratorExtractorData(proofIterator, theoremIterator))

  /**
   * Get the theorem statement and proof for the given index, if it exists.
   *
   * @throws NoSuchElementException if the index does not exist
   */
  @throws[NoSuchElementException]
  def getTheorem(idx: Long): JustifiedTheorem =
    readAt(idx)(data.getKnown(idx))

  /** Extract only the theorem statement at the given index. */
  def getStatement(idx: Long): HOLSequent =
    readAt(idx)(data.getKnownStatement(idx))

  /** Extract only the proof step at the given index. */
  def getProof(idx: Long): ProofStep =
    readAt(idx)(data.getKnownProof(idx))

  /** Return a definition at the given index without extracting an ordinary proof step. */
  def getDefinition(idx: Long): Option[ProofStep] =
    readAt(idx)(data.getKnownDefinition(idx))

  /** Return every available definition in the requested interval, skipping absent indices. */
  private[hol] def getDefinitionsBetween(fromExclusive: Long, toInclusive: Long): Seq[(Long, ProofStep)] =
    require(fromExclusive <= toInclusive, s"Invalid definition interval ($fromExclusive, $toInclusive].")
    try data.readTill(toInclusive)
    catch case ExtractorEndedException => () // An interval need not end at an existing record.
    data.knownDefinitionsBetween(fromExclusive, toInclusive).toSeq

  private def readAt[T](idx: Long)(result: => T): T =
    if idx < 0 then throw new NoSuchElementException(s"Negative index: $idx.")
    try data.readTill(idx)
    catch
      case ExtractorEndedException =>
        throw new NoSuchElementException(s"Index $idx out of bounds, no more theorems to read.")

    try result
    catch case _: NoSuchElementException => throw new NoSuchElementException(s"Index $idx does not exist in the trace.")

  /**
   * Exhaustively read the remaining proofs and theorems and return a map of
   * justifications. The context is not destroyed, but its data is fully
   * contained in the returned map view.
   */
  def toMap: collection.MapView[Long, JustifiedTheorem] =
    data.readAll()
    data.knownTheorems

  /** Close the underlying trace files. */
  def close(): Unit = data.close()

object ExtractorContext:
  private[extractor] def fromFiles(proofFile: File, theoremFile: File): ExtractorContext =
    new ExtractorContext(new FileExtractorData(proofFile, theoremFile))

object JSONParser:
  /**
   * Read a list of items from the given source interpreted as NDJSON, using the
   * given reader to parse each item.
   *
   * If the file is not newline delimited (or data contains newlines :scared:),
   * this will fail, and the lower-level uJSON API may be used instead.
   */
  private def readIterated[T](src: java.io.Reader, reader: String => T): Iterator[T] =
    val buffered = new java.io.BufferedReader(src)
    Iterator
      .continually(buffered.readLine())
      .takeWhile(_ ne null)
      .map(reader)

  /**
   * Use the given reader for a type to read a list of items from the given
   * source interpreted as NDJSON.
   */
  private def readIterated[T: upickle.default.Reader](src: java.io.Reader): Iterator[T] =
    readIterated(src, read[T](_, false))

  /**
   * Generate an extractor context from the given proof and theorem readers.
   *
   * The contents are expected to be in the ProofTrace export format.
   */
  def toContext(proofSrc: java.io.Reader, thmSrc: java.io.Reader): ExtractorContext =
    new ExtractorContext(
      readIterated[ProofLine](proofSrc),
      readIterated[TheoremStatement](thmSrc)
    )

  /**
   * Generate an extractor context from the given proof and theorem files.
   *
   * The files are expected to be in the ProofTrace export format.
   *
   * Keep both files sorted by unique non-negative IDs, with one JSON record per line.
   * Preserve the export's leading `id`, then `pr.step` or `th` fields.
   * Do not modify either file while the context is open.
   *
   * Defer payload parsing and statement lookup until requested. Use `toMap` to
   * validate complete pairing and payloads on small traces.
   *
   * @throws java.io.FileNotFoundException if either file does not exist
   * @throws java.io.IOException if either file cannot be read
   */
  @throws[java.io.FileNotFoundException]
  @throws[java.io.IOException]
  def toContext(proofFile: String, thmFile: String): ExtractorContext =
    val proofReader = new java.io.File(proofFile)
    val thmReader = new java.io.File(thmFile)

    if !proofReader.exists() then throw new java.io.FileNotFoundException(s"Proof file not found: $proofFile")
    else if !proofReader.canRead() then throw new java.io.IOException(s"Proof file cannot be read: $proofFile")
    else if !thmReader.exists() then throw new java.io.FileNotFoundException(s"Theorem file not found: $thmFile")
    else if !thmReader.canRead() then throw new java.io.IOException(s"Theorem file cannot be read: $thmFile")
    else () // ok

    ExtractorContext.fromFiles(proofReader, thmReader)

  /**
   * Generate an iterator of theorem references (index-name pairs) from the
   * given file.
   *
   * The file is expected to be in the ProofTrace export format, containing a
   * list of theorem references (ID-name pairs).
   *
   * @throws java.io.FileNotFoundException if the file does not exist
   * @throws java.io.IOException if the file cannot be read
   */
  @throws[java.io.FileNotFoundException]
  @throws[java.io.IOException]
  def namesIterator(file: String): Iterator[TheoremRef] =
    val reader = new java.io.File(file)

    if !reader.exists() then throw new java.io.FileNotFoundException(s"Theorem reference file not found: $file")
    else if !reader.canRead() then throw new java.io.IOException(s"Theorem reference file cannot be read: $file")
    else () // ok

    readIterated[TheoremRef](new java.io.FileReader(reader))

  /**
   * Given a file prefix, generate an extractor context and an iterator of
   * theorem references. The files are expected to be in the ProofTrace export
   * format, with the proof steps in `<prefix>.proofs`, the theorem statements
   * in `<prefix>.theorems`, and the theorem references in `<prefix>.names`.
   *
   * @param filePrefix the prefix path of files to read from
   * @return an [[ExtractorContext]] to retrieve theorems and proofs, and an
   * iterator of named theorems.
   *
   * @throws java.io.FileNotFoundException if any of the files do not exist
   * @throws java.io.IOException if any of the files cannot be read
   */
  @throws[java.io.FileNotFoundException]
  @throws[java.io.IOException]
  def initializeFromPrefix(filePrefix: String): (ExtractorContext, Iterator[TheoremRef]) =
    val proofFile = s"$filePrefix.proofs"
    val thmFile = s"$filePrefix.theorems"
    val namesFile = s"$filePrefix.names"

    val context = toContext(proofFile, thmFile)
    val names = namesIterator(namesFile)

    (context, names)

  /**
   * Given a proof file, a theorem file, and a theorem reference file, generate
   * an iterator of theorem name and actual-theorem pairs. The theorem is a
   * sequent paired with a proof step.
   *
   * @throws java.io.FileNotFoundException if any file does not exist
   * @throws java.io.IOException if any file cannot be read
   * @throws ExtractorException if the proof steps cannot be parsed, or if the proof tree is malformed
   */
  @throws[java.io.FileNotFoundException]
  @throws[java.io.IOException]
  @throws[ExtractorException]
  def theoremIterator(proofFile: String, thmFile: String, namesFile: String): Iterator[(String, JustifiedTheorem)] =
    val context = toContext(proofFile, thmFile)
    val names = namesIterator(namesFile)

    names.map:
      case TheoremRef(id, name) =>
        val thm = context.getTheorem(id)
        name -> thm
