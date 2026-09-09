package lisa
package hol
package extractor

import lisa.hol.core._
import upickle.default
import upickle.default.{ReadWriter => RW, _}
import upickle.implicits.key

import java.io.{File, RandomAccessFile}
import java.nio.charset.StandardCharsets
import scala.collection.mutable

import Parser._

sealed trait ExtractorException extends Exception
case class UnknownProofStepException(name: String) extends ExtractorException
case class CouldNotParseException(msg: String, next: String) extends Exception(s"Could not parse\n\tMessage: $msg\n\tNext: $next") with ExtractorException
case object IncompleteParsingException extends ExtractorException
case object UnreachableCaseException extends ExtractorException
case object ExtractorEndedException extends Exception("No more proof steps or theorems to read") with ExtractorException

extension [T](res: ParseResult[T])
  def getDone =
    res match
      case Success(out, next) if next.atEnd => out
      case Success(_, _) => throw IncompleteParsingException
      case NoSuccess(msg, next) => throw CouldNotParseException(msg, next.toString())
      case _ => throw UnreachableCaseException

private def parseTerm(str: String): Term = parse(term, str).getDone

private def parseVar(str: String): Variable = parse(variable, str).getDone

private def parseInst(insts: List[List[String]]): Map[Variable, Term] =
  insts.map {
    case List(left, right) => parseVar(left) -> parseTerm(right)
    case _ => throw UnreachableCaseException
  }.toMap

private def parseTypeVar(str: String) = parse(typeVariable, str).getDone

private def parseType(str: String) = parse(typ, str).getDone

private def parseTypeInst(insts: List[List[String]]): Map[TypeVariable, Type] =
  insts.map {
    case List(left, right) => parseTypeVar(left) -> parseType(right)
    case _ => throw UnreachableCaseException
  }.toMap

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
  private def parseTerm(str: String): Term = parseAll(term, str).getDone

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
    if !proofIterator.hasNext || !theoremIterator.hasNext then throw ExtractorEndedException

    val proofLine = proofIterator.next()
    val theoremRef = theoremIterator.next()
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
    while proofIterator.hasNext && theoremIterator.hasNext do readNext()

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

private final class FileExtractorData(proofFile: File, theoremFile: File) extends ExtractorData:
  private val proofs = new RandomAccessFile(proofFile, "r")
  private val theorems = new RandomAccessFile(theoremFile, "r")

  // Keep compact proof records for fast recursive access, but leave the much
  // larger intermediate theorem statements on disk until verification needs them.
  private val proofSteps = mutable.LongMap.empty[RawStep]
  private val theoremOffsets = mutable.LongMap.empty[Long]
  private val definitions = mutable.ArrayBuffer.empty[(Long, RawStep)]
  private var maxRead = -1L

  private def idOf(line: String): Long =
    val colon = line.indexOf(':', line.indexOf("\"id\"") + 4)
    var start = colon + 1
    while line.charAt(start).isWhitespace do start += 1
    var end = start
    while end < line.length && line.charAt(end).isDigit do end += 1
    line.substring(start, end).toLong

  private def readNext(): Unit =
    val theoremOffset = theorems.getFilePointer
    val encodedProofLine = proofs.readLine()
    val theoremLine = theorems.readLine()

    if encodedProofLine == null || theoremLine == null then throw ExtractorEndedException

    val proofLine = read[ProofLine](new String(encodedProofLine.getBytes(StandardCharsets.ISO_8859_1), StandardCharsets.UTF_8), false)
    val proofId = proofLine.id
    val theoremId = idOf(theoremLine)
    if proofId != theoremId then
      throw new IllegalArgumentException(s"Proof step $proofId is paired with theorem statement $theoremId.")

    maxRead = proofId
    proofSteps(proofId) = proofLine.step
    theoremOffsets(proofId) = theoremOffset
    proofLine.step match
      case _: DEFINITION | _: TYPE_DEFINITION => definitions += proofId -> proofLine.step
      case _ => ()

  private def readAt(file: RandomAccessFile, offset: Long): String =
    val resumeAt = file.getFilePointer
    try
      file.seek(offset)
      val encoded = file.readLine()
      if encoded == null then throw ExtractorEndedException
      new String(encoded.getBytes(StandardCharsets.ISO_8859_1), StandardCharsets.UTF_8)
    finally file.seek(resumeAt)

  def readTill(idx: Long): Unit =
    while maxRead < idx do readNext()

  def readAll(): Unit =
    try while true do readNext()
    catch case ExtractorEndedException => ()

  def getKnown(idx: Long): JustifiedTheorem =
    JustifiedTheorem(getKnownStatement(idx), getKnownProof(idx))

  def getKnownStatement(idx: Long): HOLSequent =
    read[TheoremStatement](readAt(theorems, theoremOffsets(idx)), false).sequent.extract

  def getKnownProof(idx: Long): ProofStep = proofSteps(idx).extract

  def getKnownDefinition(idx: Long): Option[ProofStep] =
    proofSteps(idx) match
      case definition: DEFINITION => Some(definition.extract)
      case definition: TYPE_DEFINITION => Some(definition.extract)
      case _ => None

  def knownDefinitionsBetween(fromExclusive: Long, toInclusive: Long): Iterator[(Long, ProofStep)] =
    definitions.iterator
      .filter((idx, _) => fromExclusive < idx && idx <= toInclusive)
      .map((idx, definition) => idx -> definition.extract)

  def knownTheorems: collection.MapView[Long, JustifiedTheorem] =
    proofSteps.keysIterator.map(idx => idx -> getKnown(idx)).toMap.view

  def close(): Unit =
    proofs.close()
    theorems.close()

final class ExtractorContext private (
    private val data: ExtractorData
) extends AutoCloseable:
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
    data.readTill(toInclusive)
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
   * The proof file should contain uniquely indexed proof steps.
   *
   * The theorem file should contain uniquely indexed theorem statements (HOL
   * sequents).
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
