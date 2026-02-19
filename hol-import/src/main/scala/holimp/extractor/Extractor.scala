package holimp
package extractor

import core.*
import upickle.default
import upickle.implicits.key
import upickle.default.{ReadWriter => RW, *}
import Parser.*
import java.io.File
import scala.collection.mutable

sealed trait ExtractorException extends Exception
case class UnknownProofStepException(name: String) extends ExtractorException
case class CouldNotParseException(msg: String, next: String) extends Exception(s"Could not parse\n\tMessage: $msg\n\tNext: $next") with ExtractorException
case object IncompleteParsingException extends ExtractorException
case object UnreachableCaseException extends ExtractorException

extension [T] (res: ParseResult[T])
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
case class InstPair(from: String, to: String) derives RW

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
      case INST(pred, insts) => core.INST(pred, parseInst(insts.map(i => List(i.from, i.to))))
      case INST_TYPE(pred, insts) => core.INST_TYPE(pred, parseTypeInst(insts.map(i => List(i.from, i.to))))
      case AXIOM(term) => core.AXIOM(parseTerm(term))
      case DEFINITION(term, name) => core.DEFINITION(name, parseTerm(term))
      case TYPE_DEFINITION(pred, term, name) => core.TYPE_DEFINITION(name, parseTerm(term), pred)

// Step variants (JSON uses "step": "REFL", etc. for variants)
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
  */
case class TheoremStatement(id: Long, @key("th") sequent: RawSequent) derives RW

/**
  * A theorem reference is a name assignment to a unique ID, which coresponds to
  * the "proof step" of the same ID.
  */
case class TheoremRef(id: Long, name: String) derives RW

case class JustifiedTheorem(statement: HOLSequent, proof: ProofStep)

final class ExtractorContext(
  val proofIterator: Iterator[ProofLine],
  val theoremIterator: Iterator[TheoremStatement]
):
  // proofIterator and theoremIterator should be in sync
  // this is not necessary for an extraction, but is always the case for the ProofTrace output
  // and allows us to read theorems lazily as we need them
  // require(proofIterator.length == theoremIterator)
  // require((0 to proofIterator.length).forall(i => proofIterator(i).id == theoremIterator(i).id))

  import ExtractorContext.*

  private var maxRead: Long = -1L // proof indices start at 0
  private val stepMap: mutable.Map[Long, JustifiedTheorem] = mutable.Map.empty

  @throws[ExtractorEndedException.type]
  private def readNext(): Unit =
    if !proofIterator.hasNext || !theoremIterator.hasNext then
      throw ExtractorEndedException
    
    val proofLine = proofIterator.next()
    val theoremRef = theoremIterator.next()

    // require(proofLine.id == theoremRef.id)
    // require(proofLine.id == maxRead + 1)

    // extract trees from the raw terms/sequents
    val thm = JustifiedTheorem(
      theoremRef.sequent.extract,
      proofLine.step.extract
    )

    val maxRead = proofLine.id
    stepMap += proofLine.id -> thm

  @throws[ExtractorEndedException.type]
  private def readTill(idx: Long): Unit =
    while maxRead < idx do readNext()

  /**
   * Get the theorem statement and proof for the given index, if it exists.
   * 
   * @throws NoSuchElementException if the index does not exist
   */
  @throws[NoSuchElementException]
  def getTheorem(idx: Long): JustifiedTheorem =
    // require(idx >= 0 && idx < proofIterator.length)

    if idx < 0 then 
      throw new NoSuchElementException(s"Negative index: $idx.")
    try 
      readTill(idx)
    catch 
      case ExtractorEndedException => 
        throw new NoSuchElementException(s"Index $idx out of bounds, no more theorems to read.")
    
    stepMap(idx)

  /**
   * Exhaustively read the remaining proofs and theorems and returns a map of
   * justifications. The context is not destroyed, but its data is fully
   * contained in the returned map view.
   */
  def toMap: collection.MapView[Long, JustifiedTheorem] =
    // read all remaining theorems
    while proofIterator.hasNext && theoremIterator.hasNext do readNext()
    stepMap.view

object ExtractorContext:
  case object ExtractorEndedException extends Exception("No more proof steps or theorems to read")

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
  private def readIterated[T: Reader](src: java.io.Reader): Iterator[T] =
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

    if !proofReader.exists() then
      throw new java.io.FileNotFoundException(s"Proof file not found: $proofFile")
    else if !proofReader.canRead() then
      throw new java.io.IOException(s"Proof file cannot be read: $proofFile")
    else if !thmReader.exists() then
      throw new java.io.FileNotFoundException(s"Theorem file not found: $thmFile")
    else if !thmReader.canRead() then
      throw new java.io.IOException(s"Theorem file cannot be read: $thmFile")
    else
      () // ok

    toContext(new java.io.FileReader(proofReader), new java.io.FileReader(thmReader))

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

    if !reader.exists() then
      throw new java.io.FileNotFoundException(s"Theorem reference file not found: $file")
    else if !reader.canRead() then
      throw new java.io.IOException(s"Theorem reference file cannot be read: $file")
    else
      () // ok

    readIterated[TheoremRef](new java.io.FileReader(reader))

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
