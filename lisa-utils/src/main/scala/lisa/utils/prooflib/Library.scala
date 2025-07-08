package lisa.utils.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SequentCalculus
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}

import scala.collection.mutable.{Stack => stack}

/**
 * A class abstracting a [[lisa.kernel.proof.RunningTheory]] providing utility functions and a convenient syntax
 * to write and use Theorems and Definitions.
 * @param theory The inner RunningTheory
 */
abstract class Library extends lisa.utils.prooflib.WithTheorems with lisa.utils.prooflib.ProofsHelpers {

  val theory: RunningTheory
  given library: this.type = this
  given RunningTheory = theory

  export lisa.kernel.proof.SCProof

  val K = lisa.utils.K
  val SC: SequentCalculus.type = K.SC
  private[prooflib] val F = lisa.utils.fol.FOL
  import F.{given}

  var last: Option[JUSTIFICATION] = None

  // Options for files
  private[prooflib] var _withCache: Boolean = false
  def withCache(using file: sourcecode.File, om: OutputManager)(): Unit =
    if last.nonEmpty then om.output(OutputManager.WARNING("Warning: withCache option should be used before the first definition or theorem."))
    else _withCache = true

  private[prooflib] var _draft: Option[sourcecode.File] = None
  def draft(using file: sourcecode.File, om: OutputManager)(): Unit =
    if last.nonEmpty then om.output(OutputManager.WARNING("Warning: draft option should be used before the first definition or theorem."))
    else _draft = Some(file)
  def isDraft = _draft.nonEmpty

  private[prooflib] var _currentSection: Map[String, (String, Int)] = Map.empty

  def section(name: String)(using om: OutputManager, file: sourcecode.File): Unit =
    val index = _currentSection.get(file.value).map(_._2).getOrElse(0) + 1
    _currentSection = _currentSection.updated(file.value, (name, index))
    om.output(OutputManager.BLUE(s" Section ${index}: ${name}"))

  private[prooflib] var contextHypotheses: Map[sourcecode.File, Set[F.Expr[F.Prop]]] = Map.empty
  def context(e: F.Expr[F.Prop])(using file: sourcecode.File): Unit =
    contextHypotheses = contextHypotheses.updated(file, contextHypotheses.getOrElse(file, Set.empty) + e)

  val knownDefs: scala.collection.mutable.Map[F.Constant[?], Option[JUSTIFICATION]] = scala.collection.mutable.Map.empty
  val shortDefs: scala.collection.mutable.Map[F.Constant[?], Option[JUSTIFICATION]] = scala.collection.mutable.Map.empty

  def addSymbol(s: F.Constant[?]): Unit =
    theory.addSymbol(s.underlying)
    knownDefs.update(s, None)

  def getDefinition(label: F.Constant[?]): Option[JUSTIFICATION] = knownDefs.get(label) match {
    case None => throw new UserLisaException.UndefinedSymbolException("Unknown symbol", label, this)
    case Some(value) => value
  }
  def getShortDefinition(label: F.Constant[?]): Option[JUSTIFICATION] = shortDefs.get(label) match {
    case None => throw new UserLisaException.UndefinedSymbolException("Unknown symbol", label, this)
    case Some(value) => value
  }

  /**
   * An alias to create a Theorem
   */
  def makeTheorem(name: String, statement: K.Sequent, proof: K.SCProof, justifications: Seq[theory.Justification]): K.Judgement[theory.Theorem] =
    theory.theorem(name, statement, proof, justifications)

  // DEFINITION Syntax

  /**
   * Allows to create a definition by shortcut of a predicate symbol:
   */
  def makeSimpleDefinition(symbol: String, expression: K.Expression): K.Judgement[theory.Definition] =
    theory.definition(symbol, expression)

  /**
   * Prints a short representation of the given theorem or definition
   */
  def show(using om: OutputManager)(thm: JUSTIFICATION) = {
    if (thm.withSorry) om.output(thm.repr, Console.YELLOW)
    else om.output(thm.repr, Console.GREEN)
  }

  /**
   * Prints a short representation of the last theorem or definition introduced
   */
  def show(using om: OutputManager): Unit = last match {
    case Some(value) => show(value)
    case None => throw new NoSuchElementException("There is nothing to show: No theorem or definition has been proved yet.")
  }

}
