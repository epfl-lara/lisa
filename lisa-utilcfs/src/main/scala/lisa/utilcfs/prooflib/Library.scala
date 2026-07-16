package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.K.given
import lisa.utilcfs.fol.FOL.*

import scala.collection.mutable
import scala.collection.View

abstract class Library:
  val theory: K.Theory = K.Theory.empty
  given K.Theory = theory

  private val definitions = mutable.HashMap.empty[K.Constant, Thm]
  private val theoremByFullName = mutable.LinkedHashMap.empty[String, Theorem]
  private val theoremByShortName = mutable.HashMap.empty[String, Vector[Theorem]]
  private var sectionIndex = 0

  def addSymbol(symbol: Constant[?]): Unit =
    theory.addSymbol(symbol.underlying)

  def Axiom(formula: Expr[Prop]): Thm =
    val statement = Sequent(Set.empty, Set(formula))
    K.Axiom(using theory)(statement.underlying) match
      case Right(thm) => Thm(statement, thm)

  private def leadingVars(e: Expr[?]): Seq[Variable[?]] =
    e match
      case Abs(v, body) => v +: leadingVars(body)
      case _ => Seq.empty

  protected def registerDefinition[S](constant: Constant[S], definition: K.Thm): Thm =
    val thm = Thm(definition)
    definitions.update(constant.underlying, thm)
    thm

  def DEF[S: Sort](using name: sourcecode.FullName)(expression: Expr[S]): Constant[S] =
    val cst = constant[S](name.value)
    val vars = leadingVars(expression)
    K.Definition(using theory)(cst.underlying, vars.map(_.underlying), expression.underlying) match
      case Right(definition) =>
        registerDefinition(cst, definition)
        cst
      case Left(error) =>
        throw new IllegalArgumentException(s"Invalid definition ${name.value}: $error")

  extension [S](constant: Constant[S])
    def definition: Thm =
      definitions.getOrElse(constant.underlying, throw new NoSuchElementException(s"No definition registered for $constant."))

    def shortDefinition: Thm =
      definition

  class DirectDefinition[S: Sort](fullName: String, line: Int | sourcecode.Line, file: String | sourcecode.File)(expression: Expr[S], vars: Seq[Variable[?]]):
    val cst: Constant[S] = constant[S](fullName)
    K.Definition(using theory)(cst.underlying, vars.map(_.underlying), expression.underlying) match
      case Right(definition) => registerDefinition(cst, definition)
      case Left(error) => throw new IllegalArgumentException(s"Invalid definition $fullName: $error")

  def section(name: String)(using output: OutputManager, file: sourcecode.File): Unit =
    sectionIndex += 1
    output.section(sectionIndex, name, file.value)

  /**
   * Provides access to theorems in the library.
   */
  object theorems:
    /**
     * Mutably update the named theorem registry
     */
    private[prooflib] def register(theorem: Theorem): Unit =
      val fullName = theorem.fullName.toString
      require(!theoremByFullName.contains(fullName), s"Theorem $fullName is already registered.")
      theoremByFullName.update(fullName, theorem)
      theoremByShortName.updateWith(theorem.shortName):
        case Some(existing) => Some(existing :+ theorem)
        case None => Some(Vector(theorem))

    /**
      * A view over all named registered theorems.
      */
    def all: View[Theorem] =
      theoremByFullName.values.view

    /**
     * Lookup a theorem by full or short name (in that order of preference).
     */
    def get(name: String): Option[Theorem] =
      getFull(name).orElse(getShort(name))

    /**
      * Lookup a theorem by full name.
      */
    def getFull(fullName: String): Option[Theorem] =
      theoremByFullName.get(fullName)

    /**
     * Lookup a theorem by short name, if the short name is unambiguous.
     */
    def getShort(shortName: String): Option[Theorem] =
      theoremByShortName.get(shortName) match
        case Some(Vector(single)) => Some(single)
        case _ => None
