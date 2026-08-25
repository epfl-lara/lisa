package lisa.kernel.proof

import lisa.kernel.fol.FOL.*

import scala.collection.mutable

sealed trait Theory:
  def defines(cst: Constant): Boolean
  def contains(expression: Expression): Boolean

  // definitions can only be registered by the respective kernel step
  protected [proof] def registerDefinition(cst: Constant, definition: Thm): Unit

  def contains(sequent: Sequent): Boolean =
    sequent.left.forall(contains) && sequent.right.forall(contains)

  /**
    * Add a symbol to the theory.
    *
    * However, the use of this method precludes the symbol from being defined in
    * the future.
    *
    * @param cst the symbol to add
    */
  def addSymbol(cst: Constant): Unit

  def makeSequentBelongToTheory(sequent: Sequent): Unit =
    sequent.left.foreach(makeFormulaBelongToTheory)
    sequent.right.foreach(makeFormulaBelongToTheory)

  def makeFormulaBelongToTheory(expression: Expression): Unit =
    expression.constants.foreach(addSymbol)

  def getDefinition(cst: Constant): Option[Thm]
  def getSymbol(id: Identifier): Option[Constant]
  def language: Set[Constant]

private final class MutableTheory(
    symbols: Map[Identifier, Constant],
    definitions: Map[Constant, Option[Thm]]
) extends Theory:
  private val symbolTable = mutable.Map.from(symbols)
  private val definitionTable = mutable.Map.from(definitions)

  def defines(cst: Constant): Boolean =
    definitionTable.get(cst).isDefined

  def contains(expression: Expression): Boolean = expression match
    case _: Variable => true
    case c: Constant => symbolTable.get(c.id).contains(c)
    case Application(f, arg) => contains(f) && contains(arg)
    case Lambda(_, body) => contains(body)

  // definitions can only be registered by the respective kernel step
  protected [proof] def registerDefinition(cst: Constant, definition: Thm): Unit =
    require(!defines(cst), s"Constant ${cst.id} is already defined in the theory")
    symbolTable.update(cst.id, cst)
    definitionTable.update(cst, Some(definition))

  def addSymbol(cst: Constant): Unit =
    if !symbolTable.contains(cst.id) then
      symbolTable.update(cst.id, cst)

  def getDefinition(cst: Constant): Option[Thm] =
    definitionTable.get(cst).flatten

  def getSymbol(id: Identifier): Option[Constant] =
    symbolTable.get(id)

  def language: Set[Constant] =
    symbolTable.values.toSet

object Theory:
  private val baseSymbols: Seq[Constant] =
    Seq(equality, top, bot, and, or, neg, implies, iff, forall, exists, epsilon)

  def empty: Theory =
    val symbols = baseSymbols.map(c => c.id -> c).toMap
    val definitions = baseSymbols.map(c => c -> Option.empty[Thm]).toMap
    new MutableTheory(symbols, definitions)
