package lisa.kernel.proof

import lisa.kernel.fol.FOL.*

import scala.collection.mutable

sealed trait Theory:
  def defines(cst: Constant): Boolean
  def contains(expression: Expression): Boolean

  // definitions can only be registered by the respective kernel step
  protected[kernel] def registerDefinition(cst: Constant, definition: Thm): Unit

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

final class MutableTheory (
    private val symbols: mutable.Map[Identifier, Constant],
    private val definitions: mutable.Map[Constant, Option[Thm]]
) extends Theory:
  def defines(cst: Constant): Boolean =
    definitions.get(cst).isDefined

  def contains(expression: Expression): Boolean = expression match
    case _: Variable => true
    case c: Constant => symbols.get(c.id).contains(c)
    case Application(f, arg) => contains(f) && contains(arg)
    case Lambda(_, body) => contains(body)

  // definitions can only be registered by the respective kernel step
  protected[kernel] def registerDefinition(cst: Constant, definition: Thm): Unit =
    require(!defines(cst), s"Constant ${cst.id} is already defined in the theory")
    symbols.update(cst.id, cst)
    definitions.update(cst, Some(definition))

  def addSymbol(cst: Constant): Unit =
    if !symbols.contains(cst.id) then
      symbols.update(cst.id, cst)

  def getDefinition(cst: Constant): Option[Thm] =
    definitions.get(cst).flatten

  def getSymbol(id: Identifier): Option[Constant] =
    symbols.get(id)

  def language: Set[Constant] =
    symbols.values.toSet

object Theory:
  private val baseSymbols: Seq[Constant] =
    Seq(equality, top, bot, and, or, neg, implies, iff, forall, exists, epsilon)

  def empty: Theory =
    val symbols = baseSymbols.map(c => c.id -> c).to(mutable.Map)
    val definitions = baseSymbols.map(c => c -> Option.empty[Thm]).to(mutable.Map)
    MutableTheory(symbols, definitions)
