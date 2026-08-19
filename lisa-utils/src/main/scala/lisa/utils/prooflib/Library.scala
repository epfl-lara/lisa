package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.K.given
import lisa.utils.fol.FOL._

import scala.collection.View
import scala.collection.mutable

class Library:
  val theory: K.Theory = K.Theory.empty
  given K.Theory = theory

  // export relevant theory methods

  /**
   * Check if a constant is defined in the library.
   */
  def defines[S](cst: Constant[S]): Boolean = theory.defines(cst.underlying)

  /**
   * Check if an expression is contained in the library, i.e., all constants in
   * the expression are defined or declared in the library.
   */
  def contains[S](expression: Expr[S]): Boolean = theory.contains(expression.underlying)

  /**
   * Declare a constant symbol in the library. This does not define the symbol,
   * but allows it to be used in expressions. 
   *
   * Note: this precludes the symbol from being defined in the future.
   */
  def addSymbol[S](symbol: Constant[S]): symbol.type = 
    theory.addSymbol(symbol.underlying)
    symbol

  /**
   * All constants defined in this library with a certified definition and the
   * expression used to define them. 
   * 
   * Invariant: key (constant) and value (expression) sorts are identical.
   */
  private val definitions = mutable.HashMap.empty[Constant[?], (Thm, Expr[?])]
  
  // theorem registry
  // TODO: does this need to be thread safe?
  private val theoremByFullName = mutable.LinkedHashMap.empty[String, Theorem]
  private val theoremByShortName = mutable.HashMap.empty[String, Vector[Theorem]]
  
  // section data, currently only for display
  private var sectionIndex = 0

  sealed trait LibraryException extends Exception
  case class AlreadyDefined(name: String, originalExpr: Expr[?], newExpr: Expr[?]) extends LibraryException:
    override def getMessage: String = s"Constant $name is already defined with expression $originalExpr, cannot redefine with $newExpr."

  /**
   * Declare an axiom in this library. The axiom is added to the theory and the
   * underlying registered theorem is returned. 
   *
   * Intended for internal use. For external use, see
   * [[lisa.utils.prooflib.BasicStep.Axiom]]. The result type is intentionally
   * opaque to discourage use.
   */
  def Axiom(file: sourcecode.File, line: sourcecode.Line)(statement: Sequent): K.Axiom.Result[K.Thm] =
    // we don't yet store axioms in the library, but theorems do accumulate them
    // instead. if we store them in multiple places, this could lead to aliasing
    // and cause unnecessary computation at every step that encounters them. the
    // file and line should be stored with the axiom for tracking.
    K.Axiom(using theory)(statement.underlying)

  /**
   * The leading bouond variables of an expression, in order of appearance. 
   */
  private def leadingVars(e: Expr[?]): Seq[Variable[?]] =
    @annotation.tailrec
    def leadingTailrec(e: Expr[?], acc: List[Variable[?]]): List[Variable[?]] =
      e match
        case Abs(v, body) => leadingTailrec(body, v :: acc)
        case _ => acc

    leadingTailrec(e, Nil).reverse

  /**
    * The defining statement for a constant. Assumes that the arity of the
    * constant matches the sort and number of provided variables and the
    * provided expression and constant.
    */
  private def definitionStatement[S](constant: Constant[S], expression: Expr[S], vars: Seq[Variable[?]]): Sequent =
    val appliedConstant = constant #@@ vars
    val appliedExpression = expression #@@ vars
    val formula =
      if appliedConstant.sort == K.Prop then 
        appliedConstant.asInstanceOf[Expr[Prop]] <=> appliedExpression.asInstanceOf[Expr[Prop]]
      else 
        appliedConstant.asInstanceOf[Expr[Ind]] === appliedExpression.asInstanceOf[Expr[Ind]]
    
    () |- formula

  private inline def storeDefinition[S](constant: Constant[S], expr: Expr[S], defn: Thm): (constant.type, Thm) =
    definitions.update(constant, (defn, expr))
    constant -> defn

  /**
    * Define a constant with the given name and expression. 
    * 
    * Intended for internal use. For external use, see [[DEF]].
    * 
    * Use discouraged largely to avoid name conflicts.
    * 
    * Synchronizes against the definitions registry.
    *
    * @throws AlreadyDefined if the constant is already defined (even if with the same expression).
    */
  def define[S: Sort](name: String, expression: Expr[S]): (Constant[S], Thm) =
    definitions.synchronized:
      val cst = constant[S](name)
      if defines(cst) then
        val (_, existing) = definitions(cst)
        throw AlreadyDefined(name, existing, expression)
      else
        val vars = leadingVars(expression)
        val thm = 
          K.Definition(using theory)(cst.underlying, vars.map(_.underlying), expression.underlying) match
            case Right(definition) =>
              definition
            case Left(error) =>
              throw new IllegalArgumentException(s"Invalid definition ${name}: $error")

        val stmt = definitionStatement(cst, expression, vars)
        val wrapped = Thm(stmt, thm)

        storeDefinition(cst, expression, wrapped)

  /**
   * Define a new constant with the given expression.
   *
   * Synchronizes against the definitions registry too avoid parallel
   * definitions.
   *
   * @example `val c = DEF(λ(x, x ∪ x))` defines a new constant `c` with the
   * expression `λ(x, x ∪ x)`. `c.definition` proves `⊢ c(x) = x ∪ x`.
   *
   * @throws AlreadyDefined if the constant is already defined (even if with the
   * same expression).
   */
  def DEF[S: Sort](using name: sourcecode.FullName)(expression: Expr[S]): Constant[S] =
    val (cst, _) = define(name.value, expression)
    cst

  /**
    * **[UNSAFE]**. Register or override a definition for a registered constant.
    *
    * Should only be used when necessary, e.g. with theory symbols defined by
    * axioms. This allows them to still be looked up by [[Constant.definition]]
    * and used in proofs, but does not guarantee that the definition has the
    * otherwise expected shape as with other definitions.
    */
  def registerDefinition[S](constant: Constant[S], definition: Thm): (constant.type, Thm) =
    definitions.synchronized:
      storeDefinition(constant, constant, definition)

  extension [S](constant: Constant[S])
    /**
      * The defining theorem for this constant. Theorem expected to be of the
      * form `⊢ cst(vars) = expr(vars)` or `⊢ cst(vars) ↔ expr(vars)` depending
      * on the sort of the constant.
      *
      * @throws NoSuchElementException if the constant is not defined in this
      * library, or does not have a registered definition (due to
      * [[addSymbol]]).
      */
    def definition: Thm =
      definitions
        .getOrElse(constant, throw new NoSuchElementException(s"No definition registered for $constant."))
        ._1

  def section(name: String)(using output: OutputManager, file: sourcecode.File): Unit =
    sectionIndex += 1
    output.section(sectionIndex, name, file.value)

  /**
   * Provides access to theorems in the library.
   */
  object theorems:
    /**
     * Mutably update the named theorem registry.
     *
     * @throws IllegalArgumentException if a theorem with the same full name is
     * already registered.
     */
    private[prooflib] def register(theorem: Theorem): Unit =
      val fullName = theorem.fullName.value
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
     * Lookup a theorem by full or short name (in that order of availability).
     *
     * @return `Some(theorem)` if a unique matching theorem is found. `None` if
     * no theorem with the given name is found. Or if there is a matching short
     * name, but is ambiguous.
     */
    def get(name: String): Option[Theorem] =
      getFull(name).orElse(getShort(name))

    /**
     * Lookup a theorem by full name.
     */
    def getFull(fullName: String): Option[Theorem] =
      theoremByFullName.get(fullName)

    /**
     * Lookup a theorem by short name, if the short name is unambiguous. `None`
     * otherwise. Use [[getAllShort]] to retrieve all theorems with a given
     * short name.
     */
    def getShort(shortName: String): Option[Theorem] =
      val all = getAllShort(shortName)
      if all.size == 1 then Some(all.head) else None

    /**
     * Lookup all theorems with a given short name. Returns an empty sequence if
     * no theorems are found.
     */
    def getAllShort(shortName: String): Seq[Theorem] =
      theoremByShortName.getOrElse(shortName, Vector.empty)
