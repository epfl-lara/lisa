package lisa.maths.SetTheory.Types.ADTv2.backends

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ADTSpec

/**
 * Capability interface that isolates ADTv2 from concrete theorem prover APIs.
 *
 * The goal is to keep interpreters backend-agnostic: they request capabilities
 * (build terms, build formulas, register theorems) without depending on a
 * specific LISA version.
 */
trait Backend {

  // ---------------------------------------------------------------------------
  // Handle Types
  // ---------------------------------------------------------------------------

  /** Opaque reference to a symbol/definition in the target backend. */
  type SymbolHandle

  /** Opaque reference to a logical formula in the target backend. */
  type FormulaHandle

  /** Opaque reference to a theorem/derived fact in the target backend. */
  type TheoremHandle

  /** Opaque reference to a term/expression in the target backend. */
  type TermHandle

  // ---------------------------------------------------------------------------
  // Capability Group 1: Symbol and Definition Creation
  // ---------------------------------------------------------------------------

  /**
   * Create or register a named symbol in the backend.
   *
   * @param name logical name of the symbol to create.
   * @return a handle to the created symbol.
   */
  def symbol(name: String): SymbolHandle

  /**
   * Define a symbol by giving it a body term.
   *
   * @param name logical name of the new definition.
   * @param body defining term for the symbol.
   * @return a handle to the resulting definition symbol.
   */
  def define(name: String, body: TermHandle): SymbolHandle

  /**
   * High-level ADT registration entry point.
   *
   * This is kept as a transitional hook for the first vertical slice.
   * Longer term, interpreters may orchestrate ADT construction through lower
   * level primitives from this trait.
   */
  def defineADT(spec: ADTSpec): ADTResult

  // ---------------------------------------------------------------------------
  // Capability Group 2: Term Construction
  // ---------------------------------------------------------------------------

  /** Build a variable term. */
  def variable(name: String): TermHandle

  /** Apply a symbol to term arguments. */
  def apply(symbol: SymbolHandle, args: Seq[TermHandle]): TermHandle

  // ---------------------------------------------------------------------------
  // Capability Group 3: Formula Construction
  // ---------------------------------------------------------------------------

  /** Build an equality formula. */
  def equality(lhs: TermHandle, rhs: TermHandle): FormulaHandle

  /** Build an implication formula. */
  def implies(premise: FormulaHandle, conclusion: FormulaHandle): FormulaHandle

  /** Build a conjunction formula from all provided conjuncts. */
  def conjunction(conjuncts: Seq[FormulaHandle]): FormulaHandle

  /** Build a universal quantification. */
  def forall(variableName: String, domain: TermHandle, body: FormulaHandle): FormulaHandle

  /** Build an existential quantification. */
  def exists(variableName: String, domain: TermHandle, body: FormulaHandle): FormulaHandle

  // ---------------------------------------------------------------------------
  // Capability Group 4: Typing and Theorem Registration
  // ---------------------------------------------------------------------------

  /** Build the typing judgement "term has type tpe" as a formula. */
  def hasType(term: TermHandle, tpe: TermHandle): FormulaHandle

  /**
   * Register a theorem from a backend-native statement handle.
   *
   * @param name user-facing theorem name.
   * @param statement theorem statement formula.
   * @return theorem handle registered by the backend.
   */
  def theorem(name: String, statement: FormulaHandle): TheoremHandle

  /** Return a stable label/identifier for a theorem handle. */
  def theoremLabel(thm: TheoremHandle): String

  // ---------------------------------------------------------------------------
  // Data Returned by High-Level ADT Registration
  // ---------------------------------------------------------------------------

  /**
   * Summary of artifacts created for a single ADT declaration.
   *
   * @param typeSymbol symbol representing the ADT itself.
   * @param constructors constructor symbols by constructor name.
   * @param constructorTypes typing theorem/formula handle per constructor.
   * @param discriminators discriminator symbols (e.g. is_nil, is_cons).
   * @param selectors selector symbols for constructor fields.
   * @param inductionTheorem theorem handle for structural induction.
   */
  final case class ADTResult(
    typeSymbol: SymbolHandle,
    constructors: Map[String, SymbolHandle],
    constructorTypes: Map[String, FormulaHandle],
    discriminators: Map[String, SymbolHandle],
    selectors: Map[String, Seq[SymbolHandle]],
    inductionTheorem: TheoremHandle
  )
}
