package lisa.kernel.fol

/**
 * The concrete implementation of first order logic.
 * All its content can be imported using a single statement:
 * <pre>
 * import lisa.fol.FOL._
 * </pre>
 */
object FOL extends FormulaDefinitions with EquivalenceChecker with Substitutions {}
