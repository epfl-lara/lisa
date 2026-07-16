package lisa.maths.SetTheory.Base

/**
 * This file defines the most common variable symbols (x, y, z, etc.) and their
 * types for a consistent use through the standard library.
 *
 * Symbols defined here must have an unambiguous and widely accepted meaning.
 */
object Symbols extends lisa.Main {

  /**
   * Variable symbols
   */
  val x, y, z: Variable[Ind] = variable[Ind]
  val a, b, c, d: Variable[Ind] = variable[Ind]

  /**
   * Sets
   */
  val A, B, C, D: Variable[Ind] = variable[Ind]
  val X, Y: Variable[Ind] = variable[Ind]

  /**
   * Function symbols
   */
  val f, g, h: Variable[Ind] = variable[Ind]

  /**
   * Class-function symbols. Must be capitalized.
   */
  val F: Variable[Ind >>: Ind] = variable[Ind >>: Ind]

  /**
   * Predicate (class) symbols
   */
  val P, φ: Variable[Ind >>: Prop] = variable[Ind >>: Prop]

}
