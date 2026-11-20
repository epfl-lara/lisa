package lisa.maths.SetTheory.Types.ADT.encoding

import lisa.maths.SetTheory.SetTheory._

/**
 *  Syntactic set theoretical interpretation of an algebraic data type. That is the least
 *  set closed under [[SyntacticConstructor]].
 *
 *  E.g. list is the smallest set containing nil and closed under the syntactic operation
 *  cons.
 *
 *  Injectivity between different constructors, introduction rules and structural
 *  induction are proved within this class.
 *
 *  ADT encoding is split into multiple traits (ordered by dependency):
 *    - `SyntacticADTBase`: shared logical encodings and core predicates.
 *    - `SyntacticADTInjectivity`: disjointness/injectivity of constructors.
 *    - `SyntacticADTHeight`: introduction-image lemmas plus height-function characterization and monotonicity.
 *    - `SyntacticADTTerm`: term definition from heights and introduction lemmas.
 *    - `SyntacticADTInduction`: structural induction principle.
 *    - `SyntacticADT`: concrete ADT class wiring those layers together.
 *
 *  @constructor creates a new algebraic data type out of a user specification.
 *  @param line the line at which the ADT is defined. Usually fetched automatically by the
 *    compiler. Used for error reporting
 *  @param file the file in which the ADT is defined. Usually fetched automatically by the
 *    compiler. Used for error reporting
 *  @param name the name of the ADT
 *  @param constructors constructors of the ADT
 *  @param typeVariables type variables used in the definition of this ADT
 */
class SyntacticADT(using line: sourcecode.Line, file: sourcecode.File)(
    val name: String,
    val constructors: Seq[SyntacticConstructor],
    val typeVariablesSeq: Seq[Variable[Ind]]
) extends SyntacticADTInduction {

  protected final def sourceLine: sourcecode.Line = line

  protected final def sourceFile: sourcecode.File = file

}
