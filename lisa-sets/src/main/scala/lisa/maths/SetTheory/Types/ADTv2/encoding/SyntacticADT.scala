package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

/** Heterogeneous tuple encoded as a Seq. N represents the arity (number of elements). */
type **[A, N <: Arity] = Seq[A]

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
 *    - `SyntacticADTIntroduction`: properties of the introduction-function image.
 *    - `SyntacticADTHeight`: height-function characterization and monotonicity.
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
class SyntacticADT[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
    val name: String,
    val constructors: Seq[SyntacticConstructor],
    val typeVariables: Variable[Ind] ** N
) extends SyntacticADTInduction[N] {

  protected final def sourceLine: sourcecode.Line = line

  protected final def sourceFile: sourcecode.File = file

  /** Sequence of type variables used in the definition of this ADT */
  val typeVariablesSeq: Seq[Variable[Ind]] = typeVariables

  /** Number of type variables used in the definition of this ADT */
  val typeArity: N = typeVariablesSeq.length.asInstanceOf[N]


  val externalHeight = isHeight
  val externalHeightMonotonic = heightMonotonic
  val externalHeightSuccessorStrong = heightSuccessorStrong
  val externalTermHasHeight = termHasHeight
  val externalTermsHaveHeight = termsHaveHeight
}
