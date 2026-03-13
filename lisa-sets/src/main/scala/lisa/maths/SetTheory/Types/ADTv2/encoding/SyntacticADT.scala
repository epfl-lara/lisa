package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

type **[A, N <: Arity] = Tuple

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
  val typeVariablesSeq: Seq[Variable[Ind]] =
    typeVariables.asInstanceOf[Product].productIterator.map(_.asInstanceOf[Variable[Ind]]).toSeq

  /** Number of type variables used in the definition of this ADT */
  val typeArity: N = typeVariablesSeq.length.asInstanceOf[N]
}
