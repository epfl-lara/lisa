package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.{FunctionalClass, TypedConstantFunctional}

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*

/**
 *  Type theoretic function over algebraic data types. Its definition is the direct sum of
 *  the definitions of its constructors. Comes with introduction and elimination rules.
 *
 *  @constructor gives a type theoretic interpretation to a set theoretic function over an
 *    ADT
 *  @tparam N the number of type variables appearing in the definition of this function's
 *    domain
 *  @param line the line at which this ADT is defined. Usually fetched automatically by
 *    the compiler. Used for error reporting
 *  @param file the file in which this ADT is defined. Usually fetched automatically by
 *    the compiler. Used for error reporting
 *  @param semantic the semantic set theoretic function
 *  @param adt the domain of this function
 */
// private
class ADTFunction[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
    private val semantic: SemanticFunction[N],
    private val adt: ADT[N]
) extends TypedConstantFunctional[Ind](
      semantic.id,
      FunctionalClass(
        // Seq.fill(underlying.typeArity)(any),
        // underlying.typeVariablesSeq,
        Nil, // As a placeholder
        Nil, // As a placeholder
        semantic.typ
      ),
      semantic.intro
    ) {

  /** Name of the function */
  val name = semantic.fullName

  /**
   *  Theorem --- Elimination rules
   *
   *  `f * (c * x1 * ... * xn) = case(c, x1, ..., xn)`
   *
   *  That is, when this function is applied to a constructor, it returns the
   *  corresponding case.
   */
  val elim: Map[Constructor[N], THM] = adt.constructors.map(c =>
    (
      c,
      THM(
        semantic.shortDefinition(c.semantic).statement,
        s"${name}/elimination: ${c.name} case",
        line.value,
        file.value,
        Theorem
      )(have(semantic.shortDefinition(c.semantic)))
    )
  ).toMap

  /** Alias for [[this.elim]] */
  val shortDefinition: Map[Constructor[N], THM] = elim

  /**
   *  Theorem --- Introduction rule
   *
   *  `∀X1, ..., Xn. f(X1, ..., Xn) : ADT(X1, ..., Xn) -> T`
   *
   *  where `f` is this function, `ADT` the ADT it takes argument and `T` its return type.
   */
  val intro: THM = THM(
    semantic.intro.statement,
    s"${name}/introduction",
    line.value,
    file.value,
    Theorem
  )(have(semantic.intro))

  /** Type variables in the signature of the function */
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
}
