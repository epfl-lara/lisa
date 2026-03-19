package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.{FunctionalClass, TypedConstantFunctional}
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 *  Type theoretic interpretation of a constructor, that is a function whose type is
 *
 *  `c :: ∀X1, ..., Xn. T1 -> ... -> Tn -> ADT
 *
 *  @tparam N the number of type variables appearing in the definition of this
 *    constructor's ADT
 *  @param line the line at which this constructor is defined. Usually fetched
 *    automatically by the compiler. Used for error reporting
 *  @param file the file  in which this constructor is defined. Usually fetched
 *    automatically by the compiler. Used for error reporting
 *  @param semantic the set theoretic semantic constructor
 */
// class Constructor[N <: Arity] private[ADTv2] (using
class Constructor[N <: Arity]  (using
    line: sourcecode.Line,
    file: sourcecode.File
)(private[ADTv2] val semantic: SemanticConstructor[N])
    extends TypedConstantFunctional[Ind](
      semantic.fullName,
      FunctionalClass(
        // List.fill(semantic.typeArity)(None),
        // semantic.typeVariablesSeq.toList,
        Nil,
        Nil,
        semantic.typ
      ),
      semantic.intro
    ) {

  /**
   *  Name of the constructor
   *
   *  e.g `list/cons` or `list/nil`
   */
  val name = semantic.fullName

  /**
   *  Theorem --- Introduction rule
   *
   *  `c :: ∀X1, ..., Xn. T1 -> ... -> Tn -> ADT
   *
   *  where `c` is this constructor, `ADT` the ADT it belongs to and `T1, ..., Tn` the
   *  domains of the constructor's arguments. X1, ..., Xn are the type variables of the
   *  ADT.
   */
  val intro = THM(
    semantic.intro.statement,
    s"${name}/introduction",
    line.value,
    file.value,
    Theorem
  )(have(semantic.intro))

  /**
   *  Theorem --- Injectivity
   *
   *  ` c(x1, ..., xn) = c(y1, ..., yn) <=> x1 = y1 /\ ... /\ xn = yn`
   */
  lazy val injectivity = THM(
    semantic.injectivity.statement,
    s"${name}/injectivity",
    line.value,
    file.value,
    Theorem
  )(have(semantic.injectivity))

  /** Type variables appearing in the signature of this constructor */
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
}
