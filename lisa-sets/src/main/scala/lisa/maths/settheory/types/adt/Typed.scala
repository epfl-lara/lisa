/**
 * Gives a type theoretic interpretation to algebraic data types and functions over them.
 */

package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{*, given}
import lisa.maths.settheory.types.TypeLib.{any}
import lisa.maths.settheory.types.TypeSystem.{TypedConstantFunctional, FunctionalClass}

/**
 * Type theoretic interpretation of a constructor, that is a function whose type is
 *
 *   `c :: ∀X1, ..., Xn. T1 -> ... -> Tn -> ADT
 *
 * @tparam N the number of type variables appearing in the definition of this constructor's ADT
 * @param line the line at which this constructor is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param file the file in which this constructor is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param underlying the set theoretic underlying constructor
 */
class Constructor[N <: Arity] private[adt] (using line: sourcecode.Line, file: sourcecode.File)(
    private[adt] val underlying: SemanticConstructor[N]
) extends TypedConstantFunctional[N](
      underlying.fullName,
      underlying.typeArity,
      FunctionalClass(Seq.fill(underlying.typeArity)(any), underlying.typeVariablesSeq, underlying.typ, underlying.typeArity),
      underlying.intro
    ) {

  /**
   * Name of the constructor
   *
   * e.g `list/cons` or `list/nil`
   */
  val name = underlying.fullName

  /**
   * Theorem --- Introduction rule
   *
   *   `c :: ∀X1, ..., Xn. T1 -> ... -> Tn -> ADT
   *
   * where `c` is this constructor, `ADT` the ADT it belongs to and `T1, ..., Tn` the domains of the constructor's arguments.
   * X1, ..., Xn are the type variables of the ADT.
   */
  val intro =
    THM(underlying.intro.statement, s"${name} introduction rule", line.value, file.value, Theorem) {
      have(underlying.intro)
    }

  /**
   * Theorem --- Injectivity
   *
   *   ` c(x1, ..., xn) = c(y1, ..., yn) <=> x1 = y1 /\ ... /\ xn = yn`
   */
  lazy val injectivity =
    THM(underlying.injectivity.statement, s"${name} injectivity", line.value, file.value, Theorem) {
      have(underlying.injectivity)
    }

  /**
   * Type variables appearing in the signature of this constructor
   */
  val typeVariables: Variable ** N = underlying.typeVariables
}

/**
 * Type theoretic polymorphic inductive datatype. Comes with a structural induction schema, injection and pattern matching.
 *
 * @tparam N the number of type variables appearing in the definition of this ADT
 * @param line the line at which this ADT is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param file the file in which this ADT is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param underlying
 * @param constructors
 */
class ADT[N <: Arity] private[adt] (using line: sourcecode.Line, file: sourcecode.File)(
    private[adt] val underlying: SemanticADT[N],
    private[adt] val constructors: Seq[Constructor[N]]
) {

  /**
   * Name of this ADT
   */
  val name = underlying.name

  /**
    * Identifier of this ADT.
    */
  val id: Identifier = underlying.id
  ADT.identifiersToADT.addOne(id -> this)

  /**
   * Theorem --- Structural induction principle
   *
   *  e.g. `P(nil) => (∀x :: T, l :: list(T). P(l) => P(cons(x, l)))) => ∀l :: list(T). P(l)`
   */
  lazy val induction =
    THM(underlying.induction.statement, s"${name} structural induction principle", line.value, file.value, Theorem) {
      have(underlying.induction)
    }

  /**
   * Theorem --- Elimination rules (Pattern Matching)
   *
   *    `x :: ADT |- ∃ x1, ..., xn. x = c1 * x1 * ... * xn \/ ... \/ ∃ x1, ..., xn'. x = cm * x1 * ... * xn'
   *
   * Every term of this ADT is an instance of one of its constructors.
   *
   * e.g. `∀l :: list(T). l = nil \/ ∃x, xs. l = cons(x, xs)`
   */
  lazy val elim =
    THM(underlying.elim.statement, s"${name} elimination rule", line.value, file.value, Theorem) {
      have(underlying.elim)
    }

  /**
   * Theorem --- Injectivity
   *
   *  ` c1 * x1 * ... * xn != c2 * y1 * ... * ym`
   *
   * Instances of different constructors are different.
   *
   * e.g. `cons(x, l) != nil`
   *
   * @param c1 the first constructor
   * @param c2 the second constructor
   */
  def injectivity(c1: Constructor[N], c2: Constructor[N]) =
    val injectivityLemma = underlying.injectivity(c1.underlying, c2.underlying)
    THM(injectivityLemma.statement, s"${c1.name}-${c2.name} injectivity", line.value, file.value, Theorem) {
      have(injectivityLemma)
    }

  /**
   * Type variables appearing in the signature of this ADT
   */
  val typeVariables: Variable ** N = underlying.typeVariables

  /**
   * Instantiate the type variables of this ADT with given types.
   * Checks the arity at runtime.
   *
   * @param args the types to instantiate the type variables with
   */
  def applyUnsafe(args: Term ** N): Term = underlying.term(args.toSeq)

  /**
   * Instantiate the type variables of this ADT with given types.
   * Checks the arity at runtime.
   *
   * @param args the types to instantiate the type variables with
   */
  def applySeq(args: Seq[Term]): Term = underlying.term(args)

  /**
   * Instantiate the type variables of this ADT with given types.
   * Checks the arity at runtime.
   *
   * TODO: wait Scala 3.4.2 to remove this method and extend Term ** N |-> Term instead
   *
   * @param args the types to instantiate the type variables with
   */
  def apply(args: Term*): Term = underlying.term(args)
}

private object ADT {
  /**
    * Global map from object identifiers to ADTs
    */
  private val identifiersToADT: scala.collection.mutable.Map[Identifier, ADT[?]] = scala.collection.mutable.Map.empty

  /**
    * Checks if a label is an ADT, and returns it if it is the case.
    *
    * @param l the label to check
    */
  def unapply(l: Label[?]): Option[ADT[?]] = getADT(l.id)

  /**
    * Checks if a term is an instance of an ADT and if it is the case, returns
    * the appropriate instances of the type variables.
    *
    * @param term the term to check
    */
  def unapply(obj: Term): Option[(ADT[?], Seq[Term])] = 
    obj match
      case l: Label[?] =>
        val lwidened: Label[?] = l 
        unapply(lwidened).map((_, Seq.empty))
      case AppliedFunctional(l, args) => unapply(l).map((_, args))
      case _ => None

  /**
    * Checks if a class is an instance of an ADT and if it is the case, returns
    * the appropriate instances of the type variables.
    *
    * @param c the class to check
    */
  def unapply(c: Class): Option[(ADT[?], Seq[Term])] = 
    c match
      case t: Term => unapply(t)
      case _ => None
    
  /**
    * Returns the ADT associated with an identifier.
    *
    * @param id the identifier of the ADT
    */
  def getADT(id: Identifier): Option[ADT[?]] = identifiersToADT.get(id)
}

/**
 * Type theoretic function over algebraic data types. Its definition is the direct sum of the definitions of its constructors.
 * Comes with introduction and elimination rules.
 *
 * @constructor gives a type theoretic interpretation to a set theoretic function over an ADT
 * @tparam N the number of type variables appearing in the definition of this function's domain
 * @param line the line at which this ADT is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param file the file in which this ADT is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param underlying the underlying set theoretic function
 * @param adt the domain of this function
 */
private class ADTFunction[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
    private val underlying: SemanticFunction[N],
    private val adt: ADT[N]
) extends TypedConstantFunctional[N](
      underlying.fullName,
      underlying.typeArity,
      FunctionalClass(Seq.fill(underlying.typeArity)(any), underlying.typeVariablesSeq, underlying.typ, underlying.typeArity),
      underlying.intro
    ) {

  /**
   * Name of the function
   *
   * e.g. list/length
   */
  val name = underlying.fullName

  /**
   * Theorem --- Elimination rules
   *
   *     `f * (c * x1 * ... * xn) = case(c, x1, ..., xn)`
   *
   * That is, when this function is applied to a constructor, it returns the corresponding case.
   */
  val elim: Map[Constructor[N], THM] = adt.constructors
    .map(c =>
      (
        c,
        THM(underlying.shortDefinition(c.underlying).statement, s"${name} elimination rule: ${c.name} case", line.value, file.value, Theorem) {
          have(underlying.shortDefinition(c.underlying))
        }
      )
    )
    .toMap

  /**
   * Alias for [[this.elim]]
   */
  val shortDefinition: Map[Constructor[N], THM] = elim

  /**
   * Theorem --- Introduction rule
   *
   *   `∀X1, ..., Xn. f(X1, ..., Xn) : ADT(X1, ..., Xn) -> T`
   *
   * where `f` is this function, `ADT` the ADT it takes argument and `T` its return type.
   */
  val intro: THM =
    THM(underlying.intro.statement, s"${name} introduction rule", line.value, file.value, Theorem) {
      have(underlying.intro)
    }

  /**
   * Type variables in the signature of the function
   */
  val typeVariables: Variable ** N = underlying.typeVariables
}
