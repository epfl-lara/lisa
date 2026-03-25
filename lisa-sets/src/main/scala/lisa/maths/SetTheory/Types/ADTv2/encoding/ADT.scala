package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
// import lisa.maths.SetTheory.Types.TypingHelpers.{FunctionalClass, TypedConstantFunctional}
import lisa.utils.prooflib.ProofTacticLib.Arity

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.typeExprToTerm

/**
 *  Type theoretic polymorphic inductive datatype. Comes with a structural induction
 *  schema, injection and pattern matching.
 *
 *  @tparam N the number of type variables appearing in the definition of this ADT
 *  @param line the line at which this ADT is defined. Usually fetched automatically by
 *    the compiler. Used for error reporting
 *  @param file the file in which this ADT is defined. Usually fetched automatically by
 *    the compiler. Used for error reporting
 *  @param semantic
 *  @param constructors
 */
// class ADT[N <: Arity] private[ADTv2] (using line: sourcecode.Line, file: sourcecode.File)(
class ADT[N <: Arity] (using line: sourcecode.Line, file: sourcecode.File)(
    // private[ADTv2] val semantic: SemanticADT[N],
    val semantic: SemanticADT[N],
    val constructors: Seq[Constructor[N]]
) {

  /** Name of this ADT */
  val name = semantic.name

  /** Identifier of this ADT. */
  // val id: Identifier = semantic.id
  ADT.namesToADT.addOne(name -> this)

  /**
   *  Theorem --- Structural induction principle
   *
   *  e.g.
   *  `P(nil) => (∀x :: T, l :: list(T). P(l) => P(cons(x, l)))) => ∀l :: list(T). P(l)`
   */
  lazy val induction = THM(
    semantic.induction.statement,
    s"${name}/induction",
    line.value,
    file.value,
    Theorem
  )(have(semantic.induction))

  /**
   *  Theorem --- Elimination rules (Pattern Matching)
   *
   *  `x :: ADT |- ∃ x1, ..., xn. x = c1 * x1 * ... * xn \/ ... \/ ∃ x1, ..., xn'. x = cm
   *  * x1 * ... * xn'
   *
   *  Every term of this ADT is an instance of one of its constructors.
   *
   *  e.g. `∀l :: list(T). l = nil \/ ∃x, xs. l = cons(x, xs)`
   */
  lazy val elim = THM(
    semantic.elim.statement,
    s"${name}/elimination",
    line.value,
    file.value,
    Theorem
  )(have(semantic.elim))

  /**
   *  Theorem --- Injectivity
   *
   *  ` c1 * x1 * ... * xn != c2 * y1 * ... * ym`
   *
   *  Instances of different constructors are different.
   *
   *  e.g. `cons(x, l) != nil`
   *
   *  @param c1 the first constructor
   *  @param c2 the second constructor
   */
  def injectivity(c1: Constructor[N], c2: Constructor[N]) =
    val injectivityLemma = semantic.injectivity(c1.semantic, c2.semantic)
    THM(
      injectivityLemma.statement,
      s"${c1.name}-${c2.name}/injectivity",
      line.value,
      file.value,
      Theorem
    )(have(injectivityLemma))

  /** Type variables appearing in the signature of this ADT */
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables

  /**
   *  Instantiate the type variables of this ADT with given types. Checks the arity at
   *  runtime.
   *
   *  @param args the types to instantiate the type variables with
   */
  def applyUnsafe(args: TypeExpr ** N): Expr[Ind] = 
    semantic.term(args.map(typeExprToTerm))

  /**
   *  Instantiate the type variables of this ADT with given types. Checks the arity at
   *  runtime.
   *
   *  @param args the types to instantiate the type variables with
   */
  def applySeq(args: Seq[TypeExpr]): Expr[Ind] = semantic.term(args.map(typeExprToTerm))

  /**
   *  Instantiate the type variables of this ADT with given types. Checks the arity at
   *  runtime.
   *
   *  TODO: wait Scala 3.4.2 to remove this method and extend TypeExpr ** N |-> TypeExpr
   *  instead
   *
   *  @param args the types to instantiate the type variables with
   */
  def apply(args: TypeExpr*): Expr[Ind] = semantic.term(args.map(typeExprToTerm))
}

object ADT {

  /** Global map from object identifiers to ADTs */
  private val namesToADT: scala.collection.mutable.Map[String, ADT[?]] =
    scala.collection.mutable.Map.empty

  /**
   *  Checks if a label is an ADT, and returns it if it is the case.
   *
   *  @param l the label to check
   */
  def unapply(t: TypeRef): Option[ADT[?]] = getADT(t.name)

  /**
   *  Checks if a term is an instance of an ADT and if it is the case, returns the
   *  appropriate instances of the type variables.
   *
   *  @param term the term to check
   */
  def unapply(obj: TypeExpr): Option[(ADT[?], Seq[TypeExpr])] = obj match
    case TypeRef(name) => getADT(name).map((_, Seq.empty))
    case TypeApply(name, args) => getADT(name).map((_, args))
    // case _ => None

  def getADT(name: String): Option[ADT[?]] = namesToADT.get(name)

  def allADTs: Iterable[ADT[?]] = namesToADT.values
}
