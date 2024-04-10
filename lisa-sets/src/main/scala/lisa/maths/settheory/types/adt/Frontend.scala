package lisa.maths.settheory.types.adt

export ADTSyntax.{ |, define, constructors, constructor_to_term, adt_to_term, function_to_term, Case, fun }
export lisa.maths.settheory.types.TypeSystem.*


/**
 * This object provides a DSL for defining algebraic data types (ADTs) in Lisa.
 *
 * This is an example of ADT definition in Lisa
 * {{{
 * val define(list: ADT, constructors(nil, cons)) = () | (x, list)
 * }}}
 * where `list`, `nil` and `cons` are new identifiers freely chosen by the user, referring respectively to the generated ADT
 * and its constructors, and `x` is a term variable.
 *
 * Formally, we define an ADT as a sequence of tuples where each tuple represents the signature of a constructor. Each tuple can either contain:
 * - a constant term (e.g. `emptySet`, or `pair(emptySet, emptySet)`)
 * - a term variable (e.g. `x`)
 * - a reference to the adt itself by using the identifier that the user is giving to the ADT (e.g. `myadt`)
 *
 * The syntax then consists of
 * {{{
 * val defined(idGivenToTheADT: ADT, constuctors(idGivenToFirstConstructor, ..., idGivenToLastConstructor)) = * tuple sequence *
 * }}}
 *
 * The user can then freely refer to the identifiers of the ADT and constructors in the rest of the program.
 * The identifer given to the ADT is of type [[TypedADT]] while the identifiers given to the constructors are of type [[TypedConstructor]].
 */
private[adt] object ADTSyntax {

//   import ADTTactic.*
  import ADTDefinitions.*
  import lisa.fol.FOL.*

  /**
   * Builder for defining the signature of a constructor.
   *
   * @param param the parameters of the constructor
   */
  case class ConstructorBuilder (private val param: Seq[ConstructorArgument]) {

    /**
     * The number of arguments the constructor takes
     */
    def size: Int = param.length

    /**
     * Merges the parameters of two constructors.
     *
     * @param b the other constructor
     */
    infix def ++(b: ConstructorBuilder): ConstructorBuilder = ConstructorBuilder(param ++ b.param.toSeq)

    /**
     * Converts this constructor into an ADT with a single constructor.
     */
    def toADTBuilder = ADTBuilder(Seq(this))

    /**
     * List of type variables appearing in the specification of this algebraic data type
     */
    def typeVariables: Seq[Variable] = param.flatMap(variables)

    /**
     * Combines two constructors into an ADT.
     *
     * @param b the other constructor
     */
    infix def |(b: ConstructorBuilder): ADTBuilder = this | b.toADTBuilder

    /**
     * Adds this constructor to an ADT.
     *
     * @param b the ADT to which the constructor is added
     */
    infix def |(b: ADTBuilder): ADTBuilder = toADTBuilder | b

    /**
     * Outputs the [[UntypedConstructor]] associated with this builder.
     *
     * @param name the name of the constructor
     */
    def build(variables1: Seq[Variable], variables2: Seq[Variable]): SyntacticConstructor = SyntacticConstructor(param, variables1, variables2)
  }

  /**
   *  Companion object for the [[ConstructorBuilder]] class.
   */
  object ConstructorBuilder {

    /**
     * Creates an empty [[ConstructorBuilder]].
     */
    def empty: ConstructorBuilder = ConstructorBuilder(Seq.empty)
  }

  trait ConstructorConverter[T] {

    /**
     * Converts a value into a [[ConstructorBuilder]].
     */
    def apply(t: T): ConstructorBuilder
  }

  /**
   * Converts a value into a [[ConstructorBuilder]].
   *
   * @param any the value to convert
   * @param c the converter that is used for the conversion
   */
  private def any_to_const[T](any: T)(using c: ConstructorConverter[T]): ConstructorBuilder = c(any)

  given unit_to_const: ConstructorConverter[Unit] with {

    /**
     * Converts a unit value into a constructor taking no arguments.
     */
    override def apply(u: Unit): ConstructorBuilder = ConstructorBuilder.empty
  }

  given empty_to_const: ConstructorConverter[EmptyTuple] with {

    /**
     * Converts an empty tuple into a constructor taking no arguments.
     */
    override def apply(t: EmptyTuple): ConstructorBuilder = ConstructorBuilder.empty
  }

  given term_to_const[T <: Term]: ConstructorConverter[T] with {

    /**
     * Converts a term into a constructor taking one non inductive argument.
     */
    override def apply(t: T): ConstructorBuilder = ConstructorBuilder(Seq(GroundType(t)))
  }

  given adt_to_const: ConstructorConverter[ADT] with {

    /**
     * Converts an ADT into a constructor taking one inductive argument.
     */
    override def apply(a: ADT): ConstructorBuilder = 
      if a == null then
        ConstructorBuilder(Seq(Self))
      else 
        ConstructorBuilder(Seq(GroundType(a)))
  }

  given adt_tuple_to_const[T <: Tuple](using ConstructorConverter[T]): ConstructorConverter[ADT *: T] with {

    /**
     * Converts a tuple prepended with a type into a constructor taking an argument and whose other arguments are deduced from
     * applying recursively the conversion to the tuple.
     */
    override def apply(t: ADT *: T): ConstructorBuilder =
      any_to_const(t.head) ++ any_to_const(t.tail)
  }


  given term_tuple_to_const[H <: Term, T <: Tuple](using ConstructorConverter[T]): ConstructorConverter[H *: T] with {

    /**
     * Converts a tuple prepended with a type into a constructor taking an argument and whose other arguments are deduced from
     * applying recursively the conversion to the tuple.
     */
    override def apply(t: H *: T): ConstructorBuilder =
      any_to_const(t.head) ++ any_to_const(t.tail)
  }

  extension [T1](left: T1)(using c1: ConstructorConverter[T1])
    /**
     * Converts two values into constructors and combines them into an ADT.
     *
     * @param right the other value to convert
     * @param c2 the implicit converter for the second value
     */
    infix def |[T2](right: T2)(using c2: ConstructorConverter[T2]): ADTBuilder = any_to_const(left) | any_to_const(right)

  case class ADTBuilder (private val constructors: Seq[ConstructorBuilder]) {

    /**
     * The number of constructors in the ADT.
     */
    def size: Int = constructors.length

    /**
     * Combines this ADT with another one.
     *
     * @param b the other ADT
     */
    infix def |(b: ADTBuilder): ADTBuilder = ADTBuilder(constructors ++ b.constructors)

    /**
     * Adds a constructor to this ADT.
     *
     * @param b the constructor to add
     */
    infix def |(b: ConstructorBuilder): ADTBuilder = this | b.toADTBuilder

    /**
     * Converts a value into a constructor and adds it to this ADT.
     *
     * @param t the value to convert
     * @param c the implicit converter
     */
    infix def |[T](t: T)(using c: ConstructorConverter[T]): ADTBuilder = this | any_to_const(t)

    /**
     * List of type variables appearing in the specification of this algebraic data type
     */
    val typeVariables: Seq[Variable] = constructors.flatMap(_.typeVariables)

    /**
     * Outputs the constructors of this ADT.
     *
     * @param names the names of the constructors
     */
    def build(names: Seq[String]): (ADT, constructors) =

      val trimmedNames = (if size == 0 then names else names.tail).take(size + 1)
      require(
        trimmedNames.length == constructors.length + 1,
        s"The number of new identifiers for constructors must match the given specification.\nNew identifiers: ${names.length - 1}, number of constructors: ${constructors.length}."
      )

      val typeVarsSet = typeVariables.toSet
      val syntacticCons = constructors.map(c => 
          c.build(Helpers.chooseVars("x", c.size, typeVarsSet), Helpers.chooseVars("y", c.size, typeVarsSet))
        )
      val syntacticADT = SyntacticADT(trimmedNames.head, syntacticCons, typeVariables)
      val semanticCons = trimmedNames.tail.zip(syntacticCons).map(SemanticConstructor(_, _, syntacticADT))
      val semanticADT = SemanticADT(syntacticADT, semanticCons)
      val cons = semanticCons.map(Constructor(_)) 
      (ADT(semanticADT, cons), new constructors(cons : _*))
  }

  /**
   *  Companion object for the [[ADTBuilder]] class.
   */
  object ADTBuilder {

    /**
     * Creates an empty [[ADTBuilder]].
     */
    def empty: ADTBuilder = ADTBuilder(Seq.empty)
  }

 

  /**
    * Lists all constructors of this ADT.
    */
  case class constructors(cons: Constructor*)

  /**
    * Companion object for the [[constructors]] class.
    */
  object constructors {
    def unapplySeq(adt: ADT): Seq[Constructor] = adt.constructors
  }


  object define {

    import scala.quoted._

    private inline def extractNames[T](e: T): Seq[String] = ${extractNames('{e})}

    private def extractNames[T](using Quotes)(e: Expr[T]) : Expr[Seq[String]]  =

      import quotes.reflect._


      val subscope = Symbol.spliceOwner.owner.owner.owner
      val scope = subscope.owner
      val tree = scope.tree

      case class traverser(s: Symbol) extends TreeTraverser {
        var reachedADT: Boolean = false 
        var constructorNames: Seq[String] = Seq.empty[String]

        override def traverseTree(tree: Tree)(owner: Symbol): Unit = tree match 
          case v : ValDef => 
            if !reachedADT then
              if v.symbol == s then
                constructorNames = constructorNames :+ v.symbol.name
                reachedADT = true
            else
              constructorNames = constructorNames :+ v.symbol.name

            super.traverseTree(tree)(owner)
          case _ => super.traverseTree(tree)(owner)
      }

      val trav = traverser(subscope)
      trav.traverseTree(tree)(scope)
      Expr(trav.constructorNames)

    /**
      * Extracts the constructors from an ADT.
      *
      * @param adt the ADT
      * @return a tuple containing the ADT and its constructors
      */
    private def extractConstructors(adt: ADT): (ADT, constructors) = (adt, constructors(adt.constructors : _*))

    inline def unapply(builder: ADTBuilder): (ADT, constructors) = builder.build(extractNames(builder))

    /**
      * Returns an ADT containing only one constructor out of a [[ConstructorBuilder]].
      * 
      * @param builder the builder of the unique constructor of the ADT
      */
    private inline def unapply(builder: ConstructorBuilder): (ADT, constructors) = unapply(builder.toADTBuilder)

    /**
      * Returns an ADT isomorphic to a given type. It has only one constructor taking as only argument an element of
      * the provided type.
      * Needs to be inline in order to fetch the name of the ADT and the constructor.
      *
      * @param t type given by the user
      */
    inline def unapply(t: Term): (ADT, constructors) = unapply(term_to_const(t))

    /**
      * Returns the unit type. This is an ADT containing only one value and hence having only one 
      * constructor (non-inductive and taking no arguments).
      * Needs to be inline in order to fetch the name of the ADT and the constructor.
      *
      * @param u user specification indicating that they want to generate the unit type
      */
    inline def unapply(u: Unit): (ADT, constructors) = unapply(unit_to_const(u))

    /**
      * Returns the empty type (also known as void or nothing). This is an empty ADT with no constructors.
      * Needs to be inline in order to fetch the name of the ADT.
      *
      * @param n user specification indicating that they want to generate the void type
      */
    inline def unapply(n: None.type): (ADT, constructors) = unapply(ADTBuilder.empty)

    /**
      * Returns a product type (also known as tuple). This is an ADT containing only one constructor.
      * Generally its arguments are non inductive as the opposite would lead to the empty type.
      * Needs to be inline in order to fetch the name of the ADT and the constructor.
      *
      * @param t user specification of the tuple
      */
    inline def unapply[T <: Tuple](t: (ADT | Term) *: T)(using ConstructorConverter[T]): (ADT, constructors) = 
      t.head match
        case a: ADT => unapply(any_to_const(a *: t.tail))
        case term: Term => unapply(any_to_const(term *: t.tail))
      

  }

  given constructor_to_term: Conversion[Constructor, Term] = c => c.applySeq(c.typeVariables)
  given adt_to_term: Conversion[ADT, Term] = adt => adt.apply(adt.typeVariables: _*)
  given function_to_term: Conversion[ADTFunction, Term] = fun => fun.apply(fun.typeVariables: _*)


  class CaseBuilder[T] {
    private val underlying = scala.collection.mutable.Map[SemanticConstructor, (Seq[Variable], T)]()
    def += (cons: Constructor, value: (Seq[Variable], T)) = underlying += (cons.underlying -> value)
    def build: Map[SemanticConstructor, (Seq[Variable], T)] = underlying.toMap
  }

  case class Case(cons: Constructor, vars: Variable*) {  
    def subproof (using proof: lisa.SetTheoryLibrary.Proof, line: sourcecode.Line, file: sourcecode.File, builder: CaseBuilder[proof.ProofStep])(subproof: proof.InnerProof ?=> Unit): Unit =
    //   //val botWithAssumptions = HaveSequent.this.bot ++ (proof.getAssumptions |- ())
    //   //val iProof: proof.InnerProof = new proof.InnerProof(Some(botWithAssumptions))
      val iProof: proof.InnerProof = new proof.InnerProof(None)
      subproof(using iProof)
      val proofStep = (new lisa.prooflib.BasicStepTactic.SUBPROOF(using proof)(None)(iProof)).judgement.validate(line, file).asInstanceOf[proof.ProofStep]
      builder += (cons, (vars, proofStep))
    
    def apply(body : Term)(using builder: CaseBuilder[Term]) = builder += (cons, (vars, body))
  }



  def fun(adt: ADT, returnType: Term)(using name: sourcecode.Name)(cases: CaseBuilder[Term] ?=> Unit): ADTFunction = {
    val builder = CaseBuilder[Term]
    cases(using builder)
    ADTFunction(SemanticFunction(name.value, adt.underlying, builder.build, returnType), adt)
  }

}