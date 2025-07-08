package lisa.maths.SetTheory.Types.ADT

import lisa.utils.fol.FOL.*

/*

/** This object provides a DSL for defining algebraic data types (ADTs) and functions over ADT in Lisa.
 * For usage examples, please refer to the documentation of the package or the reference manual.
 */
object ADTSyntax {

  import ADTDefinitions.*
  import lisa.maths.settheory.SetTheory.{*, given}

  /** Builder for defining a constructor specification.
 *
 * @param param the parameters of the constructor
 */
  case class ConstructorBuilder(private val param: Seq[ConstructorArgument]) {

    /** The number of arguments the constructor takes
 */
    def size: Int = param.length

    /** Merges the parameters of two constructors.
 *
 * @param b the other constructor
 */
    infix def ++(b: ConstructorBuilder): ConstructorBuilder = ConstructorBuilder(param ++ b.param.toSeq)

    /** Converts this constructor into an ADT with a single constructor.
 */
    def toADTBuilder = ADTBuilder(Seq(this))

    /** Combines two constructors into an ADT.
 *
 * @param b the other constructor
 */
    infix def |(b: ConstructorBuilder): ADTBuilder = this | b.toADTBuilder

    /** Adds this constructor to an ADT.
 *
 * @param b the ADT to which the constructor is added
 */
    infix def |(b: ADTBuilder): ADTBuilder = toADTBuilder | b

    /** Outputs the [[UntypedConstructor]] associated with this builder.
 *
 * @param name the name of the constructor
 */
    def build(variables1: Seq[Variable[Ind]], variables2: Seq[Variable[Ind]]): SyntacticConstructor = SyntacticConstructor(param, variables1, variables2)
  }

  /**  Companion object for the [[ConstructorBuilder]] class.
 */
  object ConstructorBuilder {

    /** Creates an empty [[ConstructorBuilder]].
 */
    def empty: ConstructorBuilder = ConstructorBuilder(Seq.empty)
  }

  trait ConstructorConverter[T] {

    /** Converts a value into a [[ConstructorBuilder]].
 */
    def apply(t: T): ConstructorBuilder
  }

  /** Converts a value into a [[ConstructorBuilder]].
 *
 * @param any the value to convert
 * @param c the converter that is used for the conversion
 */
  private def any_to_const[T](any: T)(using c: ConstructorConverter[T]): ConstructorBuilder = c(any)

  given unit_to_const: ConstructorConverter[Unit] with {

    /** Converts a unit value into a constructor taking no arguments.
 */
    override def apply(u: Unit): ConstructorBuilder = ConstructorBuilder.empty
  }

  given empty_to_const: ConstructorConverter[EmptyTuple] with {

    /** Converts an empty tuple into a constructor taking no arguments.
 */
    override def apply(t: EmptyTuple): ConstructorBuilder = ConstructorBuilder.empty
  }

  given term_to_const[T <: Expr[Ind]]: ConstructorConverter[T] with {

    /** Converts a term into a constructor taking one non inductive argument.
 */
    override def apply(t: T): ConstructorBuilder = ConstructorBuilder(Seq(GroundType(t)))
  }

  given adt_to_const[N <: Arity]: ConstructorConverter[ADT[N]] with {

    /** Converts an ADT into a constructor taking one inductive argument.
 */
    override def apply(a: ADT[N]): ConstructorBuilder = ConstructorBuilder(Seq(Self))
  }

  given adt_tuple_to_const[N <: Arity, T <: Tuple](using ConstructorConverter[T]): ConstructorConverter[ADT[N] *: T] with {

    /** Converts a tuple prepended with a type into a constructor taking an argument and whose other arguments are deduced from
 * applying recursively the conversion to the tuple.
 */
    override def apply(t: ADT[N] *: T): ConstructorBuilder =
      any_to_const(t.head) ++ any_to_const(t.tail)
  }

  given term_tuple_to_const[H <: Expr[Ind], T <: Tuple](using ConstructorConverter[T]): ConstructorConverter[H *: T] with {

    /** Converts a tuple prepended with a type into a constructor taking an argument and whose other arguments are deduced from
 * applying recursively the conversion to the tuple.
 */
    override def apply(t: H *: T): ConstructorBuilder =
      any_to_const(t.head) ++ any_to_const(t.tail)
  }

  extension [T1](left: T1)(using c1: ConstructorConverter[T1])
    /** Converts two values into constructors and combines them into an ADT.
 *
 * @param right the other value to convert
 * @param c2 the implicit converter for the second value
 */
    infix def |[T2](right: T2)(using c2: ConstructorConverter[T2]): ADTBuilder = any_to_const(left) | any_to_const(right)

  /** Builder for defining ADT specifications.
 *
 * @param constructors the builders for each constructor of the ADT.
 */
  case class ADTBuilder(private val constructors: Seq[ConstructorBuilder]) {

    /** The number of constructors in the ADT.
 */
    def size: Int = constructors.length

    /** Combines this ADT with another one.
 *
 * @param b the other ADT
 */
    infix def |(b: ADTBuilder): ADTBuilder = ADTBuilder(constructors ++ b.constructors)

    /** Adds a constructor to this ADT.
 *
 * @param b the constructor to add
 */
    infix def |(b: ConstructorBuilder): ADTBuilder = this | b.toADTBuilder

    /** Converts a value into a constructor and adds it to this ADT.
 *
 * @param t the value to convert
 * @param c the implicit converter
 */
    infix def |[T](t: T)(using c: ConstructorConverter[T]): ADTBuilder = this | any_to_const(t)

    /** Outputs the corresponding ADT and its constructors.
 *
 * @tparam N the number of type variables appearing in the specification of the ADT
 * @param typeVariables the type variables of the ADT
 * @param names the names of the constructors and of the ADT
 */
    def build[N <: Arity](typeVariables: Variable[Ind] ** N, names: Seq[String]): (ADT[N], constructors[N]) =

      val trimmedNames = (if size == 0 then names else names.tail).take(size + 1)
      require(
        trimmedNames.length == constructors.length + 1,
        s"The number of new identifiers for constructors must match the given specification.\nNew identifiers: ${names.length - 1}, number of constructors: ${constructors.length}."
      )

      val typeVarsSet = typeVariables.toSeq.toSet
      val syntacticCons = constructors.map(c => c.build(nFreshIds(c.size, typeVarsSet, base = "x"), nFreshIds(c.size, typeVarsSet, base = "y")))
      val syntacticADT = SyntacticADT[N](trimmedNames.head, syntacticCons, typeVariables)
      val semanticCons = trimmedNames.tail.zip(syntacticCons).map(SemanticConstructor(_, _, syntacticADT))
      val semanticADT = SemanticADT[N](syntacticADT, semanticCons)
      val cons = semanticCons.map(Constructor(_))
      (ADT[N](semanticADT, cons), new constructors[N](cons*))

  }

  /**  Companion object for the [[ADTBuilder]] class.
 */
  object ADTBuilder {

    /** Creates an empty [[ADTBuilder]].
 */
    def empty: ADTBuilder = ADTBuilder(Seq.empty)

    /** Creates an empty [[ADTBuilder]].
 */
    def | = empty
  }

  /** Builder for defining polymorphic ADT specifications.
 *
 * @tparam N the number of type variables of the ADT
 * @param typeVariable the type variables of the ADT
 * @param specification the builder for ADT
 */
  case class PolymorphicADTBuilder[N <: Arity](typeVariables: Variable[Ind] ** N, specification: ADTBuilder) {

    /** Outputs the corresponding ADT and its constructors.
 *
 * @param names the names of the constructors and of the ADT
 */
    def build(names: Seq[String]) = specification.build(typeVariables, names)

    /** Adds a constructor to the ADT specification
 *
 * @param b the builder of the constructor
 */
    def |(b: ConstructorBuilder): PolymorphicADTBuilder[N] = PolymorphicADTBuilder(typeVariables, specification | b)

    /** Adds a constructor to the ADT specification
 *
 * @param t the value to be converted into a constructor
 */
    def |[T](t: T)(using ConstructorConverter[T]): PolymorphicADTBuilder[N] = |(any_to_const(t))
  }

  // Syntactic sugar for polymorphic ADT Builders

  extension (u: Unit)
    def -->(builder: ADTBuilder): PolymorphicADTBuilder[0] = PolymorphicADTBuilder[0](**(), builder)
    def -->(builder: ConstructorBuilder): PolymorphicADTBuilder[0] = -->(builder.toADTBuilder)
    def -->[T](t: T)(using ConstructorConverter[T]): PolymorphicADTBuilder[0] = -->(any_to_const(t))

  extension (v: Variable[Ind])
    def -->(builder: ADTBuilder): PolymorphicADTBuilder[1] = PolymorphicADTBuilder[1](**(v), builder)
    def -->(builder: ConstructorBuilder): PolymorphicADTBuilder[1] = -->(builder.toADTBuilder)
    def -->[T](t: T)(using ConstructorConverter[T]): PolymorphicADTBuilder[1] = -->(any_to_const(t))

  extension (v: (Variable[Ind], Variable[Ind]))
    def -->(builder: ADTBuilder): PolymorphicADTBuilder[2] = PolymorphicADTBuilder[2](**(v._1, v._2), builder)
    def -->(builder: ConstructorBuilder): PolymorphicADTBuilder[2] = -->(builder.toADTBuilder)
    def -->[T](t: T)(using ConstructorConverter[T]): PolymorphicADTBuilder[2] = -->(any_to_const(t))

  extension (v: (Variable[Ind], Variable[Ind], Variable[Ind]))
    def -->(builder: ADTBuilder): PolymorphicADTBuilder[3] = PolymorphicADTBuilder[3](**(v._1, v._2, v._3), builder)
    def -->(builder: ConstructorBuilder): PolymorphicADTBuilder[3] = -->(builder.toADTBuilder)
    def -->[T](t: T)(using ConstructorConverter[T]): PolymorphicADTBuilder[3] = -->(any_to_const(t))

  extension (v: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))
    def -->(builder: ADTBuilder): PolymorphicADTBuilder[4] = PolymorphicADTBuilder[4](**(v._1, v._2, v._3, v._4), builder)
    def -->(builder: ConstructorBuilder): PolymorphicADTBuilder[4] = -->(builder.toADTBuilder)
    def -->[T](t: T)(using ConstructorConverter[T]): PolymorphicADTBuilder[4] = -->(any_to_const(t))

  extension (v: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))
    def -->(builder: ADTBuilder): PolymorphicADTBuilder[5] = PolymorphicADTBuilder[5](**(v._1, v._2, v._3, v._4, v._5), builder)
    def -->(builder: ConstructorBuilder): PolymorphicADTBuilder[5] = -->(builder.toADTBuilder)
    def -->[T](t: T)(using ConstructorConverter[T]): PolymorphicADTBuilder[5] = -->(any_to_const(t))

  /** Lists all constructors of this ADT.
 */
  case class constructors[N <: Arity](cons: Constructor[N]*)

  /** Companion object for the [[constructors]] class.
 */
  object constructors {
    def unapplySeq[N <: Arity](adt: ADT[N]): Seq[Constructor[N]] = adt.constructors
  }

  /** Contains useful macros for ADT UI
 */
  object Macro {
    import scala.quoted._

    /** Extract all the scala identifiers defined in the same line or after an expression.
 *
 * @param e the expression around which the names are extracted
 */
    inline def extractNames[T](e: T): Seq[String] = ${ extractNames('{ e }) }

    /** Macro implementing [[this.extractNames]].
 *
 * @param e the quoted expression around which the names are extracted
 */
    private def extractNames[T](using Quotes)(e: Expr[T]): Expr[Seq[String]] =

      import quotes.reflect._

      val subscope = Symbol.spliceOwner.owner.owner.owner
      val scope = subscope.owner
      val tree = scope.tree

      case class traverser(s: Symbol) extends TreeTraverser {
        var reachedADT: Boolean = false
        var constructorNames: Seq[String] = Seq.empty[String]

        override def traverseTree(tree: Tree)(owner: Symbol): Unit = tree match
          case v: ValDef =>
            if !reachedADT then
              if v.symbol == s then
                constructorNames = constructorNames :+ v.symbol.name
                reachedADT = true
            else constructorNames = constructorNames :+ v.symbol.name

            super.traverseTree(tree)(owner)
          case _ => super.traverseTree(tree)(owner)
      }

      val trav = traverser(subscope)
      trav.traverseTree(tree)(scope)
      Expr(trav.constructorNames)
  }

  /** Syntax to define Algebraic Data Types
 */
  object define {

    /** Extracts the constructors from an ADT.
 *
 * @param adt the ADT
 * @return a tuple containing the ADT and its constructors
 */
    private def extractConstructors[N <: Arity](adt: ADT[N]): (ADT[N], constructors[N]) = (adt, constructors(adt.constructors*))

    /** Outputs a polymorphic ADT and constructors from a user specification
 * Needs to be inline in order to fetch the name of the ADT and the constructor.
 *
 * @param builder the builder user for specifying the ADT
 */
    inline def unapply[N <: Arity](builder: PolymorphicADTBuilder[N]): (ADT[N], constructors[N]) = builder.build(Macro.extractNames(builder))

    /** Outputs a (non polymorphic) ADT and constructors from a user specification.
 * Needs to be inline in order to fetch the name of the ADT and the constructor.
 *
 * @param builder the builder user for specifying the ADT
 */
    inline def unapply(builder: ADTBuilder): (ADT[0], constructors[0]) = unapply[0](() --> builder)

    /** Returns an ADT containing only one constructor out of a user specification.
 * Needs to be inline in order to fetch the name of the ADT and the constructor.
 *
 * @param builder the builder of the unique constructor of the ADT
 */
    private inline def unapply(builder: ConstructorBuilder): (ADT[0], constructors[0]) = unapply(builder.toADTBuilder)

    /** Returns an ADT isomorphic to a given type. It has only one constructor taking as only argument an element of
 * the provided type.
 * Needs to be inline in order to fetch the name of the ADT and the constructor.
 *
 * @param t type given by the user
 */
    inline def unapply(t: Expr[Ind]): (ADT[0], constructors[0]) = unapply(term_to_const(t))

    /** Returns the unit type. This is an ADT containing only one value and hence having only one
 * constructor (non-inductive and taking no arguments).
 * Needs to be inline in order to fetch the name of the ADT and the constructor.
 *
 * @param u user specification indicating that they want to generate the unit type
 */
    inline def unapply(u: Unit): (ADT[0], constructors[0]) = unapply(unit_to_const(u))

    /** Returns a product type (also known as tuple). This is an ADT containing only one constructor.
 * Generally its arguments are non inductive as the opposite would lead to the empty type.
 * Needs to be inline in order to fetch the name of the ADT and the constructor.
 *
 * @param t user specification of the tuple
 */
    inline def unapply[N <: Arity, T <: Tuple](t: (ADT[N] | Expr[Ind]) *: T)(using ConstructorConverter[T]): (ADT[0], constructors[0]) =
      t.head match
        case a: ADT[N] => unapply(adt_tuple_to_const(a *: t.tail))
        case term: Expr[Ind] => unapply(any_to_const(term *: t.tail))
  }

  /** Converts an ADT with no type variables into a term.
 */
  given adt_to_term: Conversion[ADT[0], Expr[Ind]] = _.applyUnsafe(**())

  /** Converts a function over an ADT with no type variables into a term (i.e a set function).
 */
  given fun_to_term: Conversion[ADTFunction[0], Expr[Ind]] = _.applyUnsafe(**())

  /** Converts a constructor with no type variables into a term (i.e a set function).
 */
  given constructor_to_term: Conversion[Constructor[0], Expr[Ind]] = _.applyUnsafe(**())

  /** Mutable data structure that registers the patterns that have been filled inside a pattern matching syntax.
 *
 * @tparam N the type variables of the ADT
 * @param comp the complementary information stored in the builder
 */
  class CaseBuilder[N <: Arity, T, R](val comp: R) {

    /** The underlying mutable map between patterns and the body of the corresponding cases. For each
 * patterns stores the variables that have been used to represent its arguments.
 */
    private val underlying = scala.collection.mutable.Map[Constructor[N], (Seq[Variable[Ind]], T)]()

    /** Adds a case to the pattern matching
 *
 * @param cons the pattern / constructor
 * @param value the value next to the variables that are used for the pattern's arguments
 */
    def +=(cons: Constructor[N], value: (Seq[Variable[Ind]], T)) = underlying += (cons -> value)

    /** Checks if the cases of a pattern matching are valid. Specifically, it checks that:
 * - All constructors are covered
 * - There are no extra cases
 * - The number of variables provided by the user matches the arity of the constructor
 *
 * @param adt the ADT over which the pattern matching is performed
 * @return an error message if the pattern matching is invalid, None otherwise
 */
    def isValid(adt: ADT[N]): Option[String] =
      val constructors = adt.constructors.toSet
      val casesConstructors = underlying.keySet.toSet

      val constructorsMinusCases = constructors -- casesConstructors
      val casesMinusConstructors = casesConstructors -- constructors

      // STEP 1: Check that all constructors are covered
      if !constructorsMinusCases.isEmpty then Some(s"Case for ${constructorsMinusCases.head.name} is missing.")
      // STEP 2: Check that there are no extra cases
      else if !casesMinusConstructors.isEmpty then Some(s"${casesMinusConstructors.head.name} is not a constructor of ${adt.name}.")
      else
        underlying.keys.foldLeft[Option[String]](None)((acc, c) =>
          val vars = underlying(c)._1.toSet
          // STEP 3: Check that for each case the number of variables provided by the user matches the arity of the constructor
          acc.orElse(Some(s"Case ${c.name}: ${vars.size} variables were provided whereas the arity of ${c.name} is ${c.arity}.").filter(_ => vars.size != c.underlying.arity))
        )

    /** Outputs an immutable map out of the underlying mutable one
 */
    def build: Map[Constructor[N], (Seq[Variable[Ind]], T)] = underlying.toMap
  }

  /** Case of a a pattern matching syntax
 *
 * @param cons the pattern / constructor
 * @param vars variables that are used to represent the arguments of the constructor
 */
  case class Case[N <: Arity](cons: Constructor[N], vars: Variable[Ind]*) {

    /** Used in the context of an induction proof. Adds the subproof corresponding to this case into a builder.
 *
 * @see [[Induction]]
 *
 * @param proof the outer scope of the induction proof
 * @param line the line at which this case is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param file the file in which this case is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param builder the builder of the induction proof
 * @param subproof the proof of the case (possibly using the induction hypothesis)
 */
    def subproof(using proof: Proof, line: sourcecode.Line, file: sourcecode.File, builder: CaseBuilder[N, proof.ProofStep, (Sequent, Seq[Expr[Ind]], Variable[Ind])])(
        subproof: proof.InnerProof ?=> Unit
    ): Unit =
      val (bot, args, adtVar) = builder.comp
      val prop = bot.right.head
      val consTerm = appSeq(cons.underlying.term(args))(vars)
      val subst = adtVar -> consTerm

      val assumptions =
        (wellTypedSet(cons.underlying.semanticSignature(vars).map(p => (p._1, p._2.substitute(cons.underlying.typeVariablesSeq.zip(args).map(SubstPair(_, _))*))))
          ++
            cons.underlying.syntacticSignature(vars).filter(_._2 == Self).map((v, _) => prop.substitute(adtVar -> v)))

      // val botWithAssumptions = bot.substitute(subst) ++ ((assumptions ++ proof.getAssumptions) |- ())
      val botWithAssumptions = bot.substitute(subst) ++ (assumptions |- ())

      val iProof: proof.InnerProof = new proof.InnerProof(Some(botWithAssumptions))
      subproof(using iProof)
      val proofStep = (new SUBPROOF(using proof)(None)(iProof)).judgement.validate(line, file).asInstanceOf[proof.ProofStep]

      def subproofWithExtraStep: proof.ProofTacticJudgement = TacticSubproof { ip ?=>
        val fullSeq = Tautology(using lisa.SetTheoryLibrary, ip)(proofStep)(botWithAssumptions)
        if fullSeq.isValid then fullSeq.validate(line, file)
        else return proof.InvalidProofTactic(s"Proof of case ${cons.name} is invalid.\nExpected: ${botWithAssumptions}.")
      }

      builder += (cons, (vars, subproofWithExtraStep.validate(line, file)))

    /** Used in the context of a function definition. Adds the body of the case to a builder.
 *
 * @param body the body of this case
 * @param builder the builder for the function definition
 */
    def apply(body: Expr[Ind])(using builder: CaseBuilder[N, Expr[Ind], Unit]) = builder += (cons, (vars, body))
  }

  /** Defines a function over an ADT
 *
 * @param adt the domain of this function
 * @param returnType the return type of this function
 * @param name the name of this functions
 * @param cases the definition of the function for each constructor
 */
  def fun[N <: Arity](adt: ADT[N], returnType: Expr[Ind])(using name: sourcecode.Name)(cases: CaseBuilder[N, Expr[Ind], Unit] ?=> Unit): ADTFunction[N] = {
    val builder = CaseBuilder[N, Expr[Ind], Unit](())
    cases(using builder)
    builder.isValid(adt) match
      case None =>
        ADTFunction(SemanticFunction[N](name.value, adt.underlying, builder.build.map((k, v) => (k.underlying, v)), returnType), adt)
      case Some(msg) => throw IllegalArgumentException(msg)
  }

}

 */
