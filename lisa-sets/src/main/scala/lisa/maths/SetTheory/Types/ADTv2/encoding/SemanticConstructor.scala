package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Functions.Predef.*

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro

/**
 *  Semantic set theoretical interpretation of a constructor for an algebraic data type.
 *  That is a function from the arguments' domains to the set of instances of the
 *  algebraic data type.
 *
 *  `c : T1 -> ... -> Tn -> ADT`
 *
 *  Since polymorphism is supported, this function is parametrized by the type variables
 *  appearing inside the specification of the ADT. In this sense, a constructor is a class
 *  function whose parameters are type variables and whose body is the set theoretic
 *  function detailed above. With polymorphism, the signature thus becomes:
 *
 *  `c(X1, ..., Xn) : T1(X1, ..., Xn) -> ... -> Tn(X1, ..., Xn) -> ADT(X1, ..., Xn)`
 *
 *  Injectivity and introduction rule are proven within this class.
 *
 *  @constructor generates a class function for this constructor
 *  @param line the line at which this constructor is defined. Usually fetched
 *    automatically by the compiler. Used for error reporting
 *  @param file the file in which this constructor is defined. Usually fetched
 *    automatically by the compiler. Used for error reporting
 *  @param name the name of this constructor
 *  @param underlying the syntactic constructor
 *  @param adt the algebraic data type to which this constructor belongs
 */
class SemanticConstructor[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
    val name: String,
    val underlying: SyntacticConstructor,
    val adt: SyntacticADT[N]
) {

  /**
   *  Full name of this constructor, i.e. concatenation of the ADT name and this
   *  constructor name.
   */
  val fullName: String = s"${adt.name}/${name}"

  /** Type variables that may appear in the signature of this constructor. */
  val typeVariables: Variable[Ind] ** N = adt.typeVariables

  /** Sequence of type variables that may appear in the signature of this constructor. */
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq

  /** Number of type variables in the signature of this constructor. */
  val typeArity: N = adt.typeArity

  /** Variables used for constructor arguments. */
  val variables: Seq[Variable[Ind]] = underlying.variables

  /** Variables used for constructor arguments. */
  val variables1: Seq[Variable[Ind]] = underlying.variables1

  /** Alternative set of variables used for constructor arguments. */
  val variables2: Seq[Variable[Ind]] = underlying.variables2

  /**
   *  Set of variables for this constructor with their respective domain or a special
   *  symbol in case the domain is the ADT.
   *
   *  @param vars variables
   */
  def syntacticSignature(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], ConstructorArg)] =
    vars.zip(underlying.specification)

  /**
   *  Variables of this constructor with their respective domain or a special symbol in
   *  case the domain is the ADT.
   */
  val syntacticSignature: Seq[(Variable[Ind], ConstructorArg)] = underlying.signature

  /**
   *  Constructor arguments with their respective domains.
   *
   *  @param vars this constructor arguments
   */
  def semanticSignature(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] = vars
    .zip(underlying.specification.map(_.getOrElse(adt.term)))

  /** Variables of this constructor with their respective domains. */
  val semanticSignature: Seq[(Variable[Ind], Expr[Ind])] = semanticSignature(variables)

  /** Variables of this constructor with their respective domains. */
  val semanticSignature1: Seq[(Variable[Ind], Expr[Ind])] = semanticSignature

  /** Alternative set of variables of this constructor with their respective domain. */
  val semanticSignature2: Seq[(Variable[Ind], Expr[Ind])] = semanticSignature(variables2)

  /** Type of this constructor. */
  val typ: Expr[Ind] =
    // semanticSignature.unzip._2.foldRight[Expr[Ind]](adt.term)((a, b) => a |=> b)
    semanticSignature.unzip._2.foldRight[Expr[Ind]](adt.term)((a, b) => functionSet(a, b))

  /** Arity of this constructor. */
  val arity: Int = variables.size

  /** Internal representation of this constructor (i.e. as a tuple). */
  val structuralTerm: Expr[Ind] = underlying.term

  /** Internal representation of this constructor (i.e. as a tuple). */
  val structuralTerm1: Expr[Ind] = underlying.term1

  /**
   *  Internal representation of this constructor (i.e. as a tuple) with an alternative
   *  set of variables.
   */
  val structuralTerm2: Expr[Ind] = underlying.term2

  /**
   *  Definition of this constructor.
   *
   *  Formally it is the only function whose codomain is the ADT such that for all
   *  variables x1 :: S1, ...,xn :: Sn c * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...))
   */
  private val untypedDefinition = (c :: typ) /\ forallSeq(
    variables,
    wellTypedFormula(semanticSignature) ==> (appSeq(c)(variables) === structuralTerm)
  )

  /**
   *  Lemma --- Uniqueness of this constructor.
   *
   *  ` ∃!c. c ∈ T1 -> ... -> Tn -> ADT /\ ∀x1, ..., xn. c * x1 * ...* xn = (tagc, (x1, (..., (xn, ∅)...))`
   */
  private val uniqueness = Axiom(existsOne(c, untypedDefinition))

  /**
   *  Temporary placeholder while ADTv2 function-definition integration is finalized.
   *  classFunction represents the constructor as a set-theoretic function: classFunction
   *  * X1 * ... * Xm * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...)) where Xi are type
   *  variables and xi are constructor arguments. Formerly defined via:
   *  FunctionDefinition[N](fullName, ...)(typeVariablesSeq, c, untypedDefinition,
   *  uniqueness).label
   */
  private val classFunctionConst: Constant[Ind] = Constant[Ind](fullName)
  registerConstant(classFunctionConst)
  private val classFunction: Expr[Ind] = classFunctionConst

  /** Identifier of this constructor. */
  // val id: Identifier = classFunction.id

  /**
   *  This constructor in which type variables are instantiated.
   *
   *  @param args the instances of this constructor's type variables
   */
  def term(args: Seq[Expr[Ind]]): Expr[Ind] = appSeq(classFunction)(args)

  /** Constructor where type variables are instantiated with schematic variables. */
  private val term: Expr[Ind] = term(typeVariablesSeq)

  /**
   *  Lemma --- Characterization of this constructor.
   *
   *  `∀c. term = c <=> c ∈ typ /\ ∀x1,...,xn. c * x1 * ... * xn = (tagc, ...)`
   */
  private val classFunctionCharacterization =
    Axiom(forall(c, (term === c) <=> untypedDefinition)
  )

  /**
   *  Constructor where type variables are instantiated with schematic variables and
   *  arguments instantiated.
   *
   *  @param args the instances of this constructor arguments
   */
  def appliedTerm(args: Seq[Expr[Ind]]): Expr[Ind] = appSeq(term)(args)

  /**
   *  Constructor where type variables and arguments are instantiated with schematic
   *  variables.
   */
  val appliedTerm: Expr[Ind] = appliedTerm(variables)

  /**
   *  Constructor where type variables and arguments are instantiated with schematic
   *  variables.
   */
  val appliedTerm1: Expr[Ind] = appliedTerm

  /**
   *  Constructor where type variables and arguments are instantiated with schematic
   *  variables. Arguments variables are however drawn from an alternative set of
   *  variables.
   */
  val appliedTerm2: Expr[Ind] = appliedTerm(variables2)

  /**
   *  Lemma --- This constructor is equal to its internal representation.
   *
   *  `∀x1, ..., xn. c * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...))`
   */
  val shortDefinition = Lemma(using
    name = sourcecode.FullName(s"${fullName}/shortDefinition")
  )(forallSeq(
    variables,
    wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)
  )) {
    have(forall(c, (term === c) <=> untypedDefinition)) by
      Restate.from(classFunctionCharacterization)
    thenHave(
      (term === term) <=>
        ((term :: typ) /\ forallSeq(
          variables,
          wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)
        ))
    ) by InstantiateForall(term)
    thenHave(thesis) by Weakening
  }

  /**
   *  Lemma --- Introduction rule for this constructor.
   *
   *  `∀A1, ..., Am. c(X1, ..., Xm) ∈ T1(X1, ..., Xm) -> ... -> Tn(X1, ..., Xm) -> ADT(X1, ..., Xm)`
   *
   *  where Ai are the type variables of the ADT and Ti are domains of this constructor
   *  arguments.
   *
   *  e.g. `∀T. nil(T) ∈ list(T)` and `∀T. cons(T) ∈ T -> list(T) -> list(T)`
   */
  val intro = Lemma(using name = sourcecode.FullName(s"${fullName}/intro"))(forallSeq(
    typeVariablesSeq,
    term :: typ
  )) {
    // have(forall(c, (term === c) <=> untypedDefinition)) by Exact(classFunction.definition)
    have(forall(c, (term === c) <=> untypedDefinition)) by
      Restate.from(classFunctionCharacterization)
    thenHave(
      (term === term) <=>
        ((term :: typ) /\ forallSeq(
          variables,
          wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)
        ))
    ) by InstantiateForall(term)
    thenHave(term :: typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
  }

  /**
   *  Theorem --- Injectivity of constructors.
   *
   *  Two instances of this constructor are equal if and only if all of their arguments
   *  are pairwise equal
   *
   *  e.g. Cons(head1, tail1) === Cons(head2, tail2) <=> head1 === head2 /\ tail1 ===
   *  tail2
   */
  lazy val injectivity = {
    val vars1WellTyped: Set[Expr[Prop]] = wellTypedSet(semanticSignature1)
    val vars2WellTyped: Set[Expr[Prop]] = wellTypedSet(semanticSignature2)

    val lemmaName = sourcecode.FullName(s"${fullName}/injectivity")
    if arity == 0 then {
      Lemma(using name = lemmaName)(appliedTerm1 === appliedTerm2) {
        have(thesis) by RightRefl
      }
    } else
      Lemma(using name = lemmaName)(
        vars1WellTyped ++ vars2WellTyped |-
          simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))
      ) {

        have(forallSeq(
          variables1,
          wellTypedFormula(semanticSignature1) ==> (appliedTerm1 === structuralTerm1)
        )) by Restate.from(shortDefinition)

        variables1.foldLeft(lastStep)((fact, v) =>
          fact.statement.right.head match
            case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        val tappTerm1Def = thenHave(vars1WellTyped |- appliedTerm1 === structuralTerm1) by
          Restate

        // println(forallSeq(variables1, wellTypedFormula(semanticSignature1) ==> (appliedTerm1 === structuralTerm1)))
        // println(forallSeq(variables2, wellTypedFormula(semanticSignature2) ==> (appliedTerm2 === structuralTerm)))
        have(forallSeq(
          variables2,
          wellTypedFormula(semanticSignature2) ==> (appliedTerm2 === structuralTerm2)
        )) by Restate.from(shortDefinition)

        variables2.foldLeft(lastStep)((fact, v) =>
          fact.statement.right.head match
            case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        val tappTerm2Def = thenHave(vars2WellTyped |- appliedTerm2 === structuralTerm2) by
          Restate

        val s0 = have(
          vars2WellTyped + (appliedTerm1 === appliedTerm2) |-
            appliedTerm1 === structuralTerm2
        ) by Cut(
          tappTerm2Def,
          altEqualityTransitivity of
            (x := appliedTerm1, y := appliedTerm2, z := structuralTerm2)
        )
        have(
          vars1WellTyped + (appliedTerm1 === structuralTerm2) |-
            structuralTerm1 === structuralTerm2
        ) by Cut(
          tappTerm1Def,
          altEqualityTransitivity of
            (x := structuralTerm1, y := appliedTerm1, z := structuralTerm2)
        )
        have(
          (vars1WellTyped ++ vars2WellTyped) + (appliedTerm1 === appliedTerm2) |-
            structuralTerm1 === structuralTerm2
        ) by Cut(s0, lastStep)
        val forward = thenHave(
          vars1WellTyped ++ vars2WellTyped |- (appliedTerm1 === appliedTerm2) ==>
            (structuralTerm1 === structuralTerm2)
        ) by RightImplies

        val s1 = have(
          vars1WellTyped + (structuralTerm1 === structuralTerm2) |-
            appliedTerm1 === structuralTerm2
        ) by Cut(
          tappTerm1Def,
          altEqualityTransitivity of
            (x := appliedTerm1, y := structuralTerm1, z := structuralTerm2)
        )
        have(
          vars2WellTyped + (appliedTerm1 === structuralTerm2) |-
            appliedTerm1 === appliedTerm2
        ) by Cut(
          tappTerm2Def,
          altEqualityTransitivity of
            (x := appliedTerm1, y := structuralTerm2, z := appliedTerm2)
        )
        have(
          (vars1WellTyped ++ vars2WellTyped) + (structuralTerm1 === structuralTerm2) |-
            appliedTerm1 === appliedTerm2
        ) by Cut(s1, lastStep)
        val backward = thenHave(
          vars1WellTyped ++ vars2WellTyped |- (structuralTerm1 === structuralTerm2) ==>
            (appliedTerm1 === appliedTerm2)
        ) by RightImplies

        val definitionUnfolding = have(
          vars1WellTyped ++ vars2WellTyped |- (appliedTerm1 === appliedTerm2) <=>
            (structuralTerm1 === structuralTerm2)
        ) by RightIff(forward, backward)

        have(
          (appliedTerm1 === appliedTerm2) <=> (structuralTerm1 === structuralTerm2) |-
            (appliedTerm1 === appliedTerm2) <=> seqEq(variables1, variables2)
        ) by Cut(
          underlying.injectivity,
          equivalenceRewriting of
            (
              p1 := (appliedTerm1 === appliedTerm2),
              p2 := (structuralTerm1 === structuralTerm2),
              p3 := seqEq(variables1, variables2)
            )
        )
        have(thesis) by Cut(definitionUnfolding, lastStep)
      }
  }

  /** Case generated by this constructor when performing a proof by induction */
  lazy val inductiveCase: Expr[Prop] = syntacticSignature
    .foldRight[Expr[Prop]](P(appliedTerm1)) { (el, fc) =>
      val (v, typ) = el
      typ match
        case SelfRef => forall(v, (v :: adt.term) ==> (P(v) ==> fc))
        case RegularArg(t) => forall(v, (v :: typeExprToTerm(t)) ==> fc)
    }
}
