package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.Quantifiers.existsOneEpsilonUniqueness

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
 *  Injectivity, constructor equations, and typing are proven within this class.
 *
 *  Exported semantic lemmas are kept in formula form. Type variables remain schematic,
 *  while constructor arguments are explicitly quantified.
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

  override def toString: String = fullName

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
    semanticSignature.unzip._2.foldRight[Expr[Ind]](adt.term)((a, b) => (a ->: b))

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
  private val classFunction: Constant[?] = {
    val classFunctionExpr: Expr[?] = lisa.utils.fol.FOL.Abs.apply(
      xs = typeVariablesSeq, 
      t = ε(c, untypedDefinition)
    )
    type S
    given lisa.utils.fol.FOL.IsSort[S] =
      lisa.utils.fol.FOL.unsafeSortEvidence(classFunctionExpr.sort)
    DEF(using name = fullName)(classFunctionExpr.asInstanceOf[Expr[S]])
  }
  classFunction.printAs(args => renderAppliedSymbol(fullName, typeVariablesSeq.size, args))

  val id = classFunction.id

  /**
   *  This constructor in which type variables are instantiated.
   *
   *  @param args the instances of this constructor's type variables
   */
  def term(args: Seq[Expr[Ind]]): Expr[Ind] = (classFunction #@@ args).asInstanceOf[Expr[Ind]]

  /** Constructor where type variables are instantiated with schematic variables. */
  private val term: Expr[Ind] = term(typeVariablesSeq)

  /**
   *  Lemma --- Characterization of this constructor.
   *
   *  `∀c. term = c <=> c ∈ typ /\ ∀x1,...,xn. c * x1 * ... * xn = (tagc, ...)`
   */
  private val classFunctionCharacterization =
    Lemma(forall(c, (term === c) <=> untypedDefinition)
  ) {
      val epsilonWitness = ε(c, untypedDefinition)
      
      val epsilonCharacterization = have(
        untypedDefinition <=> (c === epsilonWitness)
      ) by Tautology.from(
        uniqueness,
        existsOneEpsilonUniqueness of (
          x := c,
          y := c,
          P := λ(c, untypedDefinition)
        )
      )

      val classTermIsEpsilon =
        have(term === epsilonWitness) by Congruence.from(classFunction.definition)

      val toRight = have((term === c) ==> (c === epsilonWitness)) subproof {
        assume(term === c)
        val termEqC = have(term === c) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEpsilon)
        have(c === epsilonWitness) by Congruence.from(termEqC, termEqEpsilon)
        thenHave(thesis) by Restate
      }

      val toLeft = have((c === epsilonWitness) ==> (term === c)) subproof {
        assume(c === epsilonWitness)
        val cEqEpsilon = have(c === epsilonWitness) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEpsilon)
        have(term === c) by Congruence.from(termEqEpsilon, cEqEpsilon)
        thenHave(thesis) by Restate
      }

      val equalityRewriting = have((term === c) <=> (c === epsilonWitness)) by
        Tautology.from(toRight, toLeft)

      have((term === c) <=> untypedDefinition) by
        Tautology.from(equalityRewriting, epsilonCharacterization)

      thenHave(thesis) by RightForall
    }

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
   *  `c(X1, ..., Xm) ∈ T1(X1, ..., Xm) -> ... -> Tn(X1, ..., Xm) -> ADT(X1, ..., Xm)`
   *
   *  Type variables remain schematic at the semantic layer.
   */
  val intro = Lemma(using name = sourcecode.FullName(s"${fullName}/intro"))(term :: typ) {
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
    thenHave(thesis) by Restate
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
      val typedAssumption =
        simplify(wellTypedFormula(semanticSignature1 ++ semanticSignature2))
      Lemma(using name = lemmaName)(forallSeq(
        variables1 ++ variables2,
        typedAssumption ==> simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))
      )) {

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
        val equalityCharacterization = have(
          vars1WellTyped ++ vars2WellTyped |-
            simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))
        ) by Cut(definitionUnfolding, lastStep)

        have(typedAssumption ==> simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))) subproof {
          assume(typedAssumption)
          val typed = have(typedAssumption) by Hypothesis
          have(simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))) by
            Tautology.from(equalityCharacterization, typed)
        }
        thenHave(thesis) by QuantifiersIntro(variables1 ++ variables2)
      }
  }

  /** Case generated by this constructor when performing a proof by induction */
  lazy val inductiveCase: Expr[Prop] = syntacticSignature
    .foldRight[Expr[Prop]](P(appliedTerm1)) { (el, fc) =>
      val (v, typ) = el
      typ match
        case SelfRef => forall(v, (v :: adt.term) ==> (P(v) ==> fc))
        // case RegularArg(t) => forall(v, (v :: typeExprToTerm(t)) ==> fc)
        case TypeArg(name) => forall(v, (v :: typeExprToTerm(name)) ==> fc)
    }
}
