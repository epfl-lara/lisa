package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{TypeSubstitution, instantiatedTheorem, normalizeTypeSubstitutions, resolvedTypeArguments, theoremAt}
import lisa.maths.SetTheory.Types.ADTv2.support.UniqueCharacterizedSymbol
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.`**`

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

  private def normalizedTypeArguments(
      substitutions: Seq[TypeSubstitution]
  ): Seq[Expr[Ind]] =
    resolvedTypeArguments(
      typeVariablesSeq,
      normalizeTypeSubstitutions("constructor", fullName, typeVariablesSeq, substitutions)
    )

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

  def heightTypingFormula(heightSet: Expr[Ind]): Expr[Prop] =
    wellTypedFormula(underlying.signature2)(heightSet)

  def branchPremiseAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
    heightTypingFormula(heightSet) /\ (term === structuralTerm2)

  def branchAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
    existsSeq(variables2, branchPremiseAtHeight(heightSet, term))

  def selfRefVariables2: Seq[Variable[Ind]] =
    syntacticSignature(variables2).collect {
      case (v, lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef) => v
    }

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

  private val internals = new ConstructorInternals[N](
    adt = adt,
    underlying = underlying,
    semanticSignature = semanticSignature,
    variables = variables,
    structuralTerm = structuralTerm,
    typ = typ
  )

  /**
   *  Definition of this constructor.
   *
   *  Formally it is the only function whose codomain is the ADT such that for all
   *  variables x1 :: S1, ...,xn :: Sn c * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...))
   */
  private val untypedDefinition = internals.untypedDefinition

  private val definedClassFunction = UniqueCharacterizedSymbol(
    name = fullName,
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = c,
    definitionAt = c0 => internals.untypedDefinition.substitute(c := c0)
  )(internals.uniqueness)

  val id = definedClassFunction.id

  /**
   *  This constructor in which type variables are instantiated.
   *
   *  @param args the instances of this constructor's type variables
   */
  def term(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)

  /** Constructor where type variables are instantiated with schematic variables. */
  private val term: Expr[Ind] = definedClassFunction.term

  /**
   *  Lemma --- Characterization of this constructor.
   *
   *  `∀c. term = c <=> c ∈ typ /\ ∀x1,...,xn. c * x1 * ... * xn = (tagc, ...)`
   */
  private val classFunctionCharacterization: THM = definedClassFunction.characterization

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

  def semanticTypingFromHeight(heightFun: Expr[Ind], n: Expr[Ind]): THM = Lemma(
    (adt.isHeight(heightFun), n ∈ N, heightTypingFormula(app(heightFun)(n))) |-
      wellTypedFormula(semanticSignature2)
  ) {
    val hValid = assume(adt.isHeight(heightFun))
    val nInN = assume(n ∈ N)
    val argsTypedAtHeight = assume(heightTypingFormula(app(heightFun)(n)))

    val exTypedAtHeight = have(
      ∃(k, (k ∈ N) /\ heightTypingFormula(app(heightFun)(k)))
    ) subproof {
      have((n ∈ N) /\ heightTypingFormula(app(heightFun)(n))) by
        Tautology.from(nInN, argsTypedAtHeight)
      thenHave(thesis) by RightExists
    }

    val termsHaveHeightAtH = have(
      heightTypingFormula(adt.term) <=>
        ∃(k, (k ∈ N) /\ heightTypingFormula(app(heightFun)(k)))
    ) by Tautology.from(
      hValid,
      adt.termsHaveHeight(underlying)
        .of(h := heightFun)
        .of(underlying.variables.zip(underlying.variables2).map((from, to) => from := to)*)
    )

    val argsTypedAtTerm = have(heightTypingFormula(adt.term)) by
      Tautology.from(termsHaveHeightAtH, exTypedAtHeight)
    have(wellTypedFormula(semanticSignature2)) by Restate.from(argsTypedAtTerm)
  }

  def appliedEqualityFromStructural(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind]): THM =
    Lemma(
      (adt.isHeight(heightFun), n ∈ N, branchPremiseAtHeight(app(heightFun)(n), term0)) |-
        (term0 === appliedTerm2)
    ) {
      assume(adt.isHeight(heightFun))
      assume(n ∈ N)
      assume(branchPremiseAtHeight(app(heightFun)(n), term0))
      val argsTypedAtHeight = have(heightTypingFormula(app(heightFun)(n))) by Tautology
      val termEqStructural = have(term0 === structuralTerm2) by Tautology

      val argsTypedSemantic = have(wellTypedFormula(semanticSignature2)) by
        Cut(argsTypedAtHeight, semanticTypingFromHeight(heightFun, n))

      val shortBase = have(shortDefinition.statement.right.head) by Tautology.from(shortDefinition)
      val shortAtVars2 = variables2.foldLeft(shortBase)((_, v2) =>
        lastStep.statement.right.head match
          case forall(v, phi) =>
            thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by
              InstantiateForall(v2)
          case _ => throw UnreachableException
      )
      val appliedEqStructural = shortAtVars2.statement.right.head match
        case _ ==> consequent =>
          have(consequent) by Tautology.from(shortAtVars2, argsTypedSemantic)
        case _ => throw UnreachableException
      have(term0 === appliedTerm2) by Tautology.from(
        altEqualityTransitivity of (x := term0, y := structuralTerm2, z := appliedTerm2),
        termEqStructural,
        appliedEqStructural
      )
    }

  def recursiveArgInHeight(heightFun: Expr[Ind], heightIndex: Expr[Ind]): THM =
    Lemma(
      (adt.isHeight(heightFun), heightIndex ∈ N, wellTypedFormula(semanticSignature1), appliedTerm1 ∈ app(heightFun)(successor(heightIndex))) |-
        wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))
    ) {
      val hValid = assume(adt.isHeight(heightFun))
      val nInN = assume(heightIndex ∈ N)
      val argsTypedSemantic = assume(wellTypedFormula(semanticSignature1))
      val appliedInSucc = assume(appliedTerm1 ∈ app(heightFun)(successor(heightIndex)))

      val shortBase = have(shortDefinition.statement.right.head) by Tautology.from(shortDefinition)
      val shortAtVars1 = variables1.foldLeft(shortBase)((_, v1) =>
        lastStep.statement.right.head match
          case forall(v, phi) =>
            thenHave(phi.substituteUnsafe(Map(v -> v1)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v1)
          case _ => throw UnreachableException
      )
      val appliedEqStructural = shortAtVars1.statement.right.head match
        case _ ==> consequent =>
          have(consequent) by Tautology.from(shortAtVars1, argsTypedSemantic)
        case _ => throw UnreachableException

      val structuralInSucc = have(structuralTerm1 ∈ app(heightFun)(successor(heightIndex))) by Congruence.from(
        appliedEqStructural,
        appliedInSucc
      )

      val isConstructorAtHeight = have(adt.isConstructor(structuralTerm1, app(heightFun)(heightIndex))) by Tautology.from(
        hValid,
        nInN,
        structuralInSucc,
        adt.heightSuccessorStrong of (h := heightFun, x := structuralTerm1, n := heightIndex),
        equivalenceApply of (
          p1 := structuralTerm1 ∈ app(heightFun)(successor(heightIndex)),
          p2 := adt.isConstructor(structuralTerm1, app(heightFun)(heightIndex))
        )
      )

      val constructorBranches = adt.constructors.map { other =>
        val branchVars = other.variables2.map(_ => variable[Ind])
        val branchSubsts = other.variables2.zip(branchVars).map { case (v, fresh) => v := fresh }
        val branchSignature = branchVars.zip(other.signature2.map(_._2))
        val branchTerm = other.term2.substitute(branchSubsts*).asInstanceOf[Expr[Ind]]
        val branch = existsSeq(
          branchVars,
          wellTypedFormula(branchSignature)(app(heightFun)(heightIndex)) /\
            (structuralTerm1 === branchTerm)
        )
        val branchBody =
          wellTypedFormula(branchSignature)(app(heightFun)(heightIndex)) /\
            (structuralTerm1 === branchTerm)

        if other == underlying then
          val directBranch = have(branchBody |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) subproof {
            assume(branchBody)
            val argsTypedAtHeight = have(wellTypedFormula(branchSignature)(app(heightFun)(heightIndex))) by Tautology
            val structuralEquality = have(structuralTerm1 === branchTerm) by Tautology
            val varsEqual = have(variables1 === branchVars) by Tautology.from(
              structuralEquality,
              underlying.injectivity.of(branchSubsts*),
              equivalenceApply of (
                p1 := structuralTerm1 === branchTerm,
                p2 := seqEq(variables1, branchVars)
              )
            )
            val transportedTyping = syntacticSignature.zipWithIndex.map { case ((v1, arg), idx) =>
              val v2 = branchVars(idx)
              val vEq = have(v1 === v2) by Tautology.from(varsEqual)
              arg match
                case lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef =>
                  have(v1 ∈ app(heightFun)(heightIndex)) by Congruence.from(argsTypedAtHeight, vEq)
                case lisa.maths.SetTheory.Types.ADTv2.syntax.AST.TypeArg(name) =>
                  have(v1 ∈ typeExprToTerm(name)) by Congruence.from(argsTypedAtHeight, vEq)
            }
            have(wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by Tautology.from(
              transportedTyping*
            )
          }
          val rawBranch = branchVars.reverse.foldLeft(directBranch -> branchBody) { case ((fact, premise), v) =>
            val wrappedPremise = ∃(v, premise)
            val lifted = have(fact.statement -<? premise +<? wrappedPremise) by
              LeftExists.withParameters(premise, v)(fact)
            (lifted, wrappedPremise)
          }
          have(branch |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by Tautology.from(rawBranch._1)
        else
          val directBranch = have(branchBody |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) subproof {
            assume(branchBody)
            val structuralEquality = have(structuralTerm1 === branchTerm) by Tautology
            val impossible = have(!(structuralTerm1 === branchTerm)) by
              Tautology.from(adt.injectivity(underlying, other).of(branchSubsts*))
            have(wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by Tautology.from(
              structuralEquality,
              impossible
            )
          }
          val rawBranch = branchVars.reverse.foldLeft(directBranch -> branchBody) { case ((fact, premise), v) =>
            val wrappedPremise = ∃(v, premise)
            val lifted = have(fact.statement -<? premise +<? wrappedPremise) by
              LeftExists.withParameters(premise, v)(fact)
            (lifted, wrappedPremise)
          }
          have(branch |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by Tautology.from(rawBranch._1)
      }

      have(adt.isConstructor(structuralTerm1, app(heightFun)(heightIndex)) |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by LeftOr(
        constructorBranches*
      )
      have(wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by Tautology.from(
        isConstructorAtHeight,
        lastStep
      )
      thenHave(thesis) by Restate
    }

  def semanticTypingFromHeightAt(
      substitutions: Seq[TypeSubstitution]
  )(heightFun: Expr[Ind], n: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM = {
    val normalized = normalizeTypeSubstitutions("constructor", fullName, typeVariablesSeq, substitutions)
    instantiatedTheorem(
      theoremOwner = renderAppliedSymbol(fullName, typeVariablesSeq.size, normalizedTypeArguments(normalized)),
      suffix = "semanticTypingFromHeight",
      substitutions = normalized,
      baseTheorem = semanticTypingFromHeight(heightFun, n)
    )
  }

  def recursiveArgInHeightAt(
      substitutions: Seq[TypeSubstitution]
  )(heightFun: Expr[Ind], heightIndex: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM = {
    val normalized = normalizeTypeSubstitutions("constructor", fullName, typeVariablesSeq, substitutions)
    val typeInstantiated = instantiatedTheorem(
      theoremOwner = renderAppliedSymbol(fullName, typeVariablesSeq.size, normalizedTypeArguments(normalized)),
      suffix = "recursiveArgInHeight",
      substitutions = normalized,
      baseTheorem = recursiveArgInHeight(heightFun, heightIndex)
    )
    val valueSubstitutions = variables1.zip(variables2).map((from, to) => from := to)
    Lemma(typeInstantiated.statement.substitute(valueSubstitutions*)) {
      have(thesis) by Restate.from(typeInstantiated.of(valueSubstitutions*))
    }
  }

  def appliedEqualityFromStructuralAt(
      substitutions: Seq[TypeSubstitution]
  )(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM = {
    val normalized = normalizeTypeSubstitutions("constructor", fullName, typeVariablesSeq, substitutions)
    instantiatedTheorem(
      theoremOwner = renderAppliedSymbol(fullName, typeVariablesSeq.size, normalizedTypeArguments(normalized)),
      suffix = "appliedEqualityFromStructural",
      substitutions = normalized,
      baseTheorem = appliedEqualityFromStructural(heightFun, n, term0)
    )
  }

  def structuralPairDecomposition(other: SemanticConstructor[?]): THM =
    Lemma(
      (structuralTerm1 === other.structuralTerm2) <=>
        ((underlying.tagTerm === other.underlying.tagTerm) /\
          (underlying.subterm1 === other.underlying.subterm2))
    ) {
      have(thesis) by Restate.from(
        Pair.extensionality of (
          a := underlying.tagTerm,
          b := underlying.subterm1,
          c := other.underlying.tagTerm,
          d := other.underlying.subterm2
        )
      )
    }

  def structuralDisjointness(other: SemanticConstructor[?]): THM = {
    require(this != other, "structuralDisjointness requires two distinct constructors.")

    val minTag = Math.min(underlying.tag, other.underlying.tag)
    val maxTag = Math.max(underlying.tag, other.underlying.tag)

    Lemma(!(structuralTerm1 === other.structuralTerm2)) {
      val tagsFromStructuralEq = have(
        structuralTerm1 === other.structuralTerm2 |-
          (underlying.tagTerm === other.underlying.tagTerm) /\
          (underlying.subterm1 === other.underlying.subterm2)
      ) by Tautology.from(structuralPairDecomposition(other))

      val tagsEqual = have(
        structuralTerm1 === other.structuralTerm2 |- underlying.tagTerm === other.underlying.tagTerm
      ) by Tautology.from(tagsFromStructuralEq)

      val tagsDifferent = have(!(underlying.tagTerm === other.underlying.tagTerm)) by Tautology.from(
        constructorTagDisequality(
          underlying.tagTerm,
          other.underlying.tagTerm,
          minTag,
          maxTag
        )
      )

      have(thesis) by Tautology.from(tagsEqual, tagsDifferent)
    }
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

  def shortDefinitionAt(
      substitutions: Seq[TypeSubstitution]
  )(using sourcecode.Line, sourcecode.File): THM =
    theoremAt(
      displayName = fullName,
      typeVariables = typeVariablesSeq,
      typeArgs = normalizedTypeArguments(substitutions),
      suffix = "shortDefinition",
      baseTheorem = shortDefinition
    )

  def introAt(
      substitutions: Seq[TypeSubstitution]
  )(using sourcecode.Line, sourcecode.File): THM =
    theoremAt(
      displayName = fullName,
      typeVariables = typeVariablesSeq,
      typeArgs = normalizedTypeArguments(substitutions),
      suffix = "intro",
      baseTheorem = intro
    )

  def injectivityAt(
      substitutions: Seq[TypeSubstitution]
  )(using sourcecode.Line, sourcecode.File): THM =
    theoremAt(
      displayName = fullName,
      typeVariables = typeVariablesSeq,
      typeArgs = normalizedTypeArguments(substitutions),
      suffix = "injectivity",
      baseTheorem = injectivity
    )
}
