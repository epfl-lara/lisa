package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedTheorem
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.normalizeTypeSubstitutions
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.resolvedTypeArguments
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.theoremAt
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.prooflib.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.**
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.constructorTagDisequality
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.UniqueCharacterizedSymbol
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

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

  /**
   * Type variables that may appear in the signature of this constructor.
   */
  val typeVariables: Variable[Ind] ** N = adt.typeVariables

  /**
   * Sequence of type variables that may appear in the signature of this constructor.
   */
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq

  /**
   * Number of type variables in the signature of this constructor.
   */
  val typeArity: N = adt.typeArity

  /**
   * Variables used for constructor arguments.
   */
  val variables: Seq[Variable[Ind]] = underlying.variables

  /**
   * Variables used for constructor arguments.
   */
  val variables1: Seq[Variable[Ind]] = underlying.variables1

  /**
   * Alternative set of variables used for constructor arguments.
   */
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

  /**
   * Variables of this constructor with their respective domains.
   */
  val semanticSignature: Seq[(Variable[Ind], Expr[Ind])] = semanticSignature(variables)

  /**
   * Variables of this constructor with their respective domains.
   */
  val semanticSignature1: Seq[(Variable[Ind], Expr[Ind])] = semanticSignature

  /**
   * Alternative set of variables of this constructor with their respective domain.
   */
  val semanticSignature2: Seq[(Variable[Ind], Expr[Ind])] = semanticSignature(variables2)

  def heightTypingFormula(heightSet: Expr[Ind]): Expr[Prop] =
    wellTypedFormula(underlying.signature2)(heightSet)

  def branchPremiseAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
    heightTypingFormula(heightSet) /\ (term === structuralTerm2)

  def branchAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
    existsSeq(variables2, branchPremiseAtHeight(heightSet, term))

  def selfRefVariables2: Seq[Variable[Ind]] =
    syntacticSignature(variables2).collect { case (v, lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef) =>
      v
    }

  /**
   * Type of this constructor.
   */
  val typ: Expr[Ind] =
    // semanticSignature.unzip._2.foldRight[Expr[Ind]](adt.term)((a, b) => a |=> b)
    semanticSignature.unzip._2.foldRight[Expr[Ind]](adt.term)((a, b) => (a ->: b))

  /**
   * Arity of this constructor.
   */
  val arity: Int = variables.size

  /**
   * Internal representation of this constructor (i.e. as a tuple).
   */
  val structuralTerm: Expr[Ind] = underlying.term

  /**
   * Internal representation of this constructor (i.e. as a tuple).
   */
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

  /**
   * Constructor where type variables are instantiated with schematic variables.
   */
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
  )(
    forallSeq(
      variables,
      wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)
    )
  ) {
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
    thenHave(thesis) by Weakening
  }

  private def semanticTypingFromHeight(heightFun: Expr[Ind], n: Expr[Ind]): THM = Lemma(
    (adt.isHeight(heightFun), n ∈ N, heightTypingFormula(app(heightFun)(n))) |-
      wellTypedFormula(semanticSignature2)
  ) {
    assume(adt.isHeight(heightFun))
    assume(n ∈ N)
    assume(heightTypingFormula(app(heightFun)(n)))

    have((n ∈ N) /\ heightTypingFormula(app(heightFun)(n))) by Restate
    val exTypedAtHeight = thenHave(
      ∃(k, (k ∈ N) /\ heightTypingFormula(app(heightFun)(k)))
    ) by RightExists

    have(thesis) by Tautology.from(
      adt
        .termsHaveHeight(underlying)
        .of(h := heightFun)
        .of(underlying.variables.zip(underlying.variables2).map((from, to) => from := to)*), 
      exTypedAtHeight
    )
  }

  private def appliedEqualityFromStructural(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind]): THM =
    Lemma(
      (adt.isHeight(heightFun), n ∈ N, branchPremiseAtHeight(app(heightFun)(n), term0)) |-
        (term0 === appliedTerm2)
    ) {
      assume(adt.isHeight(heightFun))
      assume(n ∈ N)
      assume(branchPremiseAtHeight(app(heightFun)(n), term0))
      
      val shortBase = have(shortDefinition.statement.right.head) by Tautology.from(shortDefinition)
      val shortAtVars2 = have(wellTypedFormula(semanticSignature2) ==> (appliedTerm2 === structuralTerm2)) by
        InstantiateForallSeq(variables2)(shortBase)
      have(term0 === appliedTerm2) by Tautology.from(
        altEqualityTransitivity of (x := term0, y := structuralTerm2, z := appliedTerm2),
        shortAtVars2,
        semanticTypingFromHeight(heightFun, n)
      )
    }

  private def recursiveArgInHeight(heightFun: Expr[Ind], heightIndex: Expr[Ind]): THM =
    Lemma(
      (adt.isHeight(heightFun), heightIndex ∈ N, wellTypedFormula(semanticSignature1), appliedTerm1 ∈ app(heightFun)(S(heightIndex))) |-
        wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))
    ) {
      val hValid = assume(adt.isHeight(heightFun))
      val nInN = assume(heightIndex ∈ N)
      assume(wellTypedFormula(semanticSignature1))
      val appliedInSucc = assume(appliedTerm1 ∈ app(heightFun)(S(heightIndex)))

      // The application equals the structural term once the arguments are well-typed.
      val shortBase = have(shortDefinition.statement.right.head) by Tautology.from(shortDefinition)
      have(wellTypedFormula(semanticSignature1) ==> (appliedTerm1 === structuralTerm1)) by
        InstantiateForallSeq(variables1)(shortBase)
      val appliedEqStructural = have(appliedTerm1 === structuralTerm1) by Restate.from(lastStep)

      val structuralInSucc = have(structuralTerm1 ∈ app(heightFun)(S(heightIndex))) by Congruence.from(
        appliedEqStructural,
        appliedInSucc
      )


      val constructorBranches = adt.constructors.map { other =>
        // Distinct fresh names per argument: `variable[Ind]` derives its identifier
        // from the enclosing val (`branchVars`), so `.map(_ => variable[Ind])` would
        // give every argument the *same* identifier — collapsing e.g. `cons(a)(b)`
        // into `cons(branchVars)(branchVars)` and breaking the injectivity/Congruence
        // reasoning below for any constructor of arity ≥ 2.
        val branchVars = other.variables2.indices.map(i => Variable[Ind](s"branchVar$i")).toSeq
        val branchSubsts = other.variables2.zip(branchVars).map { case (v, fresh) => v := fresh }
        val branchSignature = branchVars.zip(other.signature2.map(_._2))
        val branchTerm = other.term2.substitute(branchSubsts*).asInstanceOf[Expr[Ind]]
        val branchBody =
          wellTypedFormula(branchSignature)(app(heightFun)(heightIndex)) /\
            (structuralTerm1 === branchTerm)
        val branch = existsSeq(branchVars, branchBody)

        val directBranch = if other == underlying then
          val transportedTyping = syntacticSignature.zipWithIndex.map { case ((v1, arg), idx) =>
            val v2 = branchVars(idx)
            val vEq = have(branchBody |- v1 === v2) by Weakening(underlying.injectivity.of(branchSubsts*))
            // `argsTypedAtHeight` is a conjunction of all argument typings; Congruence
            // only inspects top-level hypotheses, so first split out *this* argument's
            // typing with Tautology, then transport it across `v1 = v2`.
            arg match
              case lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef =>
                val v2Typed = have(branchBody |- v2 ∈ app(heightFun)(heightIndex)) by Restate
                have(branchBody |- v1 ∈ app(heightFun)(heightIndex)) by Congruence.from(v2Typed, vEq)
              case lisa.maths.SetTheory.Types.ADTv2.syntax.AST.TypeArg(name) =>
                val v2Typed = have(branchBody |- v2 ∈ typeExprToTerm(name)) by Restate
                have(branchBody |- v1 ∈ typeExprToTerm(name)) by Congruence.from(v2Typed, vEq)
          }
          have(branchBody |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by 
            Tautology.from(transportedTyping*)

        else
          have(branchBody |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by 
            Tautology.from(adt.injectivity(underlying, other).of(branchSubsts*))
          
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
      have(thesis) by Tautology.from(
        hValid,
        nInN,
        structuralInSucc,
        adt.heightSuccessorStrong of (h := heightFun, x := structuralTerm1, n := heightIndex),
        lastStep
      )
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
    val valueSubstitutions = variables1.zip(variables2).map((from, to) => from := to)
    instantiatedTheorem(
      theoremOwner = renderAppliedSymbol(fullName, typeVariablesSeq.size, normalizedTypeArguments(normalized)),
      suffix = "recursiveArgInHeight",
      substitutions = normalized ++ valueSubstitutions,
      baseTheorem = recursiveArgInHeight(heightFun, heightIndex)
    )
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

  private def structuralPairDecomposition(other: SemanticConstructor[?]): THM =
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
      have(thesis) by Tautology.from(
        structuralPairDecomposition(other),
        constructorTagDisequality(
          underlying.tagTerm,
          other.underlying.tagTerm,
          minTag,
          maxTag
        )
      )
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
  val injectivity = {
    
    val lemmaName = sourcecode.FullName(s"${fullName}/injectivity")
    if arity == 0 then 
      Lemma(using name = lemmaName)(appliedTerm1 === appliedTerm2) {have(thesis) by RightRefl}
    else
      val typedAssumption =
        simplify(wellTypedFormula(semanticSignature1 ++ semanticSignature2))
      Lemma(using name = lemmaName)(
        forallSeq(
          variables1 ++ variables2,
          typedAssumption ==> simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))
        )
      ) {

        val vars1WellTyped: Set[Expr[Prop]] = wellTypedSet(semanticSignature1)
        val vars2WellTyped: Set[Expr[Prop]] = wellTypedSet(semanticSignature2)

        // Both applications reduce to their structural terms once the arguments are well-typed.
        have(wellTypedFormula(semanticSignature1) ==> (appliedTerm1 === structuralTerm1)) by
          InstantiateForallSeq(variables1)(shortDefinition)
        val tappTerm1Def = thenHave(vars1WellTyped |- appliedTerm1 === structuralTerm1) by Restate

        have(wellTypedFormula(semanticSignature2) ==> (appliedTerm2 === structuralTerm2)) by
          InstantiateForallSeq(variables2)(shortDefinition)
        val tappTerm2Def = thenHave(vars2WellTyped |- appliedTerm2 === structuralTerm2) by Restate

        val definitionUnfolding = have(
          vars1WellTyped ++ vars2WellTyped |- (appliedTerm1 === appliedTerm2) <=>
            (structuralTerm1 === structuralTerm2)
        ) by Congruence.from(tappTerm2Def, tappTerm1Def)

        have(
          (appliedTerm1 === appliedTerm2) <=> (structuralTerm1 === structuralTerm2) |-
            (appliedTerm1 === appliedTerm2) <=> seqEq(variables1, variables2)
        ) by Congruence.from(underlying.injectivity)

        val equalityCharacterization = have(
          vars1WellTyped ++ vars2WellTyped |-
            simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))
        ) by Cut(definitionUnfolding, lastStep)

        have(typedAssumption ==> simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))) by
          Restate.from(equalityCharacterization)
        thenHave(thesis) by QuantifiersIntro(variables1 ++ variables2)
      }
  }

  /**
   * Case generated by this constructor when performing a proof by induction
   */
  val inductiveCase: Expr[Prop] = syntacticSignature
    .foldRight[Expr[Prop]](P(appliedTerm1)) { (el, fc) =>
      val (v, typ) = el
      typ match
        case SelfRef => forall(v, (v :: adt.term) ==> (P(v) ==> fc))
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
