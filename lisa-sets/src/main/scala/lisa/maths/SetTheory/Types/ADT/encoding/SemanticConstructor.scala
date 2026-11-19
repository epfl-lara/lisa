package lisa.maths.SetTheory.Types.ADT.encoding

import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiate
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.normalizeTypeSubstitutions
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.proofs.PropositionalFacts.altEqualityTransitivity
import lisa.maths.SetTheory.Types.ADT.support.semantics.DefinedSymbol
import lisa.maths.SetTheory.Types.ADT.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.prooflib.QuantifiersIntro

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
class SemanticConstructor(using line: sourcecode.Line, file: sourcecode.File)(
    val name: String,
    private[encoding] val underlying: SyntacticConstructor,
    private val adt: SyntacticADT
) {

  /**
   *  Full name of this constructor, i.e. concatenation of the ADT name and this
   *  constructor name.
   */
  val fullName: String = s"${adt.name}/${name}"

  override def toString: String = fullName

  /**
   * Type variables that may appear in the signature of this constructor.
   */

  /**
   * Sequence of type variables that may appear in the signature of this constructor.
   */
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq

  /**
   * Number of type variables in the signature of this constructor.
   */

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

  /**
   *  Constructor arguments whose domain is the ADT itself, i.e. the recursive
   *  positions, taken from `vars`.
   */
  def recursiveBinders(vars: Seq[Variable[Ind]]): Seq[Variable[Ind]] =
    syntacticSignature(vars).collect { case (v, SelfRef) => v }

  def selfRefVariables2: Seq[Variable[Ind]] = recursiveBinders(variables2)

  val typ: Expr[Ind] =
    semanticSignature.unzip._2.foldRight[Expr[Ind]](adt.term)((a, b) => (a ->: b))

  val adtName: String = adt.name
  val adtTerm: Expr[Ind] = adt.term

  /**
   * Arity of this constructor.
   */
  val arity: Int = variables.size

  /**
   * Internal representation of this constructor (i.e. as a tuple).
   */
  private[encoding] val structuralTerm: Expr[Ind] = underlying.term

  /**
   * Internal representation of this constructor (i.e. as a tuple).
   */
  private[encoding] val structuralTerm1: Expr[Ind] = underlying.term1

  /**
   *  Internal representation of this constructor (i.e. as a tuple) with an alternative
   *  set of variables.
   */
  private[encoding] val structuralTerm2: Expr[Ind] = underlying.term2

  private val internals = new ConstructorInternals(
    adt = adt,
    underlying = underlying,
    semanticSignature = semanticSignature,
    variables = variables,
    structuralTerm = structuralTerm,
    typ = typ
  )

  /**
   * Defines the constructor directly as its curried encoding.
   */
  private val definedClassFunction = new DefinedSymbol(
    name = fullName,
    parametersSeq = typeVariablesSeq,
    body = internals.witness
  )

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

  private val constructorDefinition: THM = Lemma(term === internals.witness) {
    have(thesis) by Congruence.from(definedClassFunction.definition)
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

  // –––– Theorems ––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––

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
    have(thesis) by Substitute(constructorDefinition)(internals.witnessEquations)
  }

  /**
   *  Lemma --- Introduction rule for this constructor.
   *
   *  `c(X1, ..., Xm) ∈ T1(X1, ..., Xm) -> ... -> Tn(X1, ..., Xm) -> ADT(X1, ..., Xm)`
   *
   *  Type variables remain schematic at the semantic layer.
   */
  val intro = Lemma(using name = sourcecode.FullName(s"${fullName}/intro"))(term :: typ) {
    have(thesis) by Congruence.from(constructorDefinition, internals.witnessTyping)
  }

  private val disjointnessSchemas = scala.collection.mutable.Map.empty[SemanticConstructor, THM]
  private val disjointnessInstances = scala.collection.mutable.Map.empty[SemanticConstructor, THM]
  private lazy val declarationIndex = adt.constructors.indexOf(underlying)

  /**
   * Caches each orientation, proving only the declaration-order orientation from the encoding.
   */
  private[encoding] def disjointnessSchema(other: SemanticConstructor): THM = {
    require(
      (adt eq other.adt) && underlying != other.underlying && declarationIndex >= 0 && other.declarationIndex >= 0,
      s"Disjointness requires two distinct constructors of ${adt.name}."
    )
    disjointnessSchemas.getOrElseUpdate(
      other, {
        val avoided = typeVariablesSeq ++ variables1 ++ variables2 ++ other.variables1 ++ other.variables2
        val args = (0 until arity + other.arity).foldLeft(Vector.empty[Variable[Ind]]) { (allocated, i) =>
          allocated :+ Variable[Ind](freshId(avoided ++ allocated, s"disjointArgument$i"))
        }
        val (leftArgs, rightArgs) = args.splitAt(arity)
        val leftTerm = appliedTerm(leftArgs)
        val rightTerm = other.appliedTerm(rightArgs)
        val leftTyping = wellTypedFormula(semanticSignature(leftArgs))
        val rightTyping = wellTypedFormula(other.semanticSignature(rightArgs))
        val typed = simplify(leftTyping /\ rightTyping)
        val body = typed ==> !(leftTerm === rightTerm)

        Lemma(forallSeq(args, body)) {
          if declarationIndex < other.declarationIndex then
            val leftDefinition = have(leftTyping ==> (leftTerm === underlying.term(leftArgs))) by
              InstantiateForallSeq(leftArgs)(shortDefinition)
            val rightDefinition = have(rightTyping ==> (rightTerm === other.underlying.term(rightArgs))) by
              InstantiateForallSeq(rightArgs)(other.shortDefinition)
            val structuralDisequality = have(!(underlying.term(leftArgs) === other.underlying.term(rightArgs))) by
              Tautology.from(
                Pair.extensionality.of(a := underlying.tagTerm, b := underlying.subterm(leftArgs), c := other.underlying.tagTerm, d := other.underlying.subterm(rightArgs)),
                underlying.tagDisequality(other.underlying)
              )
            have(body) subproof {
              assume(typed)
              val left = have(leftTerm === underlying.term(leftArgs)) by Tautology.from(leftDefinition)
              val right = have(rightTerm === other.underlying.term(rightArgs)) by Tautology.from(rightDefinition)
              have(!(leftTerm === rightTerm)) by Congruence.from(left, right, structuralDisequality)
            }
          else
            val reverse = have(typed ==> !(rightTerm === leftTerm)) by
              InstantiateForallSeq(rightArgs ++ leftArgs)(other.disjointnessSchema(this))
            have(body) subproof {
              assume(typed)
              have(!(rightTerm === leftTerm)) by Tautology.from(reverse)
              thenHave(!(leftTerm === rightTerm)) by Congruence
            }
          thenHave(thesis) by QuantifiersIntro(args)
        }
      }
    )
  }

  /**
   * Returns cached disjointness at this constructor's first and the other's second argument tuple.
   */
  def disjointness(other: SemanticConstructor): THM = {
    val schema = disjointnessSchema(other)
    disjointnessInstances.getOrElseUpdate(
      other,
      Lemma(
        (wellTypedFormula(semanticSignature1) /\ wellTypedFormula(other.semanticSignature2)) ==>
          !(appliedTerm1 === other.appliedTerm2)
      ) {
        have(thesis) by InstantiateForallSeq(variables1 ++ other.variables2)(schema)
      }
    )
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

    val lemmaName = sourcecode.FullName(s"${fullName}/injectivity")
    if arity == 0 then Lemma(using name = lemmaName)(appliedTerm1 === appliedTerm2) { have(thesis) by RightRefl }
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

  // –––– Exported semantic theorems ––––––––––––––––––––––––––––––––––––––––––

  private val heightArgument = Variable[Ind](freshId(typeVariablesSeq ++ variables1 ++ variables2, s"$fullName/heightArgument"))
  private val indexArgument = Variable[Ind](freshId(typeVariablesSeq ++ variables1 ++ variables2 :+ heightArgument, s"$fullName/indexArgument"))
  private val termArgument = Variable[Ind](freshId(typeVariablesSeq ++ variables1 ++ variables2 ++ Seq(heightArgument, indexArgument), s"$fullName/termArgument"))

  private lazy val semanticTypingFromHeight: THM = {
    val heightFun = heightArgument
    val n = indexArgument
    Lemma(
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
        adt.termsHaveHeight(underlying, heightFun, underlying.variables.zip(underlying.variables2).map((from, to) => from := to)),
        exTypedAtHeight
      )
    }
  }

  private lazy val appliedEqualityFromStructural: THM = {
    val heightFun = heightArgument
    val n = indexArgument
    val term0 = termArgument
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
        semanticTypingFromHeight
      )
    }
  }

  private lazy val recursiveArgInHeight: THM = {
    val heightFun = heightArgument
    val heightIndex = indexArgument
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
              case lisa.maths.SetTheory.Types.ADT.syntax.AST.SelfRef =>
                val v2Typed = have(branchBody |- v2 ∈ app(heightFun)(heightIndex)) by Restate
                have(branchBody |- v1 ∈ app(heightFun)(heightIndex)) by Congruence.from(v2Typed, vEq)
              case lisa.maths.SetTheory.Types.ADT.syntax.AST.TypeArg(name) =>
                val v2Typed = have(branchBody |- v2 ∈ typeExprToTerm(name)) by Restate
                have(branchBody |- v1 ∈ typeExprToTerm(name)) by Congruence.from(v2Typed, vEq)
          }
          have(branchBody |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by
            Tautology.from(transportedTyping*)
        else
          have(branchBody |- wellTypedFormula(underlying.signature1)(app(heightFun)(heightIndex))) by
            Tautology.from(underlying.disjointness(other).of(branchSubsts*))

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
  }

  /**
   * Instantiates constructor-argument typing from a height stage in the current proof.
   */
  def semanticTypingFromHeightAt(
      substitutions: Seq[TypeSubstitution],
      arguments: Seq[Expr[Ind]] = variables2
  )(heightFun: Expr[Ind], n: Expr[Ind])(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact = {
    require(arguments.size == arity, s"Constructor $fullName expects $arity arguments, received ${arguments.size}.")
    val normalized = normalizeTypeSubstitutions("constructor", fullName, typeVariablesSeq, substitutions)
    val valueSubstitutions = variables2.zip(arguments).map((from, to) => from := to)
    instantiate(semanticTypingFromHeight, normalized ++ valueSubstitutions ++ Seq(heightArgument := heightFun, indexArgument := n))
  }

  /**
   * Instantiates the predecessor-stage bound for recursive arguments in the current proof.
   */
  def recursiveArgInHeightAt(
      substitutions: Seq[TypeSubstitution],
      arguments: Seq[Expr[Ind]] = variables2
  )(heightFun: Expr[Ind], heightIndex: Expr[Ind])(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact = {
    require(arguments.size == arity, s"Constructor $fullName expects $arity arguments, received ${arguments.size}.")
    val normalized = normalizeTypeSubstitutions("constructor", fullName, typeVariablesSeq, substitutions)
    val valueSubstitutions = variables1.zip(arguments).map((from, to) => from := to)
    instantiate(recursiveArgInHeight, normalized ++ valueSubstitutions ++ Seq(heightArgument := heightFun, indexArgument := heightIndex))
  }

  /**
   * Instantiates the equality between a structural term and its constructor application.
   */
  def appliedEqualityFromStructuralAt(
      substitutions: Seq[TypeSubstitution],
      arguments: Seq[Expr[Ind]] = variables2
  )(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind])(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact = {
    require(arguments.size == arity, s"Constructor $fullName expects $arity arguments, received ${arguments.size}.")
    val normalized = normalizeTypeSubstitutions("constructor", fullName, typeVariablesSeq, substitutions)
    val valueSubstitutions = variables2.zip(arguments).map((from, to) => from := to)
    instantiate(appliedEqualityFromStructural, normalized ++ valueSubstitutions ++ Seq(heightArgument := heightFun, indexArgument := n, termArgument := term0))
  }
}
