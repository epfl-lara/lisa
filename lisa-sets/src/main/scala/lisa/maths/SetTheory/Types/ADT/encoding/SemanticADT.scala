package lisa.maths.SetTheory.Types.ADT.encoding

import lisa.maths.Quantifiers.universalEquivalenceDistribution
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiate
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.normalizeTypeSubstitutions
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.proofs.PropositionalFacts._
import lisa.maths.SetTheory.Types.ADT.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.fol.FOL.SubstPair
import lisa.utils.prooflib.BasicStep.Restate
import lisa.utils.prooflib.BasicStep.RightForall
import lisa.utils.prooflib.InstantiateForall
import lisa.utils.prooflib.Thm

/**
 *  Semantic set theoretical interpretation of an algebraic data type. That is the least
 *  set closed under [[SemanticConstructor]].
 *
 *  E.g. list is the smallest set containing nil and closed under the cons function.
 *
 *  Injectivity between different constructors, structural induction and elimination rule
 *  are proved within this class.
 *
 *  Exported semantic lemmas are kept in formula form. Type variables and the induction
 *  predicate remain schematic, while value arguments are explicitly quantified.
 *
 *  @constructor generates a semantic interpretation for this ADT out of a syntactic one
 *  @param underlying the syntactic representation of this ADT
 *  @param constructors constructors of this ADT
 */
class SemanticADT(
    underlying: SyntacticADT,
    val constructors: Seq[SemanticConstructor]
) {

  /**
   * Height predicates and theorem instances with simultaneous type and value substitutions.
   */
  final class HeightAdapter private[SemanticADT] () {

    /**
     * The unspecialized height predicate.
     */
    def predicate(h: Expr[Ind]): Expr[Prop] = underlying.isHeight(h)
    private lazy val heightArgument = Variable[Ind](freshId(typeVariablesSeq, s"$name/heightArgument"))

    /**
     * Specializes the height predicate without substituting inside its argument.
     */
    def predicateAt(substitutions: Seq[TypeSubstitution])(h: Expr[Ind]): Expr[Prop] =
      predicate(heightArgument).substitute((substitutions :+ (heightArgument := h))*)

    /**
     * The datatype's general height function.
     */
    val function: Expr[Ind] = underlying.height

    private def specialize(base: Theorem, substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair])(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      instantiate(base, normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions) ++ valueSubstitutions)

    /**
     * Instantiates validity of the height function in the current proof.
     */
    def validAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.heightValid, substitutions, valueSubstitutions)

    /**
     * Instantiates existence of a height function in the current proof.
     */
    def existsAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.heightExists, substitutions, valueSubstitutions)

    /**
     * Instantiates monotonicity of height stages in the current proof.
     */
    def monotonicAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.heightMonotonic, substitutions, valueSubstitutions)

    /**
     * Instantiates emptiness of the zero height stage in the current proof.
     */
    def zeroAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.heightZero, substitutions, valueSubstitutions)

    /**
     * Instantiates preservation of stage membership in the current proof.
     */
    def membershipMonotonicAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.heightMembershipMonotonic, substitutions, valueSubstitutions)

    /**
     * Instantiates inclusion in the successor stage in the current proof.
     */
    def successorInclusionAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.heightSuccessorInclusion, substitutions, valueSubstitutions)

    /**
     * Instantiates the successor-stage characterization in the current proof.
     */
    def successorStrongAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.heightSuccessorStrong, substitutions, valueSubstitutions)

    /**
     * Instantiates existence of a height for a datatype member in the current proof.
     */
    def termHasHeightAt(substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      specialize(underlying.termHasHeight, substitutions, valueSubstitutions)

    /**
     * Instantiates a common height for a syntactic constructor's arguments.
     */
    def termsHaveHeightAt(c: SyntacticConstructor, heightFunction: Expr[Ind], substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair] = Seq.empty)(using
        proof: lisa.SetTheoryLibrary.Proof
    ): Thm =
      underlying.termsHaveHeight(c, heightFunction, normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions) ++ valueSubstitutions)

    /**
     * Instantiates a common height for a semantic constructor's arguments.
     */
    def termsHaveHeightAt(c: SemanticConstructor, heightFunction: Expr[Ind], substitutions: Seq[TypeSubstitution])(using proof: lisa.SetTheoryLibrary.Proof): Thm =
      termsHaveHeightAt(c.underlying, heightFunction, substitutions)

    /**
     * Instantiates type and value parameters of a semantic constructor's common-height theorem together.
     */
    def termsHaveHeightAt(c: SemanticConstructor, heightFunction: Expr[Ind], substitutions: Seq[TypeSubstitution], valueSubstitutions: Seq[SubstPair])(using
        proof: lisa.SetTheoryLibrary.Proof
    ): Thm =
      termsHaveHeightAt(c.underlying, heightFunction, substitutions, valueSubstitutions)
  }

  val height = HeightAdapter()

  /**
   * Name of this ADT.
   */
  val name: String = underlying.name

  /**
   * Identifier of this ADT.
   */
  val id: Identifier = underlying.polymorphicTerm.id

  /**
   * Type variables of this ADT.
   */

  /**
   * Sequence of type variables of this ADT.
   */
  val typeVariablesSeq: Seq[Variable[Ind]] = underlying.typeVariablesSeq

  /**
   * Number of type variables in this ADT.
   */

  /**
   *  Term representing this ADT where type variables are instantiated with given
   *  arguments.
   *
   *  @param args the instances of this ADT type variables
   */
  def term(args: Seq[Expr[Ind]]) = underlying.termAt(args)

  /**
   *  Term representing this ADT where type variables are instantiated with schematic
   *  variables.
   */
  val term: Expr[Ind] = underlying.term

  /**
   * Returns cached disjointness, with the first constructor's arguments quantified first.
   */
  def disjointness(c1: SemanticConstructor, c2: SemanticConstructor): Theorem =
    require(
      constructors.contains(c1) && constructors.contains(c2) && c1 != c2,
      s"Disjointness requires two distinct constructors of $name."
    )
    c1.disjointnessSchema(c2)

  /**
   *  Theorem --- Structural induction principle for this ADT.
   *
   *  `base cases => inductive cases => ∀x ∈ ADT. P(x)`
   */
  lazy val induction = Lemma.generated(
    constructors.foldRight[Expr[Prop]](forall(x, x :: term ==> P(x)))((c, f) => c.inductiveCase ==> f)
  ) { sp ?=>
    constructors.foldRight[(Expr[Prop], Expr[Prop], Thm)] {
      val prop = forall(x, x :: term ==> P(x))
      (prop, prop, have(prop <=> prop) by Restate)
    }((c, acc) =>
      val (oldBefore, oldAfter, fact) = acc
      val newBefore = underlying.inductiveCase(c.underlying) ==> oldBefore
      val newAfter = c.inductiveCase ==> oldAfter

      have(underlying.inductiveCase(c.underlying) <=> c.inductiveCase) subproof {
        val wellTypedVars: Seq[Expr[Prop]] = wellTyped(c.semanticSignature)
        val wellTypedVarsSet = wellTypedVars.toSet

        have(
          forallSeq(
            c.variables,
            wellTypedFormula(c.semanticSignature) ==> (c.appliedTerm === c.structuralTerm)
          )
        ) by Restate.from(c.shortDefinition)
        if c.arity > 0 then
          c.variables1.foldLeft(lastStep)((_, _) =>
            lastStep.statement.right.head match
              case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException
          )

        val eq = thenHave(wellTypedVarsSet |- c.appliedTerm === c.structuralTerm) by
          Restate
        have(P(c.appliedTerm) <=> P(c.appliedTerm)) by Restate
        thenHave(
          c.structuralTerm === c.appliedTerm |- P(c.structuralTerm) <=> P(c.appliedTerm)
        ) by Congruence
        have(wellTypedVarsSet |- P(c.structuralTerm) <=> P(c.appliedTerm)) by
          Cut(eq, lastStep)

        c.syntacticSignature.foldRight[(Expr[Prop], Expr[Prop], Seq[Expr[Prop]])](
          (P(c.structuralTerm), P(c.appliedTerm), wellTypedVars)
        )((el, fc) =>
          val (v, ty) = el
          val (fc1, fc2, wellTypedVars) = fc
          ty match
            case SelfRef =>
              val wellTypedV: Expr[Prop] = v :: term
              have(wellTypedVars |- (P(v) ==> fc1) <=> (P(v) ==> fc2)) by Cut(
                lastStep,
                leftImpliesEquivalenceWeak of (p := P(v), p1 := fc1, p2 := fc2)
              )
              thenHave(
                wellTypedVars.init |- wellTypedV ==> ((P(v) ==> fc1) <=> (P(v) ==> fc2))
              ) by RightImplies
              have(
                wellTypedVars.init |- (wellTypedV ==> (P(v) ==> fc1)) <=>
                  (wellTypedV ==> (P(v) ==> fc2))
              ) by Cut(
                lastStep,
                leftImpliesEquivalenceStrong of
                  (p := wellTypedV, p1 := P(v) ==> fc1, p2 := P(v) ==> fc2)
              )
              thenHave(
                wellTypedVars.init |- forall(
                  v,
                  (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2))
                )
              ) by RightForall
              have(
                wellTypedVars.init |-
                  forall(v, wellTypedV ==> (P(v) ==> fc1)) <=>
                  forall(v, wellTypedV ==> (P(v) ==> fc2))
              ) by Cut(
                lastStep,
                universalEquivalenceDistribution of
                  (
                    P := lambda(v, wellTypedV ==> (P(v) ==> fc1)),
                    Q := lambda(v, wellTypedV ==> (P(v) ==> fc2))
                  )
              )
              (
                forall(v, wellTypedV ==> (P(v) ==> fc1)),
                forall(v, wellTypedV ==> (P(v) ==> fc2)),
                wellTypedVars.init
              )
            // case RegularArg(t_) =>
            case TypeArg(typeName) =>
              val t = typeExprToTerm(typeName)
              thenHave(wellTypedVars.init |- v :: t ==> (fc1 <=> fc2)) by RightImplies
              have(wellTypedVars.init |- (v ∈ t ==> fc1) <=> (v :: t ==> fc2)) by Cut(
                lastStep,
                leftImpliesEquivalenceStrong of (p := v ∈ t, p1 := fc1, p2 := fc2)
              )
              thenHave(
                wellTypedVars.init |- forall(v, (v ∈ t ==> fc1) <=> (v :: t ==> fc2))
              ) by RightForall
              have(
                wellTypedVars.init |-
                  forall(v, v ∈ t ==> fc1) <=> forall(v, v :: t ==> fc2)
              ) by Cut(
                lastStep,
                universalEquivalenceDistribution of
                  (P := lambda(v, v ∈ t ==> fc1), Q := lambda(v, v :: t ==> fc2))
              )
              (forall(v, v ∈ t ==> fc1), forall(v, v :: t ==> fc2), wellTypedVars.init)
        )
        have(thesis) by Restate.from(lastStep)
      }
      val newFact = have(newBefore <=> newAfter) by Tautology.from(lastStep, fact)
      (newBefore, newAfter, newFact)
    )
    have(underlying.induction.statement.right.head |- thesis.right.head) by Cut(
      lastStep,
      equivalenceApply of (
        p1 := underlying.induction.statement.right.head,
        p2 := thesis.right.head
      )
    )
    have(thesis) by Cut(underlying.induction, lastStep)
  }

  /**
   *  Returns a map binding each constructor to formula describing whether x is an
   *  instance of it.
   */
  private lazy val isConstructorMap: Map[SemanticConstructor, Expr[Prop]] =
    constructors
      .map(c =>
        c -> existsSeq(
          c.variables2,
          wellTypedFormula(c.semanticSignature2) /\ (x === c.appliedTerm2)
        )
      )
      .toMap

  /**
   *  Returns a formula describing whether x is an instance of one of this ADT's
   *  constructors.
   */
  private lazy val isConstructor = seqOr(constructors.map(c => isConstructorMap(c)))

  /**
   *  Theorem --- Pattern matching principle (also known as elimination rule) for this
   *  ADT.
   *
   *  `∀x. x ∈ ADT ==> x = c * x1 * ... * xn for some constructor c and xi, ..., xj ∈ ADT`
   */
  lazy val elim = Lemma.generated(forall(x, x :: term ==> simplify(isConstructor))) { sp ?=>
    val property = lambda(x, isConstructor)
    val cases = constructors.map { c =>
      val typings = wellTypedSet(c.semanticSignature)
      val branch = isConstructorMap(c).substitute(x := c.appliedTerm)

      // Supply this constructor's arguments as witnesses for its own disjunct.
      def introduceWitnesses(formula: Expr[Prop], arguments: List[Expr[Ind]]): Thm = arguments match
        case Nil => have(typings |- formula) by Restate
        case scala.collection.immutable.::(argument, rest) =>
          formula match
            case exists(v, body) =>
              val premise = introduceWitnesses(body.substitute(v := argument), rest)
              have(typings |- formula) by RightExists.withParameters(body, v, argument)(premise)
            case _ => throw UnreachableException

      val witness = introduceWitnesses(branch, c.variables.toList)
      val constructorCase = have(typings |- isConstructor.substitute(x := c.appliedTerm)) by Weakening(witness)

      // Abstract the typed arguments; recursive induction hypotheses are unused.
      c.syntacticSignature.foldRight[Thm](constructorCase) { case ((v, ty), fact) =>
        val withHypothesis = ty match
          case SelfRef => have(fact.statement.left |- isConstructor.substitute(x := v) ==> fact.statement.right.head) by Weakening(fact)
          case TypeArg(_) => fact
        val typing = v :: ty.getOrElse(term)
        val implication = have((withHypothesis.statement.left - typing) |- typing ==> withHypothesis.statement.right.head) by Restate.from(withHypothesis)
        have(implication.statement.left |- forall(v, implication.statement.right.head)) by RightForall(implication)
      }
    }
    have(thesis) by Tautology.from((Seq[Thm](induction of (P := property)) ++ cases)*)
  }
}
