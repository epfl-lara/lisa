package lisa.maths.settheory.types.adt

import ADTDefinitions.*
import lisa.maths.settheory.SetTheory.{*, given}
import Helpers.*
import Helpers.{/\, ===, \/}
import lisa.maths.settheory.types.TypeLib.{ |=> }
import lisa.maths.settheory.types.TypeSystem.{ ::, * }
import ADTHelperTheorems as ADTThm
import ADTThm.{N}
import javax.lang.model.element.VariableElement


class SyntacticFunction(using line: sourcecode.Line, file: sourcecode.File)(
  name: String,
  adt: SyntacticADT, 
  cases: Map[SyntacticConstructor, Term => Term], 
  returnType: Term,
  typeVariables: Seq[Variable],
  ) {


  private def isNextIteration(n: Term, fn: Term)(newF: Term) =  functionFrom(newF, app(h, successor(n)), returnType) /\ 
    (/\ (cases.map((c, body) => forallSeq(c.variables, in(c.term, app(h, successor(n))) ==> (newF * c.term === body(fn))))))

  private def isExtendedNextIteration(restr: Term)(newF: Term): Formula = isNextIteration(relationDomain(restr), unionRange(restr))(newF)

  private def isTheHeightFunction(hf: Term): Formula =
    functional(hf) /\ (relationDomain(hf) === N) /\ forall(n, in(n, N) ==> isExtendedNextIteration(restrictedFunction(hf, n))(app(hf, n)))


  val hf = variable

  private val fIsTheHeightFunction: Formula = isTheHeightFunction(f)
  private val hfIsTheHeightFunction: Formula = isTheHeightFunction(hf)

  private val heightFunUniqueness = Axiom(existsOne(hf, hfIsTheHeightFunction))

  private val heightFunctionExistence = Lemma(exists(hf, hfIsTheHeightFunction)) {
    have(thesis) by Apply(lisa.maths.Quantifiers.existsOneImpliesExists of (P := lambda(hf, hfIsTheHeightFunction))).on(heightFunUniqueness.asInstanceOf)
  }

  private val heightFunctionUniqueness2 = Lemma((fIsTheHeightFunction, hfIsTheHeightFunction) |- f === hf) {
    have(thesis) by Cut(heightFunUniqueness, ADTThm.existsOneUniqueness of (P := lambda(hf, hfIsTheHeightFunction), x := f, y := hf))
  }

  private def termDefinition(fun: Term): Formula = forall(t, in(t, fun) <=> forall(h, adt.hIsTheHeightFunction ==> forall(hf, hfIsTheHeightFunction ==> in(t, unionRange(hf)))))

  private val termExistence = Axiom(existsOne(z, termDefinition(z))) 

  /**
   * Class function defining the ADT. Takes as parameters the type variables of the ADT and return the set of all its instances.
   */
  val polymorphicTerm = FunctionDefinition(name, line.value, file.value)(typeVariables, z, termDefinition(z), termExistence).label

  /**
   * The set of all instances of the ADT where the type variables are not instantiated (i.e. are kept variable).
   */
  val term = polymorphicTerm.applySeq(typeVariables)

  /**
   * Definition of this ADT's term.
   */
  private val termDefinition: Formula = termDefinition(term)

  /**
   * Lemma --- This ADT satisfies its definition.
   *
   *     `adt = ∪ height(n)`
   */
  private val termSatisfiesDefinition = Lemma(termDefinition) {
    have(thesis) by InstantiateForall(term)(polymorphicTerm.definition)
  }

  private val termHasHeight = Lemma((adt.hIsTheHeightFunction, hfIsTheHeightFunction, in(f, term)) |- ∃(n, in(n, N) /\ in(x, app(h, n)))) {

    // STEP 0 : Instantiate the definition of this ADT and recover the forward and backward implications
    val termDefinition = have(in(x, term) <=> forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h)))) by InstantiateForall(x)(termSatisfiesDefinition)
    val termDefinitionForward = have(in(x, term) |- forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h)))) by Cut(
      termDefinition,
      ADTThm.equivalenceApply of (p1 := in(x, term), p2 := forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h))))
    )
    val termDefinitionBackward = have(forall(hf, hfIsTheHeightFunction ==> in(x, unionRange(h))) |- in(x, term)) by Cut(
      termDefinition,
      ADTThm.equivalenceRevApply of (p2 := in(x, term), p1 := forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h))))
    )

    // STEP 1 : Prove that an element is in this ADT if and only if it is in one of the images of the height function.
    have(hfIsTheHeightFunction |- in(x, term) <=> in(x, unionRange(h))) subproof {

      // STEP 1.1 : Forward implication
      have(forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h))) |- forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h)))) by Hypothesis
      thenHave(forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h))) |- hfIsTheHeightFunction ==> in(x, unionRange(h))) by InstantiateForall(h)
      thenHave((forall(h, hfIsTheHeightFunction ==> in(x, unionRange(h))), hfIsTheHeightFunction) |- in(x, unionRange(h))) by Restate

      val forward = have(hfIsTheHeightFunction |- in(x, term) ==> in(x, unionRange(h))) by Apply(lastStep).on(termDefinitionForward)

      // STEP 1.2 : Backward implication, follows from uniqueness of the height function
      have(in(x, unionRange(h)) |- in(x, unionRange(h))) by Hypothesis
      thenHave((f === h, in(x, unionRange(h))) |- in(x, unionRange(f))) by RightSubstEq.withParametersSimple(List((f, h)), lambda(h, in(x, unionRange(h))))
      have((fIsTheHeightFunction, hfIsTheHeightFunction, in(x, unionRange(h))) |- in(x, unionRange(f))) by Cut(heightFunctionUniqueness2, lastStep)
      thenHave((hfIsTheHeightFunction, in(x, unionRange(h))) |- fIsTheHeightFunction ==> in(x, unionRange(f))) by RightImplies
      thenHave((hfIsTheHeightFunction, in(x, unionRange(h))) |- forall(f, fIsTheHeightFunction ==> in(x, unionRange(f)))) by RightForall
      have((hfIsTheHeightFunction, in(x, unionRange(h))) |- in(x, term)) by Cut(lastStep, termDefinitionBackward)
      val backward = thenHave(hfIsTheHeightFunction |- in(x, unionRange(h)) ==> in(x, term)) by RightImplies

      have(thesis) by RightIff(forward, backward)
    }

    // STEP 2: Conclude by instantiating the union range membership lemma
    have(hfIsTheHeightFunction |- in(x, term) <=> ∃(n, in(n, relationDomain(h)) /\ in(x, app(h, n)))) by Apply(ADTThm.equivalenceRewriting).on(ADTThm.unionRangeMembership.asInstanceOf, lastStep)

    thenHave((hfIsTheHeightFunction, relationDomain(h) === N) |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) by RightSubstEq.withParametersSimple(
      List((relationDomain(h), N)),
      lambda(z, in(x, term) <=> ∃(n, in(n, z) /\ in(x, app(h, n))))
    )
  }


}

/**
  * 
  */
class SemanticFunction(name: String, adt: SemanticADT, cases: Map[SemanticConstructor, (Seq[Variable], Term)], returnType: Term)(using line: sourcecode.Line, file: sourcecode.File) {

  /**
    * Requirements for the function to be well defined. If they are met, returns a map binding 
    * each constructor to a theorem stating that the case is well typed.
    * 
    * @throws IllegalArgumentException if the requirements are not met
    */
  private val checkReturnType: Map[SemanticConstructor, THM] = 
    val constructors = adt.constructors.toSet
    val casesConstructors = cases.keySet

    val constructorsMinusCases = constructors -- casesConstructors
    val casesMinusConstructors = casesConstructors -- constructors

    // STEP 1: Check that all constructors are covered
    if !constructorsMinusCases.isEmpty then
      throw new IllegalArgumentException(s"Case for ${constructorsMinusCases.head.fullName} is missing.")
    // STEP 2: Check that there are no extra cases
    else if !casesMinusConstructors.isEmpty then
      throw new IllegalArgumentException(s"${casesMinusConstructors.head.fullName} is not a constructor of ${adt.name}.")
    else
      (for c <- cases.keys yield
        val (vars, body) = cases(c)
        // STEP 3: Check that for each case the number of variables provided by the user matches the arity of the constructor
        if vars.length != c.arity then
          throw new IllegalArgumentException(s"Case ${c.fullName}: ${vars.length} variables were provided whereas the arity of ${c.fullName} is ${c.arity}.")
        // STEP 4: Check for each case that the body is well typed.
        // If this is the case, generate a theorem stating it.
        else
          c -> Lemma(wellTyped(c.semanticSignature) |- body :: returnType) {
            have(thesis) by TypeChecker.prove
          }
      ).toMap


  /**
    * Type variables appearing in this function.
    */
  val typeVariables = adt.typeVariables

  /**
   * Number of type variables appearing in this function.
   */
  val typeArity = typeVariables.length

  /**
    * Full name of this function. That is the name of the function prefixed by the name of the ADT.
    */
  val fullName = s"$name"
  //val fullName = s"${adt.name}/$name"

  val typ = adt.term |=> returnType

  /**
   * Definition of this function.
   *
   * Formally it is the only function whose domain is the ADT and such that for each constructor c f(c(x1, ..., xn)) = case_c(x1, ..., xn)
   */
  private val untypedDefinition = (f :: typ) /\ simplify(/\ (cases.map((c, caseDef) =>
      val (vars, body) = caseDef
      forallSeq(vars, wellTypedFormula(c.semanticSignature(vars)) ==> (f * c.appliedTerm(vars) === body)))
    ))

  /**
   * Lemma --- Uniqueness of this function.
   */
  private val uniqueness = Axiom(existsOne(f, untypedDefinition))

  /**
   * Set theoretic definition of the constructor.
   */
  private val untypedFunctional = FunctionDefinition(fullName, line.value, file.value)(typeVariables, f, untypedDefinition, uniqueness).label

  /**
   * Function where type variables are instantiated with schematic symbols.
   */
  val term = untypedFunctional.applySeq(typeVariables)

  /**
   * Lemma --- The body of this function correpsonds to the cases provided by the user.
   *
   *     `for each constructor c, ∀x1, ..., xn. f(c(x1, ..., xn)) = case_c(x1, ..., xn)`
   */
  val shortDefinition = cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    c -> Lemma(simplify(wellTypedFormula(c.semanticSignature(vars))) ==> (term * c.appliedTerm(vars) === body)) {
      have(forall(f, (term === f) <=> untypedDefinition)) by Exact(untypedFunctional.definition)
      thenHave((term === term) <=> (term :: typ) /\ (/\ (cases.map((c, caseDef) =>
          {val (vars, body) = caseDef
          forallSeq(vars, wellTypedFormula(c.semanticSignature(vars)) ==> (term * c.appliedTerm(vars) === body))}
        )))) by InstantiateForall(term)
      thenHave(thesis) by Weakening
  })



  /**
   * Typing rule of the constructor.
   */
  val intro = Lemma(forallSeq(typeVariables, term :: typ)) {
    have(forall(f, (term === f) <=> untypedDefinition)) by Exact(untypedFunctional.definition)
    thenHave((term === term) <=> (term :: typ) /\ (/\ (cases.map((c, caseDef) =>
      {val (vars, body) = caseDef
      forallSeq(vars, /\ (wellTyped(c.semanticSignature(vars))) ==> (term * c.appliedTerm(vars) === body))}
      )))) by InstantiateForall(term)
    thenHave(term :: typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariables)
  }
}
