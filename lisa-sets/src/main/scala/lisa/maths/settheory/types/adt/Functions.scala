package lisa.maths.settheory.types.adt

import ADTDefinitions.*
import lisa.maths.settheory.SetTheory.{*, given}
import Helpers.*
import Helpers.{/\, ===, \/}
import lisa.maths.settheory.types.TypeLib.{ |=> }
import lisa.maths.settheory.types.TypeSystem.{ ::, * }




/**
  * 
  */
class SemanticFunction[N <: Arity](name: String, adt: SemanticADT[N], cases: Map[SemanticConstructor[N], (Seq[Variable], Term)], returnType: Term)(using line: sourcecode.Line, file: sourcecode.File) {

  /**
    * Requirements for the function to be well defined. If they are met, returns a map binding 
    * each constructor to a theorem stating that the case is well typed.
    * 
    * @throws IllegalArgumentException if the requirements are not met
    */
  private val checkReturnType: Map[SemanticConstructor[N], THM] = 
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
  val typeVariables: Variable ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable] = adt.typeVariablesSeq

  /**
   * Number of type variables appearing in this function.
   */
  val typeArity: N = adt.typeArity

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
  private val untypedFunctional = FunctionDefinition(fullName, line.value, file.value)(typeVariablesSeq, f, untypedDefinition, uniqueness).label

  /**
   * Function where type variables are instantiated with schematic symbols.
   */
  val term = untypedFunctional.applySeq(typeVariablesSeq)

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
  val intro = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
    have(forall(f, (term === f) <=> untypedDefinition)) by Exact(untypedFunctional.definition)
    thenHave((term === term) <=> (term :: typ) /\ (/\ (cases.map((c, caseDef) =>
      {val (vars, body) = caseDef
      forallSeq(vars, /\ (wellTyped(c.semanticSignature(vars))) ==> (term * c.appliedTerm(vars) === body))}
      )))) by InstantiateForall(term)
    thenHave(term :: typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
  }
}
