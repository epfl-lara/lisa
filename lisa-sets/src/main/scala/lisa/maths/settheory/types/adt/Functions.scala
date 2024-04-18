/**
 * Defines set theoretic functions over Algebraic Data Types
 */

package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{_, given}
import lisa.maths.settheory.types.TypeLib.|=>
import lisa.maths.settheory.types.TypeSystem.::
import lisa.maths.settheory.types.TypeSystem._

import ADTDefinitions.*
import Helpers.*
import Helpers.{/\, ===, \/}

/**
 * Set theoretic interpretation of a function over an ADT.
 *
 * @tparam N the number of type variables of the domain of this function
 * @param name the name of this function
 * @param adt the domain of this function
 * @param cases the body of this function for each constructor
 * @param returnType the codomain of this function
 * @param line the line at which this function is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 * @param file the file in which this function is defined. Usually fetched automatically by the compiler.
 * Used for error reporting
 */
class SemanticFunction[N <: Arity](name: String, adt: SemanticADT[N], cases: Map[SemanticConstructor[N], (Seq[Variable], Term)], returnType: Term)(using line: sourcecode.Line, file: sourcecode.File) {

  /**
   * Map binding each constructor to a theorem stating that the case is well typed.
   */
  private val checkReturnType: Map[SemanticConstructor[N], THM] =
    (for c <- cases.keys yield
      val (vars, body) = cases(c)
        c -> Lemma(wellTyped(c.semanticSignature(vars)) |- body :: returnType) {
          have(thesis) by TypeChecker.prove
        }
    ).toMap

  /**
   * Type variables appearing in this function's domain.
   */
  val typeVariables: Variable ** N = adt.typeVariables

  /**
   * Sequence of type variables appearing in this function's domain.
   */
  val typeVariablesSeq: Seq[Variable] = adt.typeVariablesSeq

  /**
   * Number of type variables appearing in this function.
   */
  val typeArity: N = adt.typeArity

  /**
   * Full name of this function. That is the name of the function prefixed by the name of the ADT.
   */
  val fullName = s"$name"
  // val fullName = s"${adt.name}/$name"

  val typ = adt.term |=> returnType

  /**
   * Definition of this function.
   *
   * Formally it is the only function whose domain is the ADT and such that for each constructor c f * (c * x1 * ... * xn) = case(c, x1, ..., xn)
   */
  private val untypedDefinition = (f :: typ) /\ simplify(/\(cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    forallSeq(vars, wellTypedFormula(c.semanticSignature(vars)) ==> (f * c.appliedTerm(vars) === body))
  )))

  /**
   * Lemma --- Uniqueness of this function.
   */
  private val uniqueness = Axiom(existsOne(f, untypedDefinition))

  /**
   * Set theoretic definition of the constructor.
   */
  private val classFunction = FunctionDefinition(fullName, line.value, file.value)(typeVariablesSeq, f, untypedDefinition, uniqueness).label

  /**
    * Identifier of this function.
    */
  val id: Identifier = classFunction.id


  /**
   * Function where type variables are instantiated with schematic symbols.
   */
  val term = classFunction.applySeq(typeVariablesSeq)

  /**
   * Lemma --- The body of this function correpsonds to the cases provided by the user.
   *
   *     `for each constructor c, ∀x1, ..., xn. f * (c * x1 * ... * xn) = case(c, x1, ..., xn)`
   */
  val shortDefinition = cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    c -> Lemma(simplify(wellTypedFormula(c.semanticSignature(vars))) ==> (term * c.appliedTerm(vars) === body)) {
      have(forall(f, (term === f) <=> untypedDefinition)) by Exact(classFunction.definition)
      thenHave((term === term) <=> (term :: typ) /\ (/\(cases.map((c, caseDef) => {
        val (vars, body) = caseDef
        forallSeq(vars, wellTypedFormula(c.semanticSignature(vars)) ==> (term * c.appliedTerm(vars) === body))
      })))) by InstantiateForall(term)
      thenHave(forallSeq(vars, wellTypedFormula(c.semanticSignature(vars)) ==> (term * c.appliedTerm(vars) === body))) by Weakening
      vars.foldLeft(lastStep)((l, _) =>
        lastStep.statement.right.head match
          case Forall(v, phi) => thenHave(phi) by InstantiateForall(v)
          case _ => throw UnreachableException
      )
    }
  )

  /**
   * Lemma --- Introduction rule
   *
   *    `f : ADT -> T`
   *
   * where `T` is the return type of this function
   */
  val intro = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
    have(forall(f, (term === f) <=> untypedDefinition)) by Exact(classFunction.definition)
    thenHave((term === term) <=> (term :: typ) /\ (/\(cases.map((c, caseDef) => {
      val (vars, body) = caseDef
      forallSeq(vars, /\(wellTyped(c.semanticSignature(vars))) ==> (term * c.appliedTerm(vars) === body))
    })))) by InstantiateForall(term)
    thenHave(term :: typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
  }
}
