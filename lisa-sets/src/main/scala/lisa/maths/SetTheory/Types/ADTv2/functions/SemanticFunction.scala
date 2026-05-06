package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Pi.{->:}
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.Quantifiers.existsOneEpsilonUniqueness
import lisa.maths.SetTheory.Types.ADTv2.support.**

/**
 *  Set theoretic interpretation of a function over an ADT.
 *
 *  @tparam N the number of type variables of the domain of this function
 *  @param name the name of this function
 *  @param adt the domain of this function
 *  @param cases the body of this function for each constructor
 *  @param returnType the codomain of this function
 *  @param line the line at which this function is defined. Usually fetched automatically
 *    by the compiler. Used for error reporting
 *  @param file the file in which this function is defined. Usually fetched automatically
 *    by the compiler. Used for error reporting
 */
class SemanticFunction[N <: Arity](
    name: String,
    adt: SemanticADT[N],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    returnType: Expr[Ind]
)(using line: sourcecode.Line, file: sourcecode.File) {


  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity

  val fullName = s"$name"
  val typ: Expr[Ind] = adt.term ->: returnType


  private val checkReturnType: Map[SemanticConstructor[N], THM] =
    (for c <- cases.keys yield
      val (vars, body) = cases(c)
      c -> Lemma(wellTyped(c.semanticSignature(vars)) |- (body :: returnType)) {
        have(thesis) by Typecheck.prove
      }
    ).toMap

  /** Internal proof stack for uniqueness internals. */
  private val proofInternals = new SemanticFunctionInternals[N](
    functionName = fullName,
    adt = adt,
    cases = cases,
    returnType = returnType,
    checkReturnType = checkReturnType,
    typ = typ
  )


  private val untypedDefinition = proofInternals.untypedDefinition
  private val uniqueness = proofInternals.uniqueness

  // Definition of the function symbol

  /** Class function corresponding to this semantic function. */
  private val classFunction: Constant[?] = {
    val classFunctionExpr: Expr[?] = lisa.utils.fol.FOL.Abs.apply(
      xs = typeVariablesSeq,
      t = ε(f, untypedDefinition)
    )
    type S
    given lisa.utils.fol.FOL.IsSort[S] =
      lisa.utils.fol.FOL.unsafeSortEvidence(classFunctionExpr.sort)
    DEF(using name = fullName)(classFunctionExpr.asInstanceOf[Expr[S]])
  }
  classFunction.printAs(args => renderAppliedSymbol(fullName, typeVariablesSeq.size, args))

  val id: Identifier = classFunction.id
  val term: Expr[Ind] = (classFunction #@@ typeVariablesSeq).asInstanceOf[Expr[Ind]]

  // Lemmas

  private val classFunctionCharacterization =
    Lemma(forall(f, (term === f) <=> untypedDefinition)) {
      val epsilonWitness = ε(f, untypedDefinition)

      val epsilonCharacterization = have(
        untypedDefinition <=> (f === epsilonWitness)
      ) by Tautology.from(
        uniqueness,
        existsOneEpsilonUniqueness of (
          x := f,
          y := f,
          P := λ(f, untypedDefinition)
        )
      )

      val classTermIsEpsilon =
        have(term === epsilonWitness) by Congruence.from(classFunction.definition)

      val toRight = have((term === f) ==> (f === epsilonWitness)) subproof {
        assume(term === f)
        val termEqF = have(term === f) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEpsilon)
        have(f === epsilonWitness) by Congruence.from(termEqF, termEqEpsilon)
        thenHave(thesis) by Restate
      }

      val toLeft = have((f === epsilonWitness) ==> (term === f)) subproof {
        assume(f === epsilonWitness)
        val fEqEpsilon = have(f === epsilonWitness) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEpsilon)
        have(term === f) by Congruence.from(termEqEpsilon, fEqEpsilon)
        thenHave(thesis) by Restate
      }

      val equalityRewriting = have((term === f) <=> (f === epsilonWitness)) by
        Tautology.from(toRight, toLeft)

      have((term === f) <=> untypedDefinition) by
        Tautology.from(equalityRewriting, epsilonCharacterization)

      thenHave(thesis) by RightForall
    }

  /**
   *  Lemma --- The body of this function corresponds to the cases provided by the user.
   *
   *  `for each constructor c, ∀x1, ..., xn. f * (c * x1 * ... * xn) = case(c, x1, ..., xn)`
   */
  val shortDefinition = cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    c -> Lemma(
      simplify(wellTypedFormula(c.semanticSignature(vars))) ==>
        (term * c.appliedTerm(vars) === body)
    ) {

      have(forall(f, (term === f) <=> untypedDefinition)) by
        Restate.from(classFunctionCharacterization)
      thenHave(
        (term === term) <=> (term :: typ) /\
          (seqAnd(cases.map { (c, caseDef) =>
            val (vars, body) = caseDef
            forallSeq(
              vars,
              wellTypedFormula(c.semanticSignature(vars)) ==>
                (term * c.appliedTerm(vars) === body)
            )
          }))
      ) by InstantiateForall(term)
      thenHave(forallSeq(
        vars,
        wellTypedFormula(c.semanticSignature(vars)) ==>
          (term * c.appliedTerm(vars) === body)
      )) by Weakening
      vars.foldLeft(lastStep)((l, _) =>
        lastStep.statement.right.head match
          case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
          case _ => throw UnreachableException
      )

    }
  )

  /**
   *  Lemma --- Introduction rule
   *
   *  `f : ADT -> T`
   *
   *  where `T` is the return type of this function
   */
  val intro = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
    have(forall(f, (term === f) <=> untypedDefinition)) by
      Restate.from(classFunctionCharacterization)
    thenHave(
      (term === term) <=> (term :: typ) /\
        (seqAnd(cases.map { (c, caseDef) =>
          val (vars, body) = caseDef
          forallSeq(
            vars,
            seqAnd(wellTyped(c.semanticSignature(vars))) ==>
              (term * c.appliedTerm(vars) === body)
          )
        }))
    ) by InstantiateForall(term)
    thenHave(term :: typ) by Weakening
    thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
  }
}
