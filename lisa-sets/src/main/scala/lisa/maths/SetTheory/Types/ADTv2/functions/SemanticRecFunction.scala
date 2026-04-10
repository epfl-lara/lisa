package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.Quantifiers.existsOneEpsilonUniqueness

/**
 * Minimal semantic representation of a recursive ADT function.
 *
 * Unlike [[SemanticFunction]], this class intentionally avoids generating proof obligations
 * (intro/elim/typing theorems). It only registers a symbol and stores user-provided cases.
 */
class SemanticRecFunction[N <: Arity](
    name: String,
    adt: SemanticADT[N],
    selfPlaceholder: Variable[Ind],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    val returnType: Expr[Ind]
)(using line: sourcecode.Line, file: sourcecode.File) {

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity

  val fullName = s"$name"
  var argType: Expr[Ind] = adt.term
  val typ = argType ->: returnType

  private val untypedDefinition = (f :: typ) /\ simplify(seqAnd(cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    val bodyWithSelf = body.substitute(selfPlaceholder := f)
    forallSeq(
      vars,
      wellTypedFormula(c.semanticSignature(vars)) ==> (f * c.appliedTerm(vars) === bodyWithSelf)
    )
  )))

  // Definition of the function symbol

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

  /** cases with selfPlaceholder substituted by the function term. */
  val caseDefinitions: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])] =
    cases.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (vars, body.substitute(selfPlaceholder := term))
    )


  // Lemmas
  
  /** Minimal typing obligations for recursive cases (placeholder proofs). */
  private val checkReturnType: Map[SemanticConstructor[N], JUSTIFICATION] =
    caseDefinitions.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (Lemma(wellTyped(c.semanticSignature(vars)) |- (body :: returnType)) {
        // Proof idea: same shape as non-recursive typing check, but recursive occurrences
        // require a typing hypothesis for `term` itself. This introduces circularity in
        // the current pipeline, so we keep a placeholder.

        println(s"checking return type for $c ($body :: $returnType)")
        println(s"thesis: ${thesis}")
        // have(thesis) by Typecheck.prove
        have(thesis) by Sorry
      })
    )

  /** Internal proof stack for uniqueness internals. */
  private val proofInternals = new SemanticRecFunctionInternals[N](
    functionName = fullName,
    adt = adt,
    untypedDefinition = untypedDefinition,
    cases = caseDefinitions,
    returnType = returnType,
    checkReturnType = checkReturnType,
    typ = typ
  )
  private val uniqueness = proofInternals.uniqueness

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


  /** Case equations as lemmas */
  val shortDefinition: Map[SemanticConstructor[N], THM] =
    caseDefinitions.map((c, caseDef) =>
      val (vars, body) = caseDef
      c -> (Lemma(
        simplify(wellTypedFormula(c.semanticSignature(vars)) ==>
          (term * c.appliedTerm(vars) === body))
      ) {

        have(forall(f, (term === f) <=> untypedDefinition)) by
          Restate.from(classFunctionCharacterization)

        thenHave(
          (term === term) <=> (term :: typ) /\
            (seqAnd(caseDefinitions.map { (c, caseDef) =>
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
        thenHave(thesis) by Tautology
      })
    )

  /** Introduction rule for the recursive symbol */
  val intro: THM = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
    
    have(forall(f, (term === f) <=> untypedDefinition)) by
      Restate.from(classFunctionCharacterization)

    thenHave(
      (term === term) <=> (term :: typ) /\
        (seqAnd(caseDefinitions.map { (c, caseDef) =>
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
