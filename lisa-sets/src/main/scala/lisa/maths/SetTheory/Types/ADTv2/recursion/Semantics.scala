package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{ConstructorHeadPattern, Pattern, PatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UniqueCharacterizedSymbol
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.SetTheory.Types.ADTv2.support.core.`**`

final class RecFunSemantics[N <: Arity](
    val name: String,
    val adt: SemanticADT[N],
    val argType: Expr[Ind],
    val typeSubstitutions: Seq[TypeSubstitution],
    selfPlaceholder: Variable[Ind],
    patternMatching: PatternSystem[N],
    val returnType: Expr[Ind]
) {

  private val spec = FunSpec[N](
    functionName = name,
    adt = adt,
    argType = argType,
    typeSubstitutions = typeSubstitutions,
    selfPlaceholder = selfPlaceholder,
    patternMatching = patternMatching,
    returnType = returnType
  )

  val typeVariables: Variable[Ind] ** N = adt.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = spec.typeVariablesSeq
  val typeArity: N = spec.typeArity
  val typ: Expr[Ind] = spec.typ
  val rawPatterns: Seq[Pattern[N]] = spec.cases

  println(s"=== RecFunSemantics for $name ===")

  private val witness: Witness[N] = new Witness[N](spec)

  println(s"=== Witness for $name ===")
  private val approx = new Approx[N](spec, witness)
  println(s"=== Approx for $name ===")
  private val approxProp = new ApproxProp[N](spec, witness, approx)
  println(s"=== ApproxProp for $name ===")
  val existence: Existence[N] = new Existence[N](spec, witness, approx, approxProp)
  println(s"=== Existence for $name ===")

  private val functionUniquenessProof = new Uniqueness[N](spec)
  println(s"=== Uniqueness for $name ===")

  private val untypedDef: Expr[Prop] = spec.untypedDefinition(f)

  private def definitionFormula(v: Expr[Ind]): Expr[Prop] =
    spec.untypedDefinition(v)

  val uniqueness: THM = Lemma(existsOne(f, untypedDef)) {

    val existencePart = have(∃(x, definitionFormula(x))) by
      Restate.from(existence.witnessExists of (f := x))

    have(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) by
      Restate.from(functionUniquenessProof.recursivePointwisePlan)
    thenHave(∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y))) by RightForall

    val uniquenessAll = thenHave(
      ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) by RightForall

    have(
      ∃(x, definitionFormula(x)) /\
        ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) by Tautology.from(existencePart, uniquenessAll)

    have(thesis) by Tautology.from(
      lastStep,
      existsOneAlternativeDefinition of (x := f, P := λ(f, untypedDef))
    )
  }

  private val definedClassFunction = UniqueCharacterizedSymbol(
    name = name,
    typeVariablesSeq = typeVariablesSeq,
    witnessVar = f,
    definitionAt = definitionFormula
  )(uniqueness)

  val id: Identifier = definedClassFunction.id

  def term(args: Seq[Expr[Ind]]): Expr[Ind] = definedClassFunction.term(args)

  val term: Expr[Ind] = definedClassFunction.term

  val classDefinitionFact: THM = definedClassFunction.definitionFact

  private val classFunctionCharacterization: THM = definedClassFunction.characterization

  private val compiledCases: Seq[Pattern[N]] =
    rawPatterns.map(pattern =>
      pattern.withBody(pattern.body.substitute(spec.selfPlaceholder := term))
    )

  val patterns: Seq[Pattern[N]] = compiledCases
  val cases: Seq[Pattern[N]] = patterns

  private def compiledPatternFor(constructor: SemanticConstructor[N]): Pattern[N] =
    compiledCases.find(pattern =>
      ConstructorHeadPattern.require(pattern).correspondsTo(constructor)
    ).getOrElse(
      throw new IllegalArgumentException(s"No compiled pattern registered for constructor ${constructor.name}.")
    )

  private val shortDefinitionByPattern: Map[Pattern[N], THM] =
    patterns.map(pattern =>
      pattern -> Lemma(
        simplify(
          pattern.branchPremise ==>
            (term * pattern.inputTerm === pattern.body)
        )
      ) {
        have(forall(f, (term === f) <=> untypedDef)) by
          Restate.from(classFunctionCharacterization)

        thenHave(
          (term === term) <=>
            (term :: spec.typ) /\
            (seqAnd(compiledCases.map { branch =>
              forallSeq(
                branch.binders,
                branch.branchPremise ==>
                  (term * branch.inputTerm === branch.body)
              )
            }))
        ) by InstantiateForall(term)

        thenHave(
          forallSeq(
            pattern.binders,
            pattern.branchPremise ==>
              (term * pattern.inputTerm === pattern.body)
          )
        ) by Weakening

        pattern.binders.foldLeft(lastStep)((_, _) =>
          lastStep.statement.right.head match
            case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        thenHave(thesis) by Tautology
      }
    ).toMap

  def shortDefinition(pattern: Pattern[N]): THM =
    shortDefinitionByPattern(pattern)

  def elimByPattern(pattern: Pattern[N]): THM =
    shortDefinition(pattern)

  def elimByConst(constructor: SemanticConstructor[N]): THM =
    shortDefinitionByPattern(compiledPatternFor(constructor))

  def elim(pattern: Pattern[N]): THM =
    elimByPattern(pattern)

  def elim(constructor: SemanticConstructor[N]): THM =
    elimByConst(constructor)

  def shortDefinition(constructor: SemanticConstructor[N]): THM =
    elimByConst(constructor)

  val elimTotal: THM = Lemma(
    seqAnd(patterns.map(pattern =>
      simplify(pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body))
    ))
  ) {
    have(thesis) by Tautology.from(patterns.map(pattern => shortDefinitionByPattern(pattern))*)
  }

  val intro: THM = Lemma(term :: spec.typ) {

    have(forall(f, (term === f) <=> untypedDef)) by
      Restate.from(classFunctionCharacterization)

    thenHave(
      (term === term) <=>
        (term :: spec.typ) /\
        (seqAnd(patterns.map { pattern =>
          forallSeq(
            pattern.binders,
            pattern.branchPremise ==> (term * pattern.inputTerm === pattern.body)
          )
        }))
    ) by InstantiateForall(term)
    thenHave(term :: spec.typ) by Weakening
    thenHave(thesis) by Restate
  }
}
