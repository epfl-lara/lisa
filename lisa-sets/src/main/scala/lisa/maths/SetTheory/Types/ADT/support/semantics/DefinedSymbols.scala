package lisa.maths.SetTheory.Types.ADT.support.semantics

import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.maths.Quantifiers.existsOneEpsilon
import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.utils.prooflib.BasicStep.RightForall
import lisa.utils.prooflib.Thm

/**
 * Defines a symbol by abstracting its body over the supplied parameters.
 */
class DefinedSymbol[S](
    protected val name: String,
    protected val parametersSeq: Seq[Variable[Ind]],
    protected val body: Expr[S]
) {

  protected val classFunction: Constant[?] = {
    val classFunctionExpr: Expr[?] = lisa.utils.fol.FOL.Abs.apply(
      xs = parametersSeq,
      t = body
    )
    type T
    given T is lisa.utils.fol.FOL.Sort =
      lisa.utils.fol.FOL.unsafeSortEvidence(classFunctionExpr.sort)
    DEF(using name = name)(classFunctionExpr.asInstanceOf[Expr[T]])
  }
  classFunction.printAs(args => renderAppliedSymbol(name, parametersSeq.size, args))

  val symbol: Constant[?] = classFunction
  val definition: Thm = classFunction.definition
  val id: Identifier = classFunction.id

  /**
   * Instantiates every declared parameter, preserving the body's result sort.
   */
  def term(args: Seq[Expr[Ind]]): Expr[S] =
    require(args.size == parametersSeq.size, s"Symbol $name expects ${parametersSeq.size} parameter argument(s), got ${args.size}.")
    (classFunction #@@ args).asInstanceOf[Expr[S]]

  val term: Expr[S] = term(parametersSeq)

}

/**
 * Defines a parameterized predicate with folding and unfolding proofs at arbitrary arguments.
 */
class DefinedProperty(
    name: String,
    typeVariablesSeq: Seq[Variable[Ind]],
    bodyVar: Variable[Ind],
    bodyAt: Expr[Ind] => Expr[Prop]
) extends DefinedSymbol[Ind >>: Prop](name, typeVariablesSeq, λ(bodyVar, bodyAt(bodyVar))) {

  private val (appliedPredicate, definingFormula) = definition.statement.right.head match
    case lhs <=> rhs => (lhs, rhs)
    case other => throw IllegalStateException(s"$name.definition is expected to be an `<=>`, got: $other")

  /**
   * Derives the defining formula from the applied predicate.
   */
  lazy val unfold: Theorem = Lemma.generated(appliedPredicate |- definingFormula) { have(thesis) by Tautology.from(definition) }

  /**
   * Derives the applied predicate from its defining formula.
   */
  lazy val fold: Theorem = Lemma.generated(definingFormula |- appliedPredicate) { have(thesis) by Tautology.from(definition) }

  /**
   * Instantiates the unfolding direction in the current proof.
   */
  def unfoldAt(arg: Expr[Ind])(using proof: lisa.SetTheoryLibrary.ProofBuilder): Thm =
    if arg == bodyVar then unfold else unfold.of(bodyVar := arg)

  /**
   * Instantiates the folding direction in the current proof.
   */
  def foldAt(arg: Expr[Ind])(using proof: lisa.SetTheoryLibrary.ProofBuilder): Thm =
    if arg == bodyVar then fold else fold.of(bodyVar := arg)

}

/**
 * Defines an epsilon-selected symbol and proves its defining predicate from unique existence.
 */
class UniqueDefinedSymbol(
    name: String,
    typeVariablesSeq: Seq[Variable[Ind]],
    witnessVar: Variable[Ind],
    definitionAt: Expr[Ind] => Expr[Prop]
)(
    uniqueness: Theorem
) extends DefinedSymbol[Ind](name, typeVariablesSeq, ε(witnessVar, definitionAt(witnessVar))) {

  private val witnessDefinition: Expr[Prop] = definitionAt(witnessVar)

  private val classTermIsEpsilon: Theorem = Lemma.generated(term === ε(witnessVar, witnessDefinition)) {
    have(thesis) by Congruence.from(definition)
  }

  /**
   * The selected term satisfies its defining predicate.
   */
  val definitionFact: Theorem = Lemma.generated(definitionAt(term)) {
    val epsilonWitness = ε(witnessVar, witnessDefinition)

    val definitionAtEpsilon = have(definitionAt(epsilonWitness)) by Tautology.from(
      uniqueness,
      existsOneEpsilon of (x := witnessVar, P := λ(witnessVar, witnessDefinition))
    )
    val epsilonEqTerm = have(epsilonWitness === term) by Congruence.from(classTermIsEpsilon)

    val definitionAtEpsilonWithEq =
      have((epsilonWitness === term) |- definitionAt(epsilonWitness)) by
        Weakening(definitionAtEpsilon)

    val replacementVar = Variable[Ind](freshId(Seq(witnessDefinition, epsilonWitness, term) ++ typeVariablesSeq, "replacementVar"))
    val definitionAtTerm =
      have((epsilonWitness === term) |- definitionAt(term)) by
        RightSubst(
          List((epsilonWitness, term)),
          (Seq(replacementVar), definitionAt(replacementVar))
        )(definitionAtEpsilonWithEq)

    have(thesis) by Tautology.from(epsilonEqTerm, definitionAtTerm)
  }
}

/**
 * Builds epsilon-selected symbols from their existence and uniqueness proofs.
 */
object UniqueDefinedSymbol {

  /**
   * Defines a unique witness from separate existence and pointwise-uniqueness proofs.
   */
  def fromParts(
      name: String,
      typeVariablesSeq: Seq[Variable[Ind]],
      witnessVar: Variable[Ind],
      comparisonVariables: (Variable[Ind], Variable[Ind]),
      definitionAt: Expr[Ind] => Expr[Prop]
  )(
      existence: Theorem,
      pointwiseUniqueness: Theorem
  ): UniqueDefinedSymbol = {
    val (left, right) = comparisonVariables
    new UniqueDefinedSymbol(name, typeVariablesSeq, witnessVar, definitionAt)(
      Lemma.generated(∃!(witnessVar, definitionAt(witnessVar))) {
        have(∀(right, definitionAt(left) /\ definitionAt(right) ==> (left === right))) by
          RightForall(pointwiseUniqueness)
        val uniquenessAll = thenHave(
          ∀(left, ∀(right, definitionAt(left) /\ definitionAt(right) ==> (left === right)))
        ) by RightForall

        val altDef = existsOneAlternativeDefinition of (x := witnessVar, P := λ(witnessVar, definitionAt(witnessVar)))

        have(
          ∃(witnessVar, definitionAt(witnessVar)) /\ ∀(left, ∀(right, definitionAt(left) /\ definitionAt(right) ==> (left === right)))
        ) by RightAnd(existence, uniquenessAll)
        thenHave(thesis) by Substitute(altDef)
      }
    )
  }
}
