package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.{simplify, wellTypedFormula, wellTypedSet}
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Semantic template for one compiled branch of a pattern-matching definition.
 *
 * Current ADTv2 consumers still use raw constructor-indexed maps. This trait defines the
 * shape of the richer semantic layer we want to migrate to next.
 */
trait Pattern[N <: Arity] {

  def binders: Seq[Variable[Ind]]

  def body: Expr[Ind]

  protected def constructor: SemanticConstructor[N]

  def semanticConstructor: SemanticConstructor[N] = constructor

  def name: String = constructor.name

  def correspondsTo(candidate: SemanticConstructor[N]): Boolean =
    constructor == candidate

  def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] = constructor.appliedTerm(vars)

  def inputTerm: Expr[Ind] = constructor.appliedTerm(binders)

  def typingPremises: Set[Expr[Prop]] = wellTypedSet(constructor.semanticSignature(binders))

  def typingFormula: Expr[Prop] = wellTypedFormula(constructor.semanticSignature(binders))

  def branchCondition: Expr[Prop] = ⊤

  def branchPremise: Expr[Prop] = simplify(typingFormula /\ branchCondition)

  def variables2: Seq[Variable[Ind]] = constructor.variables2

  def freshInputTerm: Expr[Ind] = constructor.appliedTerm2

  def freshTypingFormula: Expr[Prop] = wellTypedFormula(constructor.semanticSignature2)

  def branchConditionAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    branchCondition.substitute(binders.zip(vars).map((from, to) => from := to)*).asInstanceOf[Expr[Prop]]

  def freshBranchCondition: Expr[Prop] = branchConditionAt(variables2)

  def freshBranchPremise: Expr[Prop] = simplify(freshTypingFormula /\ freshBranchCondition)

  def bodySubstituted(subst: Seq[(Variable[Ind], Expr[Ind])]): Expr[Ind] =
    body.substitute(subst.map((from, to) => from := to)*).asInstanceOf[Expr[Ind]]

  def bodyAtFreshVars2: Expr[Ind] = bodySubstituted(binders.zip(variables2))

  def withBody(newBody: Expr[Ind]): Pattern[N]
}

final case class ConstructorPattern[N <: Arity](
    protected val constructor: SemanticConstructor[N],
    binders: Seq[Variable[Ind]],
    body: Expr[Ind],
    override val branchCondition: Expr[Prop] = ⊤
) extends Pattern[N] {
  override def withBody(newBody: Expr[Ind]): Pattern[N] = copy(body = newBody)
}
