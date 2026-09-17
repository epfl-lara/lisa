package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Semantic template for one compiled branch of a pattern-matching definition.
 *
 * This trait only contains branch-level operations shared by every current
 * pattern family.
 */
trait Pattern[N <: Arity] {

  def binders: Seq[Variable[Ind]]

  def body: Expr[Ind]

  def name: String

  def arity: Int

  def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind]

  def inputTerm: Expr[Ind] = inputTermAt(binders)

  def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])]

  def typingPremisesAt(vars: Seq[Variable[Ind]]): Set[Expr[Prop]] =
    wellTypedSet(typingSignatureAt(vars))

  def typingFormulaAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    wellTypedFormula(typingSignatureAt(vars))

  def typingPremises: Set[Expr[Prop]] = typingPremisesAt(binders)

  def typingFormula: Expr[Prop] = typingFormulaAt(binders)

  def branchCondition: Expr[Prop] = ⊤

  def branchPremise: Expr[Prop] = simplify(typingFormula /\ branchCondition)

  /**
   * Concrete (guard) arguments of this branch, as `(position -> term)`.
   *
   * Plain patterns guard on nothing, so the default is empty.
   */
  def guardSignature: Set[(Int, Expr[Ind])] = Set.empty

  /**
   * Whether this branch is the one for `constructor` applied to `args`, treating
   * non-variable args as guards. Order- and binder-name-independent.
   *
   * The default never matches; constructor-headed patterns override it.
   */
  def matchesConstructorCase(constructor: SemanticConstructor[N], args: Seq[Expr[Ind]]): Boolean = false

  def variables2: Seq[Variable[Ind]]

  def freshInputTerm: Expr[Ind] = inputTermAt(variables2)

  def freshTypingFormula: Expr[Prop] = typingFormulaAt(variables2)

  def branchConditionAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    branchCondition.substitute(binders.zip(vars).map((from, to) => from := to)*).asInstanceOf[Expr[Prop]]

  def freshBranchCondition: Expr[Prop] = branchConditionAt(variables2)

  def branchPremiseAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    simplify(typingFormulaAt(vars) /\ branchConditionAt(vars))

  def freshBranchPremise: Expr[Prop] = simplify(freshTypingFormula /\ freshBranchCondition)

  def bodySubstituted(subst: Seq[(Variable[Ind], Expr[Ind])]): Expr[Ind] =
    body.substitute(subst.map((from, to) => from := to)*).asInstanceOf[Expr[Ind]]

  def bodyAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    bodySubstituted(binders.zip(vars))

  def bodyAtFreshVars2: Expr[Ind] = bodyAt(variables2)

  def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind]): THM

  def withBody(newBody: Expr[Ind]): Pattern[N]

  def recursiveAgreementPoints(recursiveType: Expr[Ind]): Seq[Variable[Ind]] =
    typingSignatureAt(variables2).drop(arity).collect {
      case (v, ty) if ty == recursiveType => v
    }

  def recursiveAgreementPointInHeight(using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      target: Variable[Ind],
      recursiveType: Expr[Ind],
      heightFun: Expr[Ind],
      @scala.annotation.unused hValid: proof.Fact,
      @scala.annotation.unused heightMembershipMonotonic: THM,
      currentIndex: Expr[Ind],
      @scala.annotation.unused currentIndexInN: proof.Fact,
      argsTypedAtHeight: proof.Fact,
      @scala.annotation.unused leafTyping: proof.Fact,
      @scala.annotation.unused patternGuard: proof.Fact
  ): proof.Fact = {
    require(
      recursiveAgreementPoints(recursiveType).contains(target),
      s"Pattern $name does not expose $target as a recursive agreement point."
    )
    have(target ∈ app(heightFun)(currentIndex)) by Tautology.from(argsTypedAtHeight)
  }

  // Selection disjunct used by `branchSelectionFor` and its consumers. The inner
  // (non-constructor-argument) binders are existentially bound and carry their
  // typing; for plain/nullary patterns there are no inner binders, so this reduces
  // to `freshBranchCondition ∧ (term = freshInputTerm)`.
  def branchSelectionBody(term: Expr[Ind]): Expr[Prop] =
    val inner = variables2.drop(arity)
    val cond = freshBranchCondition /\ (term === freshInputTerm)
    if inner.isEmpty then cond
    else wellTypedFormula(typingSignatureAt(variables2).drop(arity)) /\ cond

  def branchSelectionDisjunct(term: Expr[Ind]): Expr[Prop] =
    existsSeq(variables2.drop(arity), branchSelectionBody(term))
}