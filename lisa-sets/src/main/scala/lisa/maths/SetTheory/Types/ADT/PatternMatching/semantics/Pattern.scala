package lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode.Bind
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode.Construct
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternValidation
import lisa.maths.SetTheory.Types.ADT.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADT.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiatedSemanticSignature
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.syntax.AST.SelfRef
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.Thm

/**
 * A nested argument and the outer binder representing it in proofs.
 */
private[ADT] final case class BranchGuard(position: Int, binder: Variable[Ind], pattern: PatternNode) {

  /**
   * The constructor term represented by the resolved argument.
   */
  def guardTerm: Expr[Ind] = pattern.term
}

/**
 * The body-independent proof view of one resolved constructor pattern.
 */
final class Pattern private (
    private[ADT] val resolved: Construct,
    val topBinders: Seq[Variable[Ind]],
    avoid: Seq[Expr[?]]
) {

  /**
   * The semantic constructor at the root.
   */
  def semanticConstructor: SemanticConstructor = resolved.constructor.semantic

  /**
   * The specialized datatype matched by this pattern.
   */
  def specializedAdtTerm: Expr[Ind] = resolved.typ

  /**
   * The diagnostic name of the outer constructor.
   */
  def name: String = semanticConstructor.name

  /**
   * The number of outer constructor arguments.
   */
  def arity: Int = semanticConstructor.arity

  /**
   * The constructor parameters specialized by the resolved root.
   */
  lazy val typeSubstitutions: Seq[TypeSubstitution] =
    semanticConstructor.typeVariablesSeq.zip(resolved.typeArguments).collect { case (v, arg) if v != arg => v := arg }

  /**
   * Nested arguments paired with their synthetic outer binders.
   */
  private[ADT] val guards: Seq[BranchGuard] = resolved.arguments.zipWithIndex.collect { case (pattern: Construct, i) =>
    BranchGuard(i, topBinders(i), pattern)
  }

  private val innerTyped = guards.flatMap(_.pattern.typingSignature)

  /**
   * User binders below the outer constructor arguments.
   */
  val innerBinders: Seq[Variable[Ind]] = innerTyped.map(_._1)

  /**
   * The specialized types of the nested user binders.
   */
  val innerTypes: Seq[Expr[Ind]] = innerTyped.map(_._2)

  /**
   * Outer argument binders followed by nested user binders.
   */
  val binders: Seq[Variable[Ind]] = topBinders ++ innerBinders

  private val (outerVariables1, outerVariables2) = {
    val forbidden = avoid ++ resolved.typeArguments ++ semanticConstructor.typeVariablesSeq ++
      semanticConstructor.variables1 ++ semanticConstructor.variables2
    val first = semanticConstructor.variables1.foldLeft(Vector.empty[Variable[Ind]]) { (vars, variable) =>
      vars :+ Variable[Ind](freshId(forbidden ++ vars, variable.id.name))
    }
    val second = semanticConstructor.variables2.foldLeft(Vector.empty[Variable[Ind]]) { (vars, variable) =>
      vars :+ Variable[Ind](freshId(forbidden ++ first ++ vars, variable.id.name))
    }
    (first, second)
  }

  private val (innerVariables1, innerVariables2) = {
    val forbidden = avoid ++ resolved.typeArguments ++ Seq(resolved.term, resolved.typ) ++
      binders ++ outerVariables1 ++ outerVariables2
    val first = innerBinders.indices.foldLeft(Vector.empty[Variable[Ind]]) { (vars, i) =>
      vars :+ Variable[Ind](freshId(forbidden ++ vars, s"$name/inner1$i"))
    }
    val second = innerBinders.indices.foldLeft(Vector.empty[Variable[Ind]]) { (vars, i) =>
      vars :+ Variable[Ind](freshId(forbidden ++ first ++ vars, s"$name/inner2$i"))
    }
    (first, second)
  }

  /**
   * The first canonical tuple of outer and inner proof variables.
   */
  val variables1: Seq[Variable[Ind]] = outerVariables1 ++ innerVariables1

  /**
   * The second canonical tuple of outer and inner proof variables.
   */
  val variables2: Seq[Variable[Ind]] = outerVariables2 ++ innerVariables2

  /**
   * The outer constructor applied to the supplied outer argument variables.
   */
  def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    appSeq(semanticConstructor.term(resolved.typeArguments))(vars.take(arity))

  /**
   * The outer constructor term at the collected case binders.
   */
  def inputTerm: Expr[Ind] = inputTermAt(binders)

  /**
   * The outer constructor term at the first canonical tuple.
   */
  def inputTerm1: Expr[Ind] = inputTermAt(variables1)

  /**
   * The outer constructor term at the second canonical tuple.
   */
  def inputTerm2: Expr[Ind] = inputTermAt(variables2)

  /**
   * The input term used by branch theorem consumers.
   */
  def freshInputTerm: Expr[Ind] = inputTerm2

  /**
   * The specialized types of the supplied outer and inner variables.
   */
  def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] =
    val (top, inner) = vars.splitAt(arity)
    instantiatedSemanticSignature(semanticConstructor.semanticSignature(top), typeSubstitutions) ++ inner.zip(innerTypes)

  /**
   * The typing assumptions for the supplied variable tuple.
   */
  def typingPremisesAt(vars: Seq[Variable[Ind]]): Set[Expr[Prop]] = wellTypedSet(typingSignatureAt(vars))

  /**
   * The conjunction of typing assumptions for the supplied tuple.
   */
  def typingFormulaAt(vars: Seq[Variable[Ind]]): Expr[Prop] = wellTypedFormula(typingSignatureAt(vars))

  /**
   * The typing assumptions at the collected case binders.
   */
  def typingPremises: Set[Expr[Prop]] = typingPremisesAt(binders)

  /**
   * The typing conjunction at the collected case binders.
   */
  def typingFormula: Expr[Prop] = typingFormulaAt(binders)

  /**
   * The typing conjunction at the second canonical tuple.
   */
  def freshTypingFormula: Expr[Prop] = typingFormulaAt(variables2)

  /**
   * Renames guard value binders while keeping their type arguments rigid.
   */
  private[ADT] def guardsAt(vars: Seq[Variable[Ind]]): Seq[BranchGuard] =
    val renaming = binders.zip(vars).toMap
    guards.map(guard => BranchGuard(guard.position, vars(guard.position), guard.pattern.renameBinders(renaming)))

  /**
   * The guards at the second canonical tuple.
   */
  private[ADT] lazy val freshGuards: Seq[BranchGuard] = guardsAt(variables2)

  /**
   * The guard conjunction at the supplied variables.
   */
  def branchConditionAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    seqAnd(guardsAt(vars).map(guard => guard.binder === guard.guardTerm))

  /**
   * The guard conjunction at the collected case binders.
   */
  lazy val branchCondition: Expr[Prop] = branchConditionAt(binders)

  /**
   * The guard conjunction at the second canonical tuple.
   */
  lazy val freshBranchCondition: Expr[Prop] = branchConditionAt(variables2)

  /**
   * The typing and guard assumptions at the supplied variables.
   */
  def branchPremiseAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    simplify(typingFormulaAt(vars) /\ branchConditionAt(vars))

  /**
   * The typing and guard assumptions at the collected case binders.
   */
  def branchPremise: Expr[Prop] = branchPremiseAt(binders)

  /**
   * The typing and guard assumptions at the first canonical tuple.
   */
  def branchPremise1: Expr[Prop] = branchPremiseAt(variables1)

  /**
   * The typing and guard assumptions at the second canonical tuple.
   */
  def freshBranchPremise: Expr[Prop] = branchPremiseAt(variables2)

  /**
   * The branch-selection condition before binding the inner witnesses.
   */
  def branchSelectionBody(term: Expr[Ind]): Expr[Prop] =
    val condition = freshBranchCondition /\ (term === freshInputTerm)
    if innerBinders.isEmpty then condition
    else wellTypedFormula(typingSignatureAt(variables2).drop(arity)) /\ condition

  /**
   * The branch-selection condition with all inner witnesses bound.
   */
  def branchSelectionDisjunct(term: Expr[Ind]): Expr[Prop] =
    existsSeq(variables2.drop(arity), branchSelectionBody(term))

  /**
   * Matches a constructor case modulo bijective renaming of its value binders.
   */
  def matchesConstructorCase(constructor: SemanticConstructor, args: Seq[Expr[Ind]]): Boolean =
    if semanticConstructor != constructor || args.size != arity then false
    else
      val renaming = collection.mutable.Map.empty[Variable[Ind], Variable[Ind]]
      val renamedBinders = collection.mutable.Set.empty[Variable[Ind]]
      def matches(pattern: PatternNode, query: PatternNode): Boolean = (pattern, query) match
        case (Bind(from, _), Bind(to, _)) =>
          renaming.get(from) match
            case Some(mapped) => mapped == to
            case None if renamedBinders.add(to) =>
              renaming(from) = to
              true
            case _ => false
        case (Construct(c, types, children), Construct(d, otherTypes, otherChildren)) =>
          c.id == d.id && types == otherTypes && children.size == otherChildren.size &&
          children.zip(otherChildren).forall((p, q) => matches(p, q))
        case _ => false
      val domain = new SpecializedADT(resolved.constructor.adt, resolved.typeArguments)
      PatternValidation.resolveCase(resolved.constructor, args, domain).exists(query => matches(resolved, query))

  /**
   * Instantiates typing of the outer constructor application at the supplied arguments.
   */
  def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind])(using proof: lisa.SetTheoryLibrary.ProofBuilder): Thm =
    require(adtTerm == specializedAdtTerm, "Pattern.inputTypingAt expects the compiled specialized datatype.")
    PatternProofs.inputTyping(this, vars.take(arity))

  /**
   * Proves injectivity of all outer and inner pattern binders under the branch premises.
   */
  lazy val injectivity: Theorem =
    if innerBinders.isEmpty then PatternProofs.constructorInjectivity(this)
    else PatternProofs.injectivityCaseShape(this)

  private val recursivePaths: Map[Variable[Ind], List[Int]] =
    def collect(node: PatternNode, path: List[Int]): Seq[(Variable[Ind], List[Int])] = node match
      case Bind(v, _) => if path.length >= 2 then Seq(v -> path) else Seq.empty
      case Construct(c, _, children) =>
        children.zip(c.semantic.syntacticSignature).zipWithIndex.flatMap {
          case ((child, (_, SelfRef)), index) => collect(child, path :+ index)
          case _ => Seq.empty
        }
    val freshening = binders.zip(variables2).toMap
    collect(resolved, Nil).map((v, path) => freshening(v) -> path).toMap

  /**
   * Nested binders reached only through recursive constructor fields.
   */
  def recursiveAgreementPoints(recursiveType: Expr[Ind]): Seq[Variable[Ind]] =
    if recursiveType == specializedAdtTerm then variables2.drop(arity).filter(recursivePaths.contains)
    else Seq.empty

  /**
   * Proves a nested recursive binder lies below the current height using its recorded field path.
   */
  def recursiveAgreementPointInHeight(using
      proof: lisa.SetTheoryLibrary.ProofBuilder,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      target: Variable[Ind],
      recursiveType: Expr[Ind],
      heightFun: Expr[Ind],
      hValid: Thm,
      currentIndex: Expr[Ind],
      currentIndexInN: Thm,
      argsTypedAtHeight: Thm,
      leafTyping: Thm,
      patternGuard: Thm
  ): Thm =
    require(recursiveAgreementPoints(recursiveType).contains(target), s"Pattern $name does not expose $target as a recursive agreement point.")
    val path = recursivePaths(target)
    val guard = freshGuards.find(_.position == path.head).get
    val binderInHeight = have(guard.binder ∈ app(heightFun)(currentIndex)) by Tautology.from(argsTypedAtHeight)
    val guardEq = have(guard.binder === guard.guardTerm) by Tautology.from(patternGuard)
    val guardInHeight = have(guard.guardTerm ∈ app(heightFun)(currentIndex)) by Congruence.from(binderInHeight, guardEq)
    PatternProofs.descendToBinder(
      heightFun,
      hValid,
      currentIndex,
      currentIndexInN,
      leafTyping,
      guard.pattern,
      path.tail,
      guardInHeight,
      target
    )
}

/**
 * Constructs the proof view after the pattern has been resolved and validated.
 */
object Pattern {

  /**
   * Builds outer proof binders fresh against the declaration and its ambient context.
   */
  private[ADT] def fromResolved(root: Construct, avoid: Seq[Expr[?]] = Seq.empty): Pattern =
    val forbidden = avoid ++ Seq(root.term, root.typ) ++ root.typeArguments ++ root.binders
    val top = root.arguments.zipWithIndex.foldLeft(Vector.empty[Variable[Ind]]) {
      case (vars, (Bind(v, _), _)) => vars :+ v
      case (vars, (_, i)) =>
        vars :+ Variable[Ind](freshId(forbidden ++ vars, root.constructor.semantic.name + s"/arg$i"))
    }
    new Pattern(root, top, avoid)
}
