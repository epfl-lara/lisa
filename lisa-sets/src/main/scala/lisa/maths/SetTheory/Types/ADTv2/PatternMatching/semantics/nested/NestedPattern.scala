package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.nested

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.{nonZeroOmegaHasPredecessor, subsetSuccessor}
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{ConstructorHeadPattern, Pattern}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedSemanticSignature
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * A constructor-headed pattern where some arguments are compiled into branch
 * guards instead of being kept as user binders.
 *
 * For example, `cons(tru, tl)` is represented with binders `(_cons0, tl)` and
 * branch condition `_cons0 === tru`.
 */
private[PatternMatching] final case class ResolvedNullaryGuard(
    constructor: Constructor[?],
    appliedTerm: Expr[Ind]
)

private[PatternMatching] final case class BranchGuard(
    position: Int,
    binder: Variable[Ind],
    guardTerm: Expr[Ind],
    resolvedNullary: Option[ResolvedNullaryGuard]
)

private[PatternMatching] final case class NestedConstructorPattern[N <: Arity](
    semanticConstructor: SemanticConstructor[N],
    topBinders: Seq[Variable[Ind]],
    innerBinders: Seq[Variable[Ind]],
    innerTypes: Seq[Expr[Ind]],
    body: Expr[Ind],
    override val branchCondition: Expr[Prop],
    guards: Seq[BranchGuard],
    override val typeSubstitutions: Seq[TypeSubstitution] = Seq.empty,
    override val specializedAdtTerm: Expr[Ind]
) extends ConstructorHeadPattern[N] {

  // All existentially-bound variables: the top constructor-argument binders plus
  // the free variables appearing inside (possibly non-nullary) guard terms.
  // For nullary / ground guards `innerBinders` is empty, so this reduces to the
  // previous behaviour and the four overrides below are no-ops.
  override def binders: Seq[Variable[Ind]] = topBinders ++ innerBinders

  private val innerVariables1: Seq[Variable[Ind]] =
    innerBinders.indices.map(i => variable[Ind](s"${semanticConstructor.name}/inner1$i"))
  private val innerVariables2: Seq[Variable[Ind]] =
    innerBinders.indices.map(i => variable[Ind](s"${semanticConstructor.name}/inner2$i"))

  override def variables1: Seq[Variable[Ind]] = semanticConstructor.variables1 ++ innerVariables1
  override def variables2: Seq[Variable[Ind]] = semanticConstructor.variables2 ++ innerVariables2

  // The input term consumes only the top (constructor-argument) binders; inner
  // binders live inside the guard terms and the branch condition.
  override def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    specializeTerm(semanticConstructor.appliedTerm(vars.take(arity)), typeSubstitutions)

  override def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] =
    val (top, inner) = vars.splitAt(arity)
    instantiatedSemanticSignature(semanticConstructor.semanticSignature(top), typeSubstitutions) ++
      inner.zip(innerTypes)

  // The constructor-application typing concerns only the top arguments.
  override def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind]): THM =
    super.inputTypingAt(vars.take(arity), adtTerm)

  // With inner binders, well-definedness needs the *pattern* injectivity (input
  // equal ⇔ all binders equal, under the branch premises); without, the plain
  // constructor injectivity (super) is exactly right.
  override def injectivity: THM =
    if innerBinders.isEmpty then super.injectivity
    else NestedTrieProofs.injectivityCaseShape(this)

  def guardsAt(vars: Seq[Variable[Ind]]): Seq[BranchGuard] = {
    val subst = binders.zip(vars).map((from, to) => from := to)
    guards.map(guard =>
      guard.copy(
        binder = vars(binders.indexOf(guard.binder)),
        guardTerm = guard.guardTerm.substitute(subst*).asInstanceOf[Expr[Ind]]
      )
    )
  }

  def freshGuards: Seq[BranchGuard] = guardsAt(variables2)

  override def guardSignature: Set[(Int, Expr[Ind])] =
    guards.map(g => (g.position, g.guardTerm)).toSet

  override def recursiveAgreementPointInHeight(using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      target: Variable[Ind],
      recursiveType: Expr[Ind],
      heightFun: Expr[Ind],
      hValid: proof.Fact,
      heightMembershipMonotonic: THM,
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact,
      argsTypedAtHeight: proof.Fact,
      leafTyping: proof.Fact,
      patternGuard: proof.Fact
  ): proof.Fact = {
    require(
      recursiveAgreementPoints(recursiveType).contains(target),
      s"Pattern ${name} does not expose $target as a recursive agreement point."
    )
    val guard = freshGuards
      .find { g =>
        val guardType = semanticConstructor
          .semanticSignature2(g.position)
          ._2
          .substitute(typeSubstitutions*)
          .asInstanceOf[Expr[Ind]]
        NestedTrieProofs.guardBinders(g.guardTerm, guardType).exists(_._1 == target)
      }
      .getOrElse(
        throw new IllegalArgumentException(s"No guard contains recursive agreement point $target in pattern ${name}.")
      )

    val guardType = semanticConstructor
      .semanticSignature2(guard.position)
      ._2
      .substitute(typeSubstitutions*)
      .asInstanceOf[Expr[Ind]]
    val guardTy = ADT.unapply(guardType).get
    val binderInHeight = have(guard.binder ∈ app(heightFun)(currentIndex)) by Tautology.from(argsTypedAtHeight)
    val guardEq = have(guard.binder === guard.guardTerm) by Tautology.from(patternGuard)
    val guardInHeight = have(guard.guardTerm ∈ app(heightFun)(currentIndex)) by Congruence.from(binderInHeight, guardEq)

    Time.measure(s"RecArg/descendToBinder") {
      NestedConstructorPattern.descendToBinder(
        heightFun = heightFun,
        hValid = hValid,
        heightMembershipMonotonic = heightMembershipMonotonic,
        currentIndex = currentIndex,
        currentIndexInN = currentIndexInN,
        leafTyping = leafTyping,
        currentPat = NestedTrieProofs.parse(guard.guardTerm),
        currentTy = guardTy,
        currentInHeight = guardInHeight,
        target = target
      )
    }
  }

  override def withBody(newBody: Expr[Ind]): Pattern[N] = copy(body = newBody)
}

private[PatternMatching] object NestedConstructorPattern {
  import NestedTrieProofs.{RPat, Ty}
  import NestedTrieProofs.RPat.{RCon, RVar}

  private def resolveNullaryGuard(term: Expr[Ind]): Option[ResolvedNullaryGuard] =
    val allConstructors = ADT.allADTs.toSeq.flatMap(_.constructors)
    allConstructors.collectFirst {
      case constructor if constructor.semantic.arity == 0 && hasConstructorHead(term, constructor.id) =>
        ResolvedNullaryGuard(constructor, term)
    }

  private def hasConstructorHead(term: Expr[Ind], constructorId: Identifier): Boolean =
    term match
      case constant: Constant[?] @unchecked => constant.id == constructorId
      case Multiapp(head, _) =>
        head match
          case constant: Constant[?] @unchecked => constant.id == constructorId
          case _ => false
      case null => false

  /**
   * Builds a nested pattern from a mixed argument list.
   *
   * `Left(v)` keeps `v` as a binder.
   * `Right(t)` introduces a fresh binder and adds an equality guard against `t`.
   */
  def fromArgs[N <: Arity](
      constructor: SemanticConstructor[N],
      args: Seq[Either[Variable[Ind], Expr[Ind]]],
      body: Expr[Ind],
      typeSubstitutions: Seq[TypeSubstitution] = Seq.empty,
      specializedAdtTerm: Expr[Ind]
  ): NestedConstructorPattern[N] =
    val topBinders: Seq[Variable[Ind]] = args.zipWithIndex.map {
      case (Left(v), _) => v
      case (Right(_), i) => variable[Ind](s"${constructor.name}/arg$i")
    }
    val guards: Seq[BranchGuard] = args.zipWithIndex.collect { case (Right(term), i) =>
      BranchGuard(
        position = i,
        binder = topBinders(i),
        guardTerm = term,
        resolvedNullary = resolveNullaryGuard(term)
      )
    }
    val conditions: Seq[Expr[Prop]] = args.zip(topBinders).collect { case (Right(term), binder) =>
      binder === term
    }
    val condition = conditions match
      case Nil => ⊤
      case head +: tail => tail.foldLeft(head)(_ /\ _)
    // Free variables inside (possibly non-nullary) guard terms become binders too,
    // typed from the guarded argument position. Empty for nullary / ground guards.
    val innerTyped: Seq[(Variable[Ind], Expr[Ind])] = guards
      .flatMap { g =>
        val argType = constructor
          .semanticSignature2(g.position)
          ._2
          .substitute(typeSubstitutions*)
          .asInstanceOf[Expr[Ind]]
        NestedTrieProofs.guardBinders(g.guardTerm, argType)
      }
      .distinctBy(_._1)
    NestedConstructorPattern(
      constructor,
      topBinders,
      innerTyped.map(_._1),
      innerTyped.map(_._2),
      body,
      condition,
      guards,
      typeSubstitutions,
      specializedAdtTerm
    )

  private def containsBinder(p: RPat, target: Variable[Ind]): Boolean = p match
    case RVar(v) => v == target
    case RCon(_, args) => args.exists(containsBinder(_, target))

  private def childIndexForBinder(args: List[RPat], target: Variable[Ind]): Int =
    args.indexWhere(containsBinder(_, target)) match
      case -1 => throw new IllegalArgumentException(s"Binder $target not found in recursive guard.")
      case i => i

  private def typeProof(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      leafTyping: proof.Fact,
      p: RPat,
      ty: Ty
  ): proof.Fact =
    val goal = NestedTrieProofs.termOf(p, ty) :: ty._1.termAt(ty._2)
    p match
      case RVar(_) => have(goal) by Tautology.from(leafTyping)
      case RCon(c, args) =>
        val cts = NestedTrieProofs.resolvedChildTypes(c, ty._2)
        val argFacts = args.zip(cts).map((a, t) => typeProof(leafTyping, a, t.get))
        val intro = if ty._2.isEmpty then c.introApp else c.introApp(ty._2.head, ty._2.tail*)
        val argTerms = args.zip(cts).map((a, t) => NestedTrieProofs.termOf(a, t.get))
        val substs = c.semantic.variables.zip(argTerms).map((v, t) => v := t)
        val introInst: proof.Fact = if substs.isEmpty then intro else intro.of(substs*)
        have(goal) by Tautology.from((introInst +: argFacts)*)

  private def descendToBinder(using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      heightFun: Expr[Ind],
      hValid: proof.Fact,
      heightMembershipMonotonic: THM,
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact,
      leafTyping: proof.Fact,
      currentPat: RPat,
      currentTy: Ty,
      currentInHeight: proof.Fact,
      target: Variable[Ind]
  ): proof.Fact =
    currentPat match
      case RVar(v) =>
        if v != target then throw new IllegalArgumentException(s"Asked to descend to $target but reached unrelated binder $v.")
        currentInHeight

      case RCon(c, args) =>
        val predVar = Variable[Ind](freshId(Seq(currentIndex, target, heightFun), "predVar"))
        val currentTerm = NestedTrieProofs.termOf(currentPat, currentTy)
        val levelSubsts = currentTy._1.semantic.typeVariablesSeq.zip(currentTy._2).map((v, a) => v := a)
        val currentInZero = Time.measure(s"currentInZero") {
          have(!(currentTerm ∈ app(heightFun)(∅))) by Tautology.from(
            hValid,
            currentTy._1.semantic.height.zeroAt(levelSubsts).of(h := heightFun, x := currentTerm)
          )
        }

        val currentIndexNonZero = have(currentIndex =/= ∅) subproof {
          val currentIsZero = assume(currentIndex === ∅)
          have(thesis) by Congruence.from(currentInHeight, currentInZero, currentIsZero)
        }

        val predecessorTheoremAtIndex = have(
          (currentIndex ∈ N, currentIndex =/= ∅) |- ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar)))
        ) by Tautology.from(
          nonZeroOmegaHasPredecessor.of(α := currentIndex, β := predVar)
        )
        have(currentIndex =/= ∅ |- ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar)))) subproof {
          assume(currentIndex =/= ∅)
          have(thesis) by Tautology.from(currentIndexInN, predecessorTheoremAtIndex)
        }
        val predWitnessAtIndex = have(∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar)))) by Cut(
          currentIndexNonZero,
          lastStep
        )

        have(
          (predVar ∈ N /\ (currentIndex === S(predVar))) |- target ∈ app(heightFun)(currentIndex)
        ) subproof {
          assume(predVar ∈ N /\ (currentIndex === S(predVar)))
          val currentEqSucc = have(currentIndex === S(predVar)) by Tautology
          val predInN = have(predVar ∈ N) by Tautology

          val currentInSuccPred = have(currentTerm ∈ app(heightFun)(S(predVar))) by Congruence.from(
            currentInHeight,
            currentEqSucc
          )

          val cts = NestedTrieProofs.resolvedChildTypes(c, currentTy._2)
          val argTerms: Seq[Expr[Ind]] = args.zip(cts).map((a, t) => NestedTrieProofs.termOf(a, t.get))
          val argTypings = args.zip(cts).map((a, t) => typeProof(leafTyping, a, t.get))
          val semanticSubsts = c.semantic.typeVariablesSeq.zip(currentTy._2).map((v, a) => v := a)
          val semanticSigAtArgs =
            argTerms.zip(c.semantic.semanticSignature2.map(_._2.substitute(semanticSubsts*).asInstanceOf[Expr[Ind]]))
          val argsTypedSemantic = Time.measure(s"argsTypedSemantic") { have(wellTypedFormula(semanticSigAtArgs)) by Tautology.from(argTypings*) }
          val heightSigAtArgs = argTerms.zip(c.semantic.syntacticSignature).map {
            case (term, (_, SelfRef)) => term -> app(heightFun)(predVar)
            case (term, (_, TypeArg(name))) => term -> typeExprToTerm(name).substitute(semanticSubsts*).asInstanceOf[Expr[Ind]]
          }
          val recursiveAtPred = c.semantic.recursiveArgInHeightAt(semanticSubsts)(heightFun, predVar)
          val valueSubsts = c.semantic.variables2.zip(argTerms).map((v, t) => v := t)
          val childTypingsAtPred = Time.measure(s"childTypingsAtPred") {
            have(wellTypedFormula(heightSigAtArgs)) by Tautology.from(
              hValid,
              predInN,
              argsTypedSemantic,
              currentInSuccPred,
              recursiveAtPred.of(valueSubsts*)
            )
          }

          val childIdx = childIndexForBinder(args, target)
          val childTy = cts(childIdx).get
          val childTerm = argTerms(childIdx)
          val childInPred = have(childTerm ∈ app(heightFun)(predVar)) by Tautology.from(childTypingsAtPred)
          val innerAtPred = descendToBinder(
            heightFun = heightFun,
            hValid = hValid,
            heightMembershipMonotonic = heightMembershipMonotonic,
            currentIndex = predVar,
            currentIndexInN = predInN,
            leafTyping = leafTyping,
            currentPat = args(childIdx),
            currentTy = childTy,
            currentInHeight = childInPred,
            target = target
          )

          val predSubSucc = have(predVar ⊆ S(predVar)) by Tautology.from(subsetSuccessor.of(n := predVar))
          val predSubCurrent = have(predVar ⊆ currentIndex) by Congruence.from(predSubSucc, currentEqSucc)
          Time.measure(s"targetInHeight") {
            have(target ∈ app(heightFun)(currentIndex)) by Tautology.from(
              hValid,
              currentIndexInN,
              predInN,
              predSubCurrent,
              innerAtPred,
              heightMembershipMonotonic.of(h := heightFun, n := currentIndex, m := predVar, x := target)
            )
          }
        }
        val fromPredWitness = thenHave(
          ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar))) |- target ∈ app(heightFun)(currentIndex)
        ) by LeftExists
        have(target ∈ app(heightFun)(currentIndex)) by Cut(predWitnessAtIndex, fromPredWitness)
}
