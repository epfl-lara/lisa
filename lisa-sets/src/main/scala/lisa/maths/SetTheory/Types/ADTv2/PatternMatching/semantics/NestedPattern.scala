package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedSemanticSignature
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ExtendedInteger.subsetSuccessor
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.altEqualityTransitivity
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.LeftOr
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

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
    val guard = freshGuards.find { g =>
      val guardType = semanticConstructor.semanticSignature2(g.position)._2
        .substitute(typeSubstitutions*).asInstanceOf[Expr[Ind]]
      NestedTrieProofs.guardBinders(g.guardTerm, guardType).exists(_._1 == target)
    }.getOrElse(
      throw new IllegalArgumentException(s"No guard contains recursive agreement point $target in pattern ${name}.")
    )

    val guardType = semanticConstructor.semanticSignature2(guard.position)._2
      .substitute(typeSubstitutions*).asInstanceOf[Expr[Ind]]
    val guardTy = ADT.unapply(guardType).get
    val binderInHeight = have(guard.binder ∈ app(heightFun)(currentIndex)) by Tautology.from(argsTypedAtHeight)
    val guardEq = have(guard.binder === guard.guardTerm) by Tautology.from(patternGuard)
    val guardInHeight = have(guard.guardTerm ∈ app(heightFun)(currentIndex)) by Congruence.from(binderInHeight, guardEq)

    Time.measure(s"RecArg/descendToBinder") {NestedConstructorPattern.descendToBinder(
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
    )}
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
          case _                                => false
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
      case (Left(v), _)  => v
      case (Right(_), i) => variable[Ind](s"${constructor.name}/arg$i")
    }
    val guards: Seq[BranchGuard] = args.zipWithIndex.collect {
      case (Right(term), i) =>
        BranchGuard(
          position = i,
          binder = topBinders(i),
          guardTerm = term,
          resolvedNullary = resolveNullaryGuard(term)
        )
    }
    val conditions: Seq[Expr[Prop]] = args.zip(topBinders).collect {
      case (Right(term), binder) => binder === term
    }
    val condition = conditions match
      case Nil          => ⊤
      case head +: tail => tail.foldLeft(head)(_ /\ _)
    // Free variables inside (possibly non-nullary) guard terms become binders too,
    // typed from the guarded argument position. Empty for nullary / ground guards.
    val innerTyped: Seq[(Variable[Ind], Expr[Ind])] = guards.flatMap { g =>
      val argType = constructor.semanticSignature2(g.position)._2
        .substitute(typeSubstitutions*).asInstanceOf[Expr[Ind]]
      NestedTrieProofs.guardBinders(g.guardTerm, argType)
    }.distinctBy(_._1)
    NestedConstructorPattern(
      constructor, topBinders, innerTyped.map(_._1), innerTyped.map(_._2),
      body, condition, guards, typeSubstitutions, specializedAdtTerm
    )

  private def containsBinder(p: RPat, target: Variable[Ind]): Boolean = p match
    case RVar(v)       => v == target
    case RCon(_, args) => args.exists(containsBinder(_, target))

  private def childIndexForBinder(args: List[RPat], target: Variable[Ind]): Int =
    args.indexWhere(containsBinder(_, target)) match
      case -1 => throw new IllegalArgumentException(s"Binder $target not found in recursive guard.")
      case i  => i

  private def typeProof(using proof: lisa.SetTheoryLibrary.Proof)(
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

  private def descendToBinder(using proof: lisa.SetTheoryLibrary.Proof, line: sourcecode.Line, file: sourcecode.File)(
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
        if v != target then
          throw new IllegalArgumentException(s"Asked to descend to $target but reached unrelated binder $v.")
        currentInHeight

      case RCon(c, args) =>
        val predVar = Variable[Ind](freshId(Seq(currentIndex, target, heightFun), "predVar"))
        val currentTerm = NestedTrieProofs.termOf(currentPat, currentTy)
        val levelSubsts = currentTy._1.semantic.typeVariablesSeq.zip(currentTy._2).map((v, a) => v := a)
        val currentInZero = Time.measure(s"currentInZero"){have(!(currentTerm ∈ app(heightFun)(∅))) by Tautology.from(
          hValid,
          currentTy._1.semantic.height.zeroAt(levelSubsts).of(h := heightFun, x := currentTerm)
        )}

        val currentIndexNonZero = have(currentIndex =/= ∅) subproof {
          val currentIsZero = assume(currentIndex === ∅)
          have(thesis) by Congruence.from(currentInHeight, currentInZero, currentIsZero)
        }

        val predecessorTheoremAtIndex = have(
          (currentIndex ∈ N, currentIndex =/= ∅) |- ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar)))
        ) by Tautology.from(
          ExtendedInteger.nonZeroOmegaHasPredecessor.of(α := currentIndex, β := predVar)
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
          val argTerms = args.zip(cts).map((a, t) => NestedTrieProofs.termOf(a, t.get))
          val argTypings = args.zip(cts).map((a, t) => typeProof(leafTyping, a, t.get))
          val semanticSubsts = c.semantic.typeVariablesSeq.zip(currentTy._2).map((v, a) => v := a)
          val semanticSigAtArgs =
            argTerms.zip(c.semantic.semanticSignature2.map(_._2.substitute(semanticSubsts*).asInstanceOf[Expr[Ind]]))
          val argsTypedSemantic = Time.measure(s"argsTypedSemantic"){have(wellTypedFormula(semanticSigAtArgs)) by Tautology.from(argTypings*)}
          val heightSigAtArgs = argTerms.zip(c.semantic.underlying.signature2.map(_._2)).map {
            case (term, SelfRef)       => term -> app(heightFun)(predVar)
            case (term, TypeArg(name)) => term -> typeExprToTerm(name).substitute(semanticSubsts*).asInstanceOf[Expr[Ind]]
          }
          val recursiveAtPred = c.semantic.recursiveArgInHeightAt(semanticSubsts)(heightFun, predVar)
          val valueSubsts = c.semantic.variables2.zip(argTerms).map((v, t) => v := t)
          val childTypingsAtPred = Time.measure(s"childTypingsAtPred"){have(wellTypedFormula(heightSigAtArgs)) by Tautology.from(
            hValid,
            predInN,
            argsTypedSemantic,
            currentInSuccPred,
            recursiveAtPred.of(valueSubsts*)
          )}

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
          Time.measure(s"targetInHeight"){have(target ∈ app(heightFun)(currentIndex)) by Tautology.from(
            hValid,
            currentIndexInN,
            predInN,
            predSubCurrent,
            innerAtPred,
            heightMembershipMonotonic.of(h := heightFun, n := currentIndex, m := predVar, x := target)
          )}
        }
        val fromPredWitness = thenHave(
          ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar))) |- target ∈ app(heightFun)(currentIndex)
        ) by LeftExists
        have(target ∈ app(heightFun)(currentIndex)) by Cut(predWitnessAtIndex, fromPredWitness)

  // def recursiveAgreementPointInHeight[N <: Arity](using
  //     proof: lisa.SetTheoryLibrary.Proof,
  //     line: sourcecode.Line,
  //     file: sourcecode.File
  // )(
  //     pattern: NestedConstructorPattern[N],
  //     target: Variable[Ind],
  //     recursiveType: Expr[Ind],
  //     heightFun: Expr[Ind],
  //     hValid: proof.Fact,
  //     heightMembershipMonotonic: THM,
  //     currentIndex: Expr[Ind],
  //     currentIndexInN: proof.Fact,
  //     argsTypedAtHeight: proof.Fact,
  //     leafTyping: proof.Fact,
  //     patternGuard: proof.Fact
  // ): proof.Fact = {
  //   require(
  //     pattern.recursiveAgreementPoints(recursiveType).contains(target),
  //     s"Pattern ${pattern.name} does not expose $target as a recursive agreement point."
  //   )
  //   val guard = pattern.freshGuards.find { g =>
  //     val guardType = pattern.semanticConstructor.semanticSignature2(g.position)._2
  //       .substitute(pattern.typeSubstitutions*).asInstanceOf[Expr[Ind]]
  //     NestedTrieProofs.guardBinders(g.guardTerm, guardType).exists(_._1 == target)
  //   }.getOrElse(
  //     throw new IllegalArgumentException(s"No guard contains recursive agreement point $target in pattern ${pattern.name}.")
  //   )

  //   val guardType = pattern.semanticConstructor.semanticSignature2(guard.position)._2
  //     .substitute(pattern.typeSubstitutions*).asInstanceOf[Expr[Ind]]
  //   val guardTy = ADT.unapply(guardType).get
  //   val binderInHeight = have(guard.binder ∈ app(heightFun)(currentIndex)) by Tautology.from(argsTypedAtHeight)
  //   val guardEq = have(guard.binder === guard.guardTerm) by Tautology.from(patternGuard)
  //   val guardInHeight = have(guard.guardTerm ∈ app(heightFun)(currentIndex)) by Congruence.from(binderInHeight, guardEq)

  //   Time.measure(s"RecArg/descendToBinder") {descendToBinder(
  //     heightFun = heightFun,
  //     hValid = hValid,
  //     heightMembershipMonotonic = heightMembershipMonotonic,
  //     currentIndex = currentIndex,
  //     currentIndexInN = currentIndexInN,
  //     leafTyping = leafTyping,
  //     currentPat = NestedTrieProofs.parse(guard.guardTerm),
  //     currentTy = guardTy,
  //     currentInHeight = guardInHeight,
  //     target = target
  //   )}
  // }
}

/**
 * Pattern system supporting several guarded branches for the same constructor.
 *
 * Proof obligations are intentionally left open for now.
 */
private[PatternMatching] final case class NestedPatternSystem[N <: Arity](
    domain: SemanticADT[N],
    override val patterns: Seq[NestedConstructorPattern[N]],
    typeSubstitutions: Seq[TypeSubstitution],
    specializedAdtTerm: Expr[Ind]
) extends PatternSystem[N] {
  validateRestrictedShape()

  override def constructors: Seq[SemanticConstructor[N]] =
    patterns.map(_.semanticConstructor).distinct

  override def patternsFor(constructor: SemanticConstructor[N]): Seq[Pattern[N]] =
    patterns.filter(_.semanticConstructor == constructor)

  override def supportsAutomaticCoverage: Boolean = false

  override lazy val coverage: THM = Time.measure(s"Pattern/Coverage") {
    val coveredTerm = variable[Ind]
    val specializedDomainTerm = specializedAdtTerm
    val specializedDomainElim = domainElim()
    val target = ∀(
      coveredTerm :: specializedDomainTerm,
      specializedCaseCoverage(coveredTerm)
    )
    Lemma(target) {
      val coverageAtPoint = have(
        coveredTerm :: specializedDomainTerm ==> specializedCaseCoverage(coveredTerm)
      ) subproof {
        val constructorCoverageFacts = constructors.map(constructor =>
          val constructorCase = specializedConstructorCase(constructor, coveredTerm)
          val constructorPatterns = patternsForNested(constructor)

          val directCoverage = if constructorPatterns.size == 1 then
            val pattern = constructorPatterns.head
            val directBranch = have(
              (wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*) /\
                ((coveredTerm === constructor.appliedTerm2).substitute(typeSubstitutions*))) |- specializedCaseCoverage(coveredTerm)
            ) subproof {
              assume(
                wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*) /\
                  ((coveredTerm === constructor.appliedTerm2).substitute(typeSubstitutions*))
              )
              val freshCase = have(
                pattern.freshBranchPremise /\
                  (coveredTerm === pattern.freshInputTerm)
              ) by Tautology
              val branchCase = have(
                existsSeq(
                  pattern.variables2,
                  pattern.freshBranchPremise /\ (coveredTerm === pattern.freshInputTerm)
                )
              ) by QuantifiersIntro(pattern.variables2)(freshCase)
              have(specializedCaseCoverage(coveredTerm)) by Tautology.from(branchCase)
            }

            constructor.variables2.reverse.foldLeft(directBranch)((fact, v) =>
              thenHave(∃(v, fact.statement.left.head) |- specializedCaseCoverage(coveredTerm)) by LeftExists
            )
          else
            val selectionSchema = branchSelectionFor(constructor, coveredTerm)
            val directCoverage = have(
              (wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*) /\
                ((coveredTerm === constructor.appliedTerm2).substitute(typeSubstitutions*))) |- specializedCaseCoverage(coveredTerm)
            ) subproof {
              val ctorCaseAssumption = assume(
                wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*) /\
                  ((coveredTerm === constructor.appliedTerm2).substitute(typeSubstitutions*))
              )
              val argsTyped = have(wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*)) by Tautology
              val selectionSchemaInContext = have(selectionSchema.statement.right.head) by
                Tautology.from(selectionSchema)
              var selectionAtCtorVars = selectionSchemaInContext
              for v <- constructor.variables2 do
                selectionAtCtorVars.statement.right.head match
                  case forall(qv, phi) =>
                    selectionAtCtorVars =
                      have(phi.substituteUnsafe(Map(qv -> v)).asInstanceOf[Expr[Prop]]) by
                        InstantiateForall(v)(selectionAtCtorVars)
                  case _ => ()
              val selectedBranch = selectionAtCtorVars.statement.right.head match
                case _ ==> consequent =>
                  have(consequent) by Tautology.from(selectionAtCtorVars, ctorCaseAssumption)
                case _ => throw UnreachableException

              val branchCoverageFacts = constructorPatterns.map(pattern =>
                have(
                  (pattern.freshBranchCondition /\ (coveredTerm === pattern.freshInputTerm)) |- specializedCaseCoverage(coveredTerm)
                ) subproof {
                  assume(pattern.freshBranchCondition /\ (coveredTerm === pattern.freshInputTerm))
                  val branchCond = have(pattern.freshBranchCondition) by Tautology
                  val inputEq = have(coveredTerm === pattern.freshInputTerm) by Tautology
                  val freshCase = have(
                    pattern.freshBranchPremise /\ (coveredTerm === pattern.freshInputTerm)
                  ) by Tautology.from(argsTyped, branchCond, inputEq)
                  val branchCase = have(
                    existsSeq(
                      pattern.variables2,
                      pattern.freshBranchPremise /\ (coveredTerm === pattern.freshInputTerm)
                    )
                  ) by QuantifiersIntro(pattern.variables2)(freshCase)
                  have(specializedCaseCoverage(coveredTerm)) by Tautology.from(branchCase)
                }
              )

              val selectedCoverage = if branchCoverageFacts.size == 1 then
                have(targetBody(constructor, coveredTerm) |- specializedCaseCoverage(coveredTerm)) by
                  Tautology.from(branchCoverageFacts.head)
              else
                have(targetBody(constructor, coveredTerm) |- specializedCaseCoverage(coveredTerm)) by
                  LeftOr(branchCoverageFacts*)

              have(specializedCaseCoverage(coveredTerm)) by Tautology.from(selectedBranch, selectedCoverage)
            }

            constructor.variables2.reverse.foldLeft(directCoverage)((fact, v) =>
              thenHave(∃(v, fact.statement.left.head) |- specializedCaseCoverage(coveredTerm)) by LeftExists
            )

          constructorCase -> directCoverage
        )

        val decompositionAtInput = have(
        coveredTerm :: specializedDomainTerm ==> specializedConstructorDisjunction(coveredTerm)
      ) by InstantiateForall(coveredTerm)(specializedDomainElim)

        val constructorsToCoverage =
          if constructorCoverageFacts.size == 1 then
            have(specializedConstructorDisjunction(coveredTerm) |- specializedCaseCoverage(coveredTerm)) by
              Restate.from(constructorCoverageFacts.head._2)
          else
            have(specializedConstructorDisjunction(coveredTerm) |- specializedCaseCoverage(coveredTerm)) by
              LeftOr(constructorCoverageFacts.map(_._2)*)

        assume(coveredTerm :: specializedDomainTerm)
        val coveredByCtor = have(specializedConstructorDisjunction(coveredTerm)) by
          Tautology.from(decompositionAtInput)
        have(specializedCaseCoverage(coveredTerm)) by Tautology.from(constructorsToCoverage, coveredByCtor)
      }

      have(thesis) by RightForall(coverageAtPoint)
    }
  }

  override def branchSelectionFor(
      constructor: SemanticConstructor[N],
      term: Expr[Ind]
  ): THM = branchSelectionCache.getOrElseUpdate(
      (constructor, term), Time.measure(s"Pattern/Branch selection"){
    val genericStatement = forallSeq(
      constructor.variables2,
      (wellTypedFormula(constructor.semanticSignature2) /\ (term === constructor.appliedTerm2)) ==>
        seqOr(patternsFor(constructor).map(pattern =>
          pattern.freshBranchCondition /\ (term === pattern.freshInputTerm)
        ))
    )
    val target = genericStatement.substitute(typeSubstitutions*)
    val constructorPatterns = patternsForNested(constructor)

    if constructorPatterns.size == 1 then
      Lemma(target) {
        have(thesis) by Tautology
      }
    else
      val splitPosition = constructorPatterns.head.guards.head.position
      val splitVariable = constructor.variables2(splitPosition)
      val (guardAdt, typeArgs) = resolveArgAdt(constructor, constructorPatterns.head.guards.head)
      val guardType = constructor.semanticSignature2(splitPosition)._2.substitute(typeSubstitutions*)
      val elimination = adtElimAt(guardAdt, typeArgs)
      Lemma(target) {
        val eliminationAtGuard = have(
          splitVariable :: guardType ==> simplify(guardAdtIsConstructorDisjunction(guardAdt, typeArgs, splitVariable))
        ) by InstantiateForall(splitVariable)(elimination)

        val pointwise = have(
          (wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*) /\
            ((term === constructor.appliedTerm2).substitute(typeSubstitutions*))) ==> targetBody(constructor, term)
        ) subproof {
          assume(
            wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*) /\
              ((term === constructor.appliedTerm2).substitute(typeSubstitutions*))
          )
          val argsTyped = have(wellTypedFormula(constructor.semanticSignature2).substitute(typeSubstitutions*)) by Tautology
          val inputEq = have((term === constructor.appliedTerm2).substitute(typeSubstitutions*)) by Tautology
          val splitTyped = have(splitVariable :: guardType) by Tautology.from(argsTyped)
          val constructorDisjunction = have(
            simplify(guardAdtIsConstructorDisjunction(guardAdt, typeArgs, splitVariable))
          ) by Tautology.from(eliminationAtGuard, splitTyped)
          have(targetBody(constructor, term)) by Tautology.from(constructorDisjunction, inputEq)
        }

        var quantified = pointwise
        for v <- constructor.variables2.reverse do
          quantified = thenHave(∀(v, quantified.statement.right.head)) by RightForall
        have(thesis) by Tautology.from(quantified)
      }
  })

  override def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM =
    incompatibleCache.getOrElseUpdate(
      (pattern1, pattern2), Time.measure(s"Pattern/Incompatible") {
    require(pattern1 != pattern2, "incompatible is only meaningful for distinct patterns.")
    val constructorPattern1 = pattern1 match
      case pattern: NestedConstructorPattern[N] => pattern
      case _ =>
        throw new IllegalArgumentException(
          s"Pattern ${pattern1.name} is not a nested constructor-headed pattern."
        )
    val constructorPattern2 = pattern2 match
      case pattern: NestedConstructorPattern[N] => pattern
      case _ =>
        throw new IllegalArgumentException(
          s"Pattern ${pattern2.name} is not a nested constructor-headed pattern."
        )

    if !constructorPattern1.hasSameHeadAs(constructorPattern2) then
      ConstructorPatternSystem(
        ADT.getADT(constructorPattern1.semanticConstructor.adt.name).get.semantic.asInstanceOf[SemanticADT[N]],
        Seq(constructorPattern1, constructorPattern2).asInstanceOf[Seq[ConstructorHeadPattern[N]]],
        specializedAdtTerm
      )
        .incompatible(constructorPattern1, constructorPattern2)
    else
      val (guard1, guard2) = distinctSameHeadGuards(constructorPattern1, constructorPattern2)
      val distinctGuardTerms = nullaryGuardDisequality(guard1.resolvedNullary.get, guard2.resolvedNullary.get)

      Lemma(
        (constructorPattern1.branchPremise1 /\ constructorPattern2.freshBranchPremise) ==>
          !(constructorPattern1.inputTerm1 === constructorPattern2.inputTerm2)
      ) {
        val branch = assume(constructorPattern1.branchPremise1 /\ constructorPattern2.freshBranchPremise)
        val branch1Typed = have(constructorPattern1.branchPremise1) by Tautology.from(branch)
        val branch2Typed = have(constructorPattern2.freshBranchPremise) by Tautology.from(branch)

        assume(constructorPattern1.inputTerm1 === constructorPattern2.inputTerm2)
        val inputsEqual = have(constructorPattern1.inputTerm1 === constructorPattern2.inputTerm2) by Hypothesis

        val injectivitySchema = have(constructorPattern1.injectivity.statement.right.head) by
          Tautology.from(constructorPattern1.injectivity)
        var injectivityAtVars = injectivitySchema
        for v <- constructorPattern1.variables1 ++ constructorPattern2.variables2 do
          injectivityAtVars.statement.right.head match
            case forall(qv, phi) =>
              injectivityAtVars = have(phi.substituteUnsafe(Map(qv -> v)).asInstanceOf[Expr[Prop]]) by
                InstantiateForall(v)(injectivityAtVars)
            case _ => ()

        val guardedArgsEqual = have(guard1.binder === guard2.binder) by
          Tautology.from(injectivityAtVars, branch1Typed, branch2Typed, inputsEqual)

        val guard1Eq = have(guard1.binder === guard1.guardTerm) by Tautology.from(branch1Typed)
        val guard2Eq = have(guard2.binder === guard2.guardTerm) by Tautology.from(branch2Typed)
        val guard1EqRev = have(guard1.guardTerm === guard1.binder) by Congruence.from(guard1Eq)
        val guard1ToGuard2Binder = have(guard1.guardTerm === guard2.binder) by Tautology.from(
          altEqualityTransitivity of (
            x := guard1.guardTerm,
            y := guard1.binder,
            z := guard2.binder
          ),
          guard1EqRev,
          guardedArgsEqual
        )
        val guardTermsEqual = have(guard1.guardTerm === guard2.guardTerm) by Tautology.from(
          altEqualityTransitivity of (
            x := guard1.guardTerm,
            y := guard2.binder,
            z := guard2.guardTerm
          ),
          guard1ToGuard2Binder,
          guard2Eq
        )

        have(thesis) by Tautology.from(guardTermsEqual, distinctGuardTerms)
      }
  })

  private def validateRestrictedShape(): Unit =
    constructors.foreach(constructor => validateConstructorPatterns(constructor, patternsForNested(constructor)))

  private def resolveArgAdt(
      constructor: SemanticConstructor[N],
      guard: BranchGuard
  ): (ADT[?], Seq[Expr[Ind]]) =
    val argType = constructor.semanticSignature2(guard.position)._2.substitute(typeSubstitutions*)
    ADT.unapply(argType).getOrElse(
      throw new IllegalArgumentException(
        s"Cannot resolve ADT for guarded position ${guard.position} of constructor ${constructor.name} (type $argType)."
      )
    )

  private def adtElimAt(adt: ADT[?], typeArgs: Seq[Expr[Ind]]): THM =
    typeArgs match
      case Seq()          => adt.elim
      case first +: rest  => adt.elim(first, rest*)

  private def domainElim(): THM =
    val (adt, typeArgs) = ADT.unapply(specializedAdtTerm).getOrElse(
      throw new IllegalArgumentException(
        s"Cannot resolve specialized ADT for coverage term $specializedAdtTerm."
      )
    )
    adtElimAt(adt, typeArgs)

  private def distinctSameHeadGuards(
      pattern1: NestedConstructorPattern[N],
      pattern2: NestedConstructorPattern[N]
  ): (BranchGuard, BranchGuard) =
    val guard1 = pattern1.guardsAt(pattern1.variables1).headOption.getOrElse(
      throw new IllegalArgumentException(
        s"Same-head pattern ${pattern1.name} has no tracked guard."
      )
    )
    val guard2 = pattern2.freshGuards.headOption.getOrElse(
      throw new IllegalArgumentException(
        s"Same-head pattern ${pattern2.name} has no tracked guard."
      )
    )
    require(
      guard1.position == guard2.position,
      s"Same-head patterns ${pattern1.name} and ${pattern2.name} guard different positions."
    )
    val resolved1 = guard1.resolvedNullary.getOrElse(
      throw new IllegalArgumentException(
        s"Pattern ${pattern1.name} does not carry a resolved nullary guard."
      )
    )
    val resolved2 = guard2.resolvedNullary.getOrElse(
      throw new IllegalArgumentException(
        s"Pattern ${pattern2.name} does not carry a resolved nullary guard."
      )
    )
    require(
      resolved1.constructor.id != resolved2.constructor.id,
      s"Patterns ${pattern1.name} and ${pattern2.name} overlap on the same guarded constructor ${resolved1.constructor.name}."
    )
    (guard1, guard2)

  private def nullaryGuardDisequality(
      guard1: ResolvedNullaryGuard,
      guard2: ResolvedNullaryGuard
  ): THM =
    val constructor1 = guard1.constructor.semantic
    val constructor2 = guard2.constructor.semantic
    require(
      constructor1.arity == 0 && constructor2.arity == 0,
      "nullaryGuardDisequality expects nullary constructors."
    )
    require(
      guard1.appliedTerm == constructor1.appliedTerm1 && guard2.appliedTerm == constructor2.appliedTerm2,
      "Resolved guard term does not match the constructor's nullary applied term."
    )

    Lemma(!(guard1.appliedTerm === guard2.appliedTerm)) {
      val constructor1Def = have(constructor1.shortDefinition.statement.right.head) by
        Tautology.from(constructor1.shortDefinition)
      val constructor1Eq = constructor1Def.statement.right.head match
        case _ ==> consequent => have(consequent) by Tautology.from(constructor1Def)
        case consequent            => have(consequent) by Tautology.from(constructor1Def)
      val constructor2Def = have(constructor2.shortDefinition.statement.right.head) by
        Tautology.from(constructor2.shortDefinition)
      val constructor2Eq = constructor2Def.statement.right.head match
        case _ ==> consequent => have(consequent) by Tautology.from(constructor2Def)
        case consequent            => have(consequent) by Tautology.from(constructor2Def)

      assume(guard1.appliedTerm === guard2.appliedTerm)
      val inputsEqual = have(guard1.appliedTerm === guard2.appliedTerm) by Hypothesis
      val constructor1EqRev = have(constructor1.structuralTerm1 === guard1.appliedTerm) by
        Congruence.from(constructor1Eq)
      val constructor1ToApplied2 = have(constructor1.structuralTerm1 === guard2.appliedTerm) by Tautology.from(
        altEqualityTransitivity of (
          x := constructor1.structuralTerm1,
          y := guard1.appliedTerm,
          z := guard2.appliedTerm
        ),
        constructor1EqRev,
        inputsEqual
      )
      val structuralEq = have(constructor1.structuralTerm1 === constructor2.structuralTerm2) by Tautology.from(
        altEqualityTransitivity of (
          x := constructor1.structuralTerm1,
          y := guard2.appliedTerm,
          z := constructor2.structuralTerm2
        ),
        constructor1ToApplied2,
        constructor2Eq
      )
      val structuralDifferent = have(!(constructor1.structuralTerm1 === constructor2.structuralTerm2)) by
        Tautology.from(constructor1.structuralDisjointness(constructor2))
      have(thesis) by Tautology.from(structuralEq, structuralDifferent)
    }

  private def guardAdtIsConstructorDisjunction(
      adt: ADT[?],
      typeArgs: Seq[Expr[Ind]],
      variable: Variable[Ind]
  ): Expr[Prop] =
    val constructorCases = adt.constructors.map(constructor =>
      if typeArgs.isEmpty then variable === constructor.term
      else variable === constructor.termAt(typeArgs)
    )
    seqOr(constructorCases)

  private def targetBody(
      constructor: SemanticConstructor[N],
      term: Expr[Ind]
  ): Expr[Prop] =
    seqOr(patternsForNested(constructor).map(pattern =>
      pattern.freshBranchCondition /\ (term === pattern.freshInputTerm)
    ))

  private def specializedConstructorCase(
      constructor: SemanticConstructor[N],
      term: Expr[Ind]
  ): Expr[Prop] =
    existsSeq(
      constructor.variables2,
      (wellTypedFormula(constructor.semanticSignature2) /\ (term === constructor.appliedTerm2)).substitute(typeSubstitutions*).asInstanceOf[Expr[Prop]]
    )

  private def specializedConstructorDisjunction(term: Expr[Ind]): Expr[Prop] =
    simplify(seqOr(constructors.map(constructor => specializedConstructorCase(constructor, term))))

  private def specializedCaseCoverage(term: Expr[Ind]): Expr[Prop] =
    simplify(caseCoverage(term))

  private def patternsForNested(constructor: SemanticConstructor[N]): Seq[NestedConstructorPattern[N]] =
    patterns.filter(_.semanticConstructor == constructor)

  private def validateConstructorPatterns(
      constructor: SemanticConstructor[N],
      constructorPatterns: Seq[NestedConstructorPattern[N]]
  ): Unit =
    require(
      constructorPatterns.nonEmpty,
      s"No pattern registered for constructor ${constructor.name}."
    )

    if constructorPatterns.size == 1 then
      validateSinglePatternConstructor(constructor, constructorPatterns.head)
    else
      validateSplitConstructor(constructor, constructorPatterns)

  private def validateSinglePatternConstructor(
      constructor: SemanticConstructor[N],
      pattern: NestedConstructorPattern[N]
  ): Unit =
    require(
      pattern.guards.isEmpty,
      s"Constructor ${constructor.name} has a single nested branch with guards. This restricted nested-pattern implementation only supports either one unconditional branch or an exhaustive nullary split."
    )

  private def validateSplitConstructor(
      constructor: SemanticConstructor[N],
      constructorPatterns: Seq[NestedConstructorPattern[N]]
  ): Unit =
    constructorPatterns.foreach(pattern =>
      require(
        pattern.guards.size == 1,
        s"Constructor ${constructor.name} must split on exactly one guarded position per branch; branch ${pattern.name} has ${pattern.guards.size} guard(s)."
      )
    )

    val guardedPosition = constructorPatterns.head.guards.head.position
    require(
      constructorPatterns.forall(_.guards.head.position == guardedPosition),
      s"Constructor ${constructor.name} has nested branches guarding different argument positions. Only one shared guarded position is supported."
    )

    val resolvedGuards = constructorPatterns.map(pattern =>
      pattern.guards.head.resolvedNullary.getOrElse(
        throw new IllegalArgumentException(
          s"Constructor ${constructor.name} uses a non-nullary or non-constructor guard term ${pattern.guards.head.guardTerm}. Only nullary constructor guards are supported."
        )
      )
    )

    val guardAdts = resolvedGuards.map(_.constructor.semantic.adt.name).distinct
    require(
      guardAdts.size == 1,
      s"Constructor ${constructor.name} mixes guard constructors from different ADTs. A split constructor must guard one nullary-constructor ADT."
    )

    val guardAdt = resolvedGuards.head.constructor.semantic.adt
    val guardConstructors = ADT.getADT(guardAdt.name).getOrElse(
      throw new IllegalArgumentException(
        s"Guard ADT ${guardAdt.name} is not registered in the interface layer."
      )
    ).constructors
    require(
      guardConstructors.forall(_.semantic.arity == 0),
      s"Constructor ${constructor.name} guards over ADT ${guardAdt.name}, which has non-nullary constructors. Only nullary-constructor guard ADTs are supported."
    )

    val guardIds = resolvedGuards.map(_.constructor.id)
    require(
      guardIds.distinct.size == guardIds.size,
      s"Constructor ${constructor.name} repeats a guarded constructor in multiple branches. Guard constructors must be pairwise distinct."
    )

    val expectedGuardIds = guardConstructors.map(_.id).toSet
    require(
      guardIds.toSet == expectedGuardIds,
      s"Constructor ${constructor.name} does not form an exhaustive nullary split over ADT ${guardAdt.name}. Expected guards: ${guardConstructors.map(_.name).mkString(", ")}."
    )
}

private[PatternMatching] object NestedPatternSystem {
  def fromMixedArgs[N <: Arity](
      rawCases: Seq[(SemanticConstructor[N], Seq[Either[Variable[Ind], Expr[Ind]]], Expr[Ind])],
      domain: SemanticADT[N],
      typeSubstitutions: Seq[TypeSubstitution] = Seq.empty,
      specializedAdtTerm: Expr[Ind]
  ): NestedPatternSystem[N] =
    NestedPatternSystem(
      domain,
      rawCases.map((constructor, args, body) =>
        NestedConstructorPattern.fromArgs(constructor, args, body, typeSubstitutions, specializedAdtTerm)
      ),
      typeSubstitutions,
      specializedAdtTerm
    )
}
