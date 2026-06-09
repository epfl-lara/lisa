package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Ordinals.Ordinal.{S, successorOrdinal, ordinal, <=}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{NestedConstructorPattern, NestedTrieProofs, Pattern}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrieProofs.{RPat, Ty}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrieProofs.RPat.{RCon, RVar}
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.{ApproximationChainFacts, LimitKernel}
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.{ExtendedInteger, NatFacts}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{equivalenceApply, subsetSuccessor}
import lisa.maths.SetTheory.Types.ADTv2.support.Time

private[recursion] object RecursiveAgreement {

  final case class InnerAgreementContext[Fact](
      heightFun: Expr[Ind],
      hValid: Fact,
      currentIndex: Expr[Ind],
      currentIndexInN: Fact
  )

  def innerAgreementContext(using proof: lisa.SetTheoryLibrary.Proof)(
      heightFun: Expr[Ind],
      hValid: proof.Fact,
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact
  ): InnerAgreementContext[proof.Fact] =
    InnerAgreementContext(
      heightFun = heightFun,
      hValid = hValid,
      currentIndex = currentIndex,
      currentIndexInN = currentIndexInN
    )

  private val h = variable[Ind]
  private val x = variable[Ind]
  private val n = variable[Ind]
  private val m = variable[Ind]
  private val α = variable[Ind]
  private val betaVar = variable[Ind]
  private val pointVar = variable[Ind]
  private val upperVar = variable[Ind]
  private val lowerVar = variable[Ind]

  def recursiveInnerBinders[N <: lisa.utils.prooflib.ProofTacticLib.Arity](
      pattern: Pattern[N],
      recursiveType: Expr[Ind]
  ): Seq[Variable[Ind]] =
    pattern.typingSignatureAt(pattern.variables2).drop(pattern.arity).collect {
      case (v, ty) if ty == recursiveType => v
    }

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
        // Fresh predecessor variable per descent level: at deeper levels
        // `currentIndex` is the parent level's predecessor, so a shared name
        // would be captured by the `∃(predVar, currentIndex === S(predVar))`
        // binder and degenerate into the false `predVar === S(predVar)`.
        val predVar = Variable[Ind](freshId(Seq(currentIndex, target, heightFun), "predVar"))
        val currentTerm = NestedTrieProofs.termOf(currentPat, currentTy)
        // `heightZero` must be specialized to *this* level's type arguments: `hValid`
        // is the type-instantiated height predicate (e.g. `isHeight` at `bool/term`),
        // so the abstract `underlying.heightZero` (over the type variable `A`) would
        // leave Tautology with an undischargeable `isHeight[A]` precondition.
        val levelSubsts = currentTy._1.semantic.typeVariablesSeq.zip(currentTy._2).map((v, a) => v := a)
        val currentInZero = Time.measure(s"currentInZero"){have(!(currentTerm ∈ app(heightFun)(∅))) by Tautology.from(
          hValid,
          currentTy._1.semantic.height.zeroAt(levelSubsts).of(h := heightFun, x := currentTerm)
        )}

        val currentIndexNonZero = have(currentIndex =/= ∅) subproof {
          val currentIsZero = assume(currentIndex === ∅)
          // `currentIndex = ∅` ⇒ `h(currentIndex) = h(∅)`, so `currentInHeight` gives
          // `currentTerm ∈ h(∅)`, contradicting `currentInZero`. This is a pure
          // congruence/contradiction argument — `Congruence` handles it atomically via its
          // e-graph, whereas the previous `Tautology.from(currentInHeight, …)` decomposed
          // currentInHeight's deep ambient context (~13.6s).
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
          val succEq = have(S(predVar) === successor(predVar)) by Congruence.from(
            S.definition.of(α := predVar),
            successor.definition.of(x := predVar)
          )
          val predInN = have(predVar ∈ N) by Tautology

          val currentInSuccPred = have(currentTerm ∈ app(heightFun)(successor(predVar))) by Congruence.from(
            currentInHeight,
            currentEqSucc,
            succEq
          )

          val cts = NestedTrieProofs.resolvedChildTypes(c, currentTy._2)
          val argTerms = args.zip(cts).map((a, t) => NestedTrieProofs.termOf(a, t.get))
          val argTypings = args.zip(cts).map((a, t) => typeProof(leafTyping, a, t.get))
          val semanticSubsts = c.semantic.adt.typeVariablesSeq.zip(currentTy._2).map((v, a) => v := a)
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

          val predSubSucc = have(predVar ⊆ successor(predVar)) by Tautology.from(subsetSuccessor.of(n := predVar))
          val predSubCurrent = have(predVar ⊆ currentIndex) by Congruence.from(predSubSucc, currentEqSucc, succEq)
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

  private def innerBinderInHeight[N <: lisa.utils.prooflib.ProofTacticLib.Arity](using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      heightFun: Expr[Ind],
      hValid: proof.Fact,
      heightMembershipMonotonic: THM,
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact,
      argsTypedAtHeight: proof.Fact,
      leafTyping: proof.Fact,
      patternGuard: proof.Fact,
      pattern: NestedConstructorPattern[N],
      target: Variable[Ind]
  ): proof.Fact = {
    val guard = pattern.freshGuards.find { g =>
      val guardType = pattern.semanticConstructor.semanticSignature2(g.position)._2
        .substitute(pattern.typeSubstitutions*).asInstanceOf[Expr[Ind]]
      NestedTrieProofs.guardBinders(g.guardTerm, guardType).exists(_._1 == target)
    }.getOrElse(throw new IllegalArgumentException(s"No guard contains recursive inner binder $target."))

    val guardType = pattern.semanticConstructor.semanticSignature2(guard.position)._2
      .substitute(pattern.typeSubstitutions*).asInstanceOf[Expr[Ind]]
    val guardTy = ADT.unapply(guardType).get
    val binderInHeight = have(guard.binder ∈ app(heightFun)(currentIndex)) by Tautology.from(argsTypedAtHeight)
    val guardEq = have(guard.binder === guard.guardTerm) by Tautology.from(patternGuard)
    val guardInHeight = have(guard.guardTerm ∈ app(heightFun)(currentIndex)) by Congruence.from(binderInHeight, guardEq)

    Time.measure(s"Descend to inner binder $target") {descendToBinder(
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

  def innerAgreementsFor[N <: lisa.utils.prooflib.ProofTacticLib.Arity](using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      pattern: Pattern[N],
      recursiveType: Expr[Ind],
      heightMembershipMonotonic: THM,
      argsTypedAtHeight: proof.Fact,
      leafTyping: proof.Fact,
      patternGuard: proof.Fact,
      context: InnerAgreementContext[proof.Fact]
  )(
      agreementBuilder: InnerAgreementContext[proof.Fact] => ((Variable[Ind], proof.Fact) => proof.Fact)
  ): Seq[proof.Fact] =
    pattern match
      case nested: NestedConstructorPattern[?] =>
        val agreementAt = agreementBuilder(context)
        recursiveInnerBinders(nested, recursiveType).map { iv =>
          val ivInHeight = innerBinderInHeight(
            heightFun = context.heightFun,
            hValid = context.hValid,
            heightMembershipMonotonic = heightMembershipMonotonic,
            currentIndex = context.currentIndex,
            currentIndexInN = context.currentIndexInN,
            argsTypedAtHeight = argsTypedAtHeight,
            leafTyping = leafTyping,
            patternGuard = patternGuard,
            pattern = nested.asInstanceOf[NestedConstructorPattern[N]],
            target = iv
          )
          agreementAt(iv, ivInHeight)
        }
      case _ => Seq.empty

  def selfAgreementFromForall(using proof: lisa.SetTheoryLibrary.Proof)(
      heightFun: Expr[Ind],
      currentIndex: Expr[Ind],
      leftFun: Expr[Ind],
      rightFun: Expr[Ind],
      agreeForall: proof.Fact,
      point: Expr[Ind],
      pointInHeight: proof.Fact
  ): proof.Fact = {
    val pIn: Expr[Prop] = point ∈ app(heightFun)(currentIndex)
    val pEq: Expr[Prop] = app(leftFun)(point) === app(rightFun)(point)
    val atPoint = have(pIn ==> pEq) by InstantiateForall(point)(agreeForall)
    
    // Modus ponens via kernel rules instead of `Tautology.from(pointInHeight, atPoint)`:
    // `pointInHeight` carries the deep ~1.5k-char branchSelectionBody in its context, and
    // Tautology would decompose it (~30s). With `pIn`/`pEq` kept atomic, that context is
    // carried untouched through the cut.
    val mp = have(Set[Expr[Prop]](pIn ==> pEq, pIn) |- pEq) by LeftImplies.withParameters(pIn, pEq)(
      have(pIn |- pIn) by Hypothesis,
      have(pEq |- pEq) by Hypothesis
    )
    val viaImpl = have((atPoint.statement.left + pIn) |- pEq) by Cut(atPoint, mp)
    have((atPoint.statement.left ++ pointInHeight.statement.left) |- pEq) by Cut(pointInHeight, viaImpl)
    
  }

  def selfAgreementFromForallAt(using proof: lisa.SetTheoryLibrary.Proof)(
      leftFun: Expr[Ind],
      rightFun: Expr[Ind],
      agreeForall: proof.Fact
  )(context: InnerAgreementContext[proof.Fact]): (Variable[Ind], proof.Fact) => proof.Fact =
    (point, pointInHeight) =>
      selfAgreementFromForall(
        heightFun = context.heightFun,
        currentIndex = context.currentIndex,
        leftFun = leftFun,
        rightFun = rightFun,
        agreeForall = agreeForall,
        point = point,
        pointInHeight = pointInHeight
      )

  def selfAgreementWithLimit(using proof: lisa.SetTheoryLibrary.Proof)(
      argType: Expr[Ind],
      heightFun: Expr[Ind],
      limitFun: Expr[Ind],
      approximantFamily: Expr[Ind >>: Ind],
      chosenIndexFamily: Expr[Ind >>: Ind],
      limitFunDef: Expr[Prop],
      termHasHeight: THM,
      stabilizationSchema: proof.Fact,
      heightMembershipMonotonicSchema: proof.Fact,
      hValid: proof.Fact,
      currentIndex: Expr[Ind],
      currentIndexInN: proof.Fact,
      point: Expr[Ind],
      pointInHeight: proof.Fact
  ): proof.Fact = {
    val pointHeightChar = have(LimitKernel.pointHeightCharAt(argType, heightFun, point)) by
      Tautology.from(hValid, termHasHeight.of(x := point, h := heightFun))
    have(app(limitFun)(point) === app(approximantFamily(currentIndex))(point)) by Tautology.from(
      pointHeightChar,
      have(LimitKernel.limitIndexDefinitionAt(heightFun, chosenIndexFamily, point)) by Restate,
      have(limitFunDef) by Restate,
      have(LimitKernel.approxAgreementAt(heightFun, approximantFamily, point, chosenIndexFamily(point), currentIndex)) by
        Tautology.from(
          ApproximationChainFacts.approximantsAgreeAcrossHeightsAt(
            heightFun,
            approximantFamily,
            chosenIndexFamily(point),
            currentIndex,
            point
          )(stabilizationSchema, heightMembershipMonotonicSchema)
        ),
      currentIndexInN,
      pointInHeight,
      LimitKernel.limitAtHeightAt(
        argType,
        heightFun,
        limitFun,
        approximantFamily,
        chosenIndexFamily,
        point,
        currentIndex
      )
    )
  }

  def selfAgreementWithLimitAt(using proof: lisa.SetTheoryLibrary.Proof)(
      argType: Expr[Ind],
      limitFun: Expr[Ind],
      approximantFamily: Expr[Ind >>: Ind],
      chosenIndexFamily: Expr[Ind >>: Ind],
      limitFunDef: Expr[Prop],
      termHasHeight: THM,
      stabilizationSchema: proof.Fact,
      heightMembershipMonotonicSchema: proof.Fact
  )(context: InnerAgreementContext[proof.Fact]): (Variable[Ind], proof.Fact) => proof.Fact =
    (point, pointInHeight) =>
      selfAgreementWithLimit(
        argType = argType,
        heightFun = context.heightFun,
        limitFun = limitFun,
        approximantFamily = approximantFamily,
        chosenIndexFamily = chosenIndexFamily,
        limitFunDef = limitFunDef,
        termHasHeight = termHasHeight,
        stabilizationSchema = stabilizationSchema,
        heightMembershipMonotonicSchema = heightMembershipMonotonicSchema,
        hValid = context.hValid,
        currentIndex = context.currentIndex,
        currentIndexInN = context.currentIndexInN,
        point = point,
        pointInHeight = pointInHeight
      )
}
