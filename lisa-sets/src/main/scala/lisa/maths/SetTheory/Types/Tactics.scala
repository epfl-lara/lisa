package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.maths.SetTheory.Base.Subset.reflexivity
import lisa.maths.SetTheory.Base.Subset.transitivity
import lisa.maths.SetTheory.Cardinal.Predef.isUniverse
import lisa.maths.SetTheory.Cardinal.Predef.universeOf
import lisa.maths.SetTheory.Cardinal.Predef.universeOfIsUniverse
import lisa.maths.SetTheory.Functions.Predef._
import lisa.utils.K
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.Exports._
import lisa.utils.prooflib.ProofCarrier
import lisa.utils.prooflib.ProofJudgement
import lisa.utils.prooflib.Proof
import lisa.utils.prooflib.Subproof
import lisa.utils.prooflib.SubproofM
import lisa.utils.prooflib.Thm
import lisa.utils.prooflib.TacticHelpers.failWith

import scala.collection.Set
import scala.collection.mutable

import F.{∀ => _, _}
import TypingRules.{TAbs, TApp, TSort, TConvAdv}
import TypingHelpers._
import TypingTheorems.{universeHierarchyPiClosureLeft, universeHierarchyPiClosureRight, subsetOfUniverse, piCovariance}

object Tactics:
  val x, y, z, A, B, C: Variable[Ind] = variable[Ind]
  // Base term
  private val e1, e2: Variable[Ind] = variable[Ind]

  // Function
  private val e = variable[Ind >>: Ind]

  // Base type
  private val T, T1: Variable[Ind] = variable[Ind]

  // Dependent type
  private val T2, T2p: Variable[Ind >>: Ind] = variable[Ind >>: Ind]

  // Proposition
  private val Q, H: Variable[Ind >>: Prop] = variable[Ind >>: Prop]

  // Type Universe
  private val U, U1, U2: Variable[Ind] = variable[Ind]

  // Proposition
  private val p: Variable[Prop] = variable[Prop]

  object Typecheck:
    /** Extract one side of a proved conjunction with explicit sequent steps. */
    private def conjunct(using lib: SetTheoryLibrary.type, proof: Proof)(fact: Thm, takeLeft: Boolean): Thm =
      fact.statement.right.head match
        case conjunction @ (left /\ right) =>
          val selected = if takeLeft then left else right
          val expandedLeft = fact.statement.left ++ Set(left, right)
          val selectedHypothesis = have(expandedLeft |- selected) by Hypothesis.withParameters(selected)
          val fromConjunction = have((fact.statement.left + conjunction) |- selected) by
            LeftAnd.withParameters(left, right)(selectedHypothesis)
          have(fact.statement.left |- selected) by Cut.withParameters(conjunction)(fact, fromConjunction)
        case _ => throw new IllegalArgumentException(s"Expected a proved conjunction, got ${fact.statement}")

    /** Memoize recursive checks while constructing one typing proof. */
    private final class Memo:
      private val inferred = mutable.HashMap.empty[(Set[Long], Long), ProofCarrier[Expr[Ind]]]
      private val checked = mutable.HashMap.empty[(Set[Long], Long, Long), ProofJudgement]

      private def contextKey(localContext: Set[Expr[Prop]]): Set[Long] =
        localContext.map(_.underlying.uniqueNumber)

      def infer(localContext: Set[Expr[Prop]], tm: Expr[Ind])(compute: => ProofCarrier[Expr[Ind]]): ProofCarrier[Expr[Ind]] =
        inferred.getOrElseUpdate((contextKey(localContext), tm.underlying.uniqueNumber), compute)

      def check(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind])(compute: => ProofJudgement): ProofJudgement =
        checked.getOrElseUpdate((contextKey(localContext), tm.underlying.uniqueNumber, ty.underlying.uniqueNumber), compute)

    // Helper function: get universe level
    def getDepth(e: Expr[Ind]): Int = e match
      case App(universeOf, inner: Expr[Ind]) => 1 + getDepth(inner)
      case _ => 1

    // Bidirectional type checking proof construct(infer, check, equal)
    def prove(using lib: SetTheoryLibrary.type, proof: Proof)(bot: F.Sequent): ProofJudgement =
      import lib.*
      if bot.right.size != 1 then invalidTactic("Typecheck can only prove one theorem once upon a time")
      else
        val premises = bot.left
        val goal = bot.right.head
        Subproof {
          goal match
            case typeOf(tm, ty) =>
              val innerProof = checkProof(using SetTheoryLibrary)(premises, tm, ty)
              if !innerProof.isValid then failWith(innerProof)
              val stmt = have(innerProof)
              val (toEliminate, toKeep) = stmt.statement.left.partition {
                case App(cmd, App(tag, t2)) =>
                  cmd == isUniverse && tag == universeOf
                case _ => false
              }
              val lemmaFacts = toEliminate.map { univFact =>
                univFact match
                  case App(cmd, App(tag, v: Expr[Ind])) => universeOfIsUniverse of (x := v)
                  case _ => throw new Exception("Unreachable code: structure validation failed")
              }.toSeq
              val universeFacts = lemmaFacts.map(conjunct(_, takeLeft = true))
              val cleaned = have(Discharge(universeFacts*)(stmt))
              have(stmt.statement.removeAllLeft(toEliminate)) by Weakening(cleaned)
              thenHave(premises |- tm ∈ ty) by Weakening
            case _ => failWith("Type check can only check type relation(∈)")
        }

    def apply(using lib: SetTheoryLibrary.type, proof: Proof)(bot: F.Sequent): ProofJudgement =
      prove(bot)

    /** Derive application typing from proved function and argument typings; return the result type. */
    def applicationProof(using lib: SetTheoryLibrary.type, proof: Proof)(
        function: Expr[Ind],
        argument: Expr[Ind],
        functionType: Expr[Ind]
    )(functionTyping: Thm, argumentTyping: Thm): ProofCarrier[Expr[Ind]] = SubproofM {
      import lib.*
      functionType match
        case SPi(domain: Expr[Ind], codomain @ Abs(bound: Expr[Ind], body: Expr[Ind])) =>
          // Substitute frontend annotations even when the erased codomain is independent.
          val resultType = body.substitute(bound := argument)
          val statement = (app(function)(argument) ∈ resultType) ++<< functionTyping.statement ++<< argumentTyping.statement
          val functionFormula = function ∈ functionType
          val argumentFormula = argument ∈ domain
          val rule = TApp of (e1 := function, e2 := argument, T1 := domain, T2 := codomain)
          val conclusion = rule.statement.right.head
          val withFunction = have((conclusion +<< argumentFormula) ++<< functionTyping.statement) by
            Cut.withParameters(functionFormula)(functionTyping, rule)
          val applied = have((conclusion ++<< functionTyping.statement) ++<< argumentTyping.statement) by
            Cut.withParameters(argumentFormula)(argumentTyping, withFunction)
          val typing = have(statement) by Restate(applied)
          ProofJudgement(typing).map(_ => resultType)
        case _ => failWith(s"Expected a Π-type with a lambda codomain, got $functionType.")
    }

    /** Derive abstraction typing from a proved body typing; return the dependent product type. */
    def abstractionProof(using lib: SetTheoryLibrary.type, proof: Proof)(
        bound: Variable[Ind],
        domain: Expr[Ind],
        body: Expr[Ind],
        bodyType: Expr[Ind]
    )(bodyTyping: Thm): ProofCarrier[Expr[Ind]] = SubproofM {
      import lib.*
      val resultType = Pi(domain)(λ(bound, bodyType))

      // Shared body proofs can carry alpha-equivalent copies of the binder's typing.
      val assumption = bound ∈ domain
      val conclusion = body ∈ bodyType
      val resetBot = bodyTyping.statement -<? assumption
      val weakened = have((assumption |- conclusion) ++<< bodyTyping.statement) by Weakening(bodyTyping)
      val implication = have((assumption ==> conclusion) ++<< resetBot) by
        RightImplies.withParameters(assumption, conclusion)(weakened)
      have((∀(bound ∈ domain, body ∈ bodyType)) ++<< resetBot) by
        RightForall.withParameters(assumption ==> conclusion, bound)(implication)
      val quantifiedTyping = lastStep

      val abstraction = TAbs of (T1 := domain, T2 := Abs(bound, bodyType), e := Abs(bound, body))
      val typing = have(Discharge(quantifiedTyping)(abstraction))
      ProofJudgement(typing).map(_ => resultType)
    }

    /**
     * Infer a type for `tm` and prove the corresponding typing judgement.
     *
     * The payload and justification have the invariant
     *
     * ```
     * payload       = inferredType
     * justification = context |- tm ∈ inferredType
     * ```
     *
     * Keeping the type in the carrier is important: recursive callers receive
     * both results together and never have to recover the type by inspecting
     * the right-hand side of the generated theorem.
     */
    private def inferProofM(using lib: SetTheoryLibrary.type, proof: Proof)(
        localContext: Set[Expr[Prop]],
        tm: Expr[Ind],
        memo: Memo
    ): ProofCarrier[Expr[Ind]] =
      memo.infer(localContext, tm) {
        import lib.*
        SubproofM {
        tm match
          /**
           * Function application:
           *
           *     Γ₁ |- func ∈ Π(x : T₁). T₂(x)    Γ₂ |- arg ∈ T₁
           *     ------------------------------------------------ TApp
           *              Γ₁, Γ₂ |- func(arg) ∈ T₂(arg)
           *
           * First inference returns the function type as payload. Once it is
           * known to be a Π-type, checking the argument returns its proof.
           * `resultType` is then threaded out with the TApp justification.
           */
          case Sapp(func: Expr[Ind], tm2: Expr[Ind]) =>
            inferProofM(using SetTheoryLibrary)(localContext, func, memo).flatMap { (funcType, funcTyping) =>
              funcType match
                case SPi(ty1: Expr[Ind], _: Abs[?, ?]) =>
                  checkProofM(using SetTheoryLibrary)(localContext, tm2, ty1, memo).flatMap { (_, argTyping) =>
                    applicationProof(func, tm2, funcType)(funcTyping, argTyping)
                  }
                case SPi(_, ty2) => failWith(s"Inferred type T2($ty2) is not a lambda expression")
                case _ => failWith(s"$funcType must be a Π-type")
            }

          /**
           * Abstraction:
           *
           *     Γ, x ∈ T₁ |- body ∈ T₂
           *     ------------------------- implication, forall, TAbs
           *     Γ |- λ(x : T₁). body ∈ Π(x : T₁). T₂
           *
           * Body inference directly supplies `T₂`; no theorem inspection is
           * needed. The temporary binder assumption is discharged before the
           * abstraction type and proof are returned together.
           */
          case Sabs(ty: Expr[Ind], Abs(boundVar: Variable[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            inferProofM(using SetTheoryLibrary)(newContext, body, memo).flatMap { (bodyType, bodyTyping) =>
              abstractionProof(boundVar, ty, body, bodyType)(bodyTyping)
            }

          /**
           * Dependent product formation:
           *
           *     Γ, x ∈ T₁ |- T₂(x) ∈ U₂    Umin ⊆ Umax
           *     ---------------------------------------- universe Π-closure
           *              Γ |- Π(x : T₁). T₂(x) ∈ Umax
           *
           * Body inference carries `U₂`. `U₁` comes from the local context
           * when available, otherwise from `universeOf(T₁)`. The larger
           * universe becomes this branch's inferred-type payload.
           */
          case SPi(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            inferProofM(using SetTheoryLibrary)(newContext, body, memo).flatMap { (u2, bodyTyping) =>
              val (u1, u1Fact, u1Premises) = localContext
                .collectFirst {
                  case typeOf(s, u) if isSame(s, ty) => (u, None, Set(isUniverse(u), ty ∈ u))
                }
                .getOrElse {
                  (universeOf(ty), Some(universeOfIsUniverse of (x := ty)), Set())
                }
              val (maxU, minU, closureThm) =
                if getDepth(u1) > getDepth(u2) then (u1, u2, universeHierarchyPiClosureRight)
                else (u2, u1, universeHierarchyPiClosureLeft)
              subsetProof(using SetTheoryLibrary)(localContext, minU, maxU).flatMap { (_, subRel) =>
                val resetBot = bodyTyping.statement -<< (boundVar ∈ ty)
                have((boundVar ∈ ty |- body ∈ u2) ++<< bodyTyping.statement) by Weakening(bodyTyping)
                thenHave((boundVar ∈ ty ==> body ∈ u2) ++<< resetBot) by RightImplies
                thenHave((∀(boundVar ∈ ty, body ∈ u2)) ++<< resetBot) by RightForall
                val quantifiedBody = lastStep
                val closure = closureThm of (T1 := ty, T2 := Abs(boundVar, body), U1 := u1, U2 := u2)
                val closed = have(Discharge(quantifiedBody, subRel)(closure))
                val withUniverse = u1Fact.fold(closed): fact =>
                  val universe = conjunct(fact, takeLeft = true)
                  val membership = conjunct(fact, takeLeft = false)
                  have(Discharge(universe, membership)(closed))
                val typing = have(((u1Premises ++ Set(isUniverse(u2)) |- tm ∈ maxU) ++<< resetBot)) by Weakening(withUniverse)
                ProofJudgement(typing).map(_ => maxU)
              }
            }

          /** Typed constants already carry both parts of the inference result. */
          case tCst: TypedConstant => ProofJudgement(tCst.justif).map(_ => tCst.typ)

          /**
           * Fully applied type-level constants use their quantified typing
           * theorem. Instantiating its binders yields
           *
           *     requirements(args) |- tm ∈ outType(args)
           *
           * and `outType(args)` is returned as payload.
           */
          case Multiapp(func, args: List[Expr[Ind]] @unchecked) if args.forall(_.sort == K.Ind) =>
            func match
              case tcf: TypedConstantFunctional[?] =>
                if tcf.arity != args.size then
                  throw new IllegalArgumentException(
                    "computeType can only handle fully applied functions. Function " + tcf + " has arity " + tcf.arity + " but was applied to " + args.size + " arguments."
                  )
                val subst = (tcf.typ.args zip args).map((v, a) => (v := a))
                val instance = args.foldLeft(tcf.justif.statement.right.head) {
                  case (forall(v, body), arg) => body.substitute(v := arg)
                  case _ => failWith(s"Typing theorem for $tcf does not quantify all type arguments.")
                }
                val instantiated =
                  if args.isEmpty then have(tcf.justif)
                  else have(instance) by InstantiateForall(args*)(tcf.justif)
                val resultType = tcf.typ.outTyp.substitute(subst*)
                val typing = tm ∈ resultType
                def conjuncts(formula: Expr[Prop]): Set[Expr[Prop]] = formula match
                  case left /\ right => conjuncts(left) union conjuncts(right)
                  case _ => Set(formula)
                @annotation.tailrec
                def antecedents(formula: Expr[Prop], acc: Set[Expr[Prop]] = Set.empty): (Set[Expr[Prop]], Expr[Prop]) =
                  formula match
                    case premise ==> result => antecedents(result, acc union conjuncts(premise))
                    case result => acc -> result
                val (requirements, result) = antecedents(instance)
                if !isSame(result, typing) then failWith(s"Instantiated typing theorem for $tcf concludes $result instead of $typing.")
                val baseTyping = have(requirements |- typing) by Restate.from(instantiated)
                val typingProof = have((localContext ++ requirements) |- typing) by Weakening(baseTyping)
                ProofJudgement(typingProof).map(_ => resultType)

              case _ => inferAtomic(localContext, tm)

          case _ => inferAtomic(localContext, tm)
        }
      }

    /**
     * Infer a non-structural term from the local context. If no assignment is
     * known, TSort provides the conservative universe type.
     */
    private def inferAtomic(using lib: SetTheoryLibrary.type, proof: Proof)(
        localContext: Set[Expr[Prop]],
        tm: Expr[Ind]
    ): ProofCarrier[Expr[Ind]] =
      import lib.*
      localContext.collectFirst { case typeOf(t1, t2) if isSame(t1, tm) => t2 } match
        case Some(ty) =>
          val typing = have(tm ∈ ty |- tm ∈ ty) by Hypothesis
          ProofJudgement(typing).map(_ => ty)
        case None =>
          val ty = universeOf(tm)
          val typing = have(TSort of (U := tm))
          ProofJudgement(typing).map(_ => ty)

    /** Infer the type of the given term (↑), discarding the internal payload. */
    def inferProof(using lib: SetTheoryLibrary.type, proof: Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind]): ProofJudgement =
      inferProofM(using lib, proof)(localContext, tm, Memo()).judgement

    /**
     * Check the type of the given term(↓)
     */
    def checkProof(using lib: SetTheoryLibrary.type, proof: Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind]): ProofJudgement =
      checkProofM(using lib, proof)(localContext, tm, ty, Memo())

    private def checkProofM(using lib: SetTheoryLibrary.type, proof: Proof)(
        localContext: Set[Expr[Prop]],
        tm: Expr[Ind],
        ty: Expr[Ind],
        memo: Memo
    ): ProofJudgement =
      memo.check(localContext, tm, ty) {
        import lib.*
        SubproofM {
        (tm, ty) match
          /**
           * Bidirectional abstraction check:
           *
           *     Γ, x ∈ T₁ |- body ∈ T₂(x)
           *     ----------------------------- TAbs
           *     Γ |- λ(x : T₁). body ∈ Π(x : T₁). T₂(x)
           *
           * The expected Π-type supplies the codomain, so only the body needs
           * recursive checking. Its carrier threads the proof into this step.
           */
          case (Sabs(ty1: Expr[Ind], body: Expr[Ind >>: Ind]), SPi(ty1prime: Expr[Ind], ty2: Expr[Ind >>: Ind])) =>
            val (newBoundVariable, replaceVar, body1, body2) = (body, ty2) match
              case (Abs(v1, b1), Abs(v2, b2)) => (v1, v2, b1, b2)
              case _ => failWith("Term and Type must be lambda expressions")
            have(ty1 === ty1prime) by RightRefl.withParameters(ty1 === ty1prime)
            val newContext = localContext ++ Set(newBoundVariable ∈ ty1)
            val newBody2 = body2.substitute((replaceVar, newBoundVariable))
            checkProofM(using SetTheoryLibrary)(newContext, body1, newBody2, memo).flatMap { (_, bodyTyping) =>
              val resetBot = bodyTyping.statement -<< (newBoundVariable ∈ ty1)
              have((newBoundVariable ∈ ty1 |- body1 ∈ newBody2) ++<< bodyTyping.statement) by Weakening(bodyTyping)
              thenHave((newBoundVariable ∈ ty1 ==> body1 ∈ newBody2) ++<< resetBot) by RightImplies
              thenHave((∀(newBoundVariable ∈ ty1, body1 ∈ newBody2)) ++<< resetBot) by RightForall
              val quantifiedTyping = lastStep
              val abstraction = TAbs of (T1 := ty1, T2 := ty2, e := body)
              val typing = have(Discharge(quantifiedTyping)(abstraction))
              ProofJudgement(typing)
            }

          /**
           * Conversion check:
           *
           *     Γ₁ |- tm ∈ inferredType    Γ₂ |- inferredType ⊆ expectedType
           *     ------------------------------------------------------------ TConvAdv
           *                   Γ₁, Γ₂ |- tm ∈ expectedType
           *
           * Reuse the inferred typing when its type matches; restate equivalent
           * types and construct a conversion only for a genuine inclusion.
           */
          case _ =>
            inferProofM(using SetTheoryLibrary)(localContext, tm, memo).flatMap { (inferredType, inferredTyping) =>
              if inferredType == ty then ProofJudgement(inferredTyping)
              else if isSame(inferredType, ty) then
                val typing = have((tm ∈ ty) ++<< inferredTyping.statement) by Restate.from(inferredTyping)
                ProofJudgement(typing)
              else
                subsetProof(using SetTheoryLibrary)(localContext, inferredType, ty).flatMap { (_, conversion) =>
                  val statement = (tm ∈ ty) ++<< inferredTyping.statement ++<< conversion.statement
                  val inferredTypingFormula = tm ∈ inferredType
                  val conversionFormula = inferredType ⊆ ty
                  val rule = TConvAdv of (e1 := tm, T := inferredType, T1 := ty)
                  val withInference = have(((tm ∈ ty) +<< conversionFormula) ++<< inferredTyping.statement) by
                    Cut.withParameters(inferredTypingFormula)(inferredTyping, rule)
                  val typing = have(statement) by Cut.withParameters(conversionFormula)(conversion, withInference)
                  ProofJudgement(typing)
                }
            }
        }
      }

    /** Prove type inclusion, handling reflexivity before dependent covariance. */
    def subsetProof(using lib: SetTheoryLibrary.type, proof: Proof)(localContext: Set[Expr[Prop]], sub: Expr[Ind], sup: Expr[Ind]): ProofJudgement =
      import lib.*
      Subproof {
        (sub, sup) match
          case _ if sub == sup => have(reflexivity of (x := sub))
          case (SPi(d1: Expr[Ind], Abs(v1: Expr[Ind], c1: Expr[Ind])), SPi(d2: Expr[Ind], Abs(v2: Expr[Ind], c2: Expr[Ind]))) =>
            val domainEquiv = have(d1 === d2) by RightRefl.withParameters(d1 === d2)
            val c2Replace = c2.substitute((v1, v2))
            val newContext = localContext ++ Set(v1 ∈ d1)
            val codomainProof = subsetProof(using SetTheoryLibrary)(newContext, c1, c2Replace)
            if !codomainProof.isValid then failWith(s"Cannot prove codomain covariance: '${c1} ⊆ ${c2Replace}' for variable ${v1}.")
            val h1 = have(codomainProof)
            have(h1)
            thenHave((v1 ∈ d1 ==> c1 ⊆ c2Replace) ++<< h1.statement) by Weakening
            thenHave(∀(v1 ∈ d1, c1 ⊆ c2Replace) ++<< h1.statement) by RightForall
            val quantifiedCovariance = lastStep
            val covariance = piCovariance of (T := d1, T1 := d2, T2 := Abs(v1, c1), T2p := Abs(v2, c2))
            have(Discharge(domainEquiv, quantifiedCovariance)(covariance))
          case _ =>
            val dSub = getDepth(sub)
            val dSup = getDepth(sup)
            if (dSub > dSup) then failWith(s"Depth mismatch: $sub (d=$dSub) cannot be subset of $sup (d=$dSup)")
            else if (dSub == dSup) then
              if (localContext.contains(sub ⊆ sup)) then have(sub ⊆ sup |- sub ⊆ sup) by Hypothesis
              else
                val equality = have(sub === sup) by RightRefl.withParameters(sub === sup)
                val reflexive = have(reflexivity of (x := sub))
                val rewritten = have(sub === sup |- sub ⊆ sup) by
                  RightSubstEq.withParameters(List((sub, sup)), (Seq(T), sub ⊆ T))(reflexive)
                have(Discharge(equality)(rewritten))
            else if (dSub == dSup - 1) then have(subsetOfUniverse of (A := sub))
            else
              val step1 = have(subsetOfUniverse of (A := sub))
              val step2Proof = subsetProof(using SetTheoryLibrary)(localContext, universeOf(sub), sup)
              if !step2Proof.isValid then failWith(s"Further subset proof failed: ${universeOf(sub)} and $sup")
              val step2 = have(step2Proof)
              val transitive = transitivity of (x := sub, y := universeOf(sub), z := sup)
              have(Discharge(step1, step2)(transitive))
      }
