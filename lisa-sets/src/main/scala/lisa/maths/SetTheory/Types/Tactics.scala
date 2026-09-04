package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.maths.SetTheory.Base.Subset.doubleInclusion
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
import lisa.utils.prooflib.TacticHelpers.failWith

import scala.collection.Set
import scala.collection.mutable

import F.{∀ => _, _}
import TypingRules.TAbs
import TypingRules.TApp
import TypingRules.TSort
import TypingRules.TConvAdv
import TypingHelpers._
import TypingTheorems.universeHierarchyPiClosureLeft
import TypingTheorems.universeHierarchyPiClosureRight
import TypingTheorems.subsetOfUniverse
import TypingTheorems.piCovariance

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
              have(Discharge(lemmaFacts*)(stmt))
              thenHave(stmt.statement.removeAllLeft(toEliminate)) by Restate
              thenHave(premises |- tm ∈ ty) by Weakening
            case _ => failWith("Type check can only check type relation(∈)")
        }

    def apply(using lib: SetTheoryLibrary.type, proof: Proof)(bot: F.Sequent): ProofJudgement =
      prove(bot)

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
                case SPi(ty1: Expr[Ind], ty2 @ Abs(boundVar: Expr[Ind], typeBody: Expr[Ind])) =>
                  checkProofM(using SetTheoryLibrary)(localContext, tm2, ty1, memo).flatMap { (_, argTyping) =>
                    val resultType = typeBody.substitute(boundVar := tm2)
                    val statement = (tm ∈ resultType) ++<< funcTyping.statement ++<< argTyping.statement
                    val functionTyping = func ∈ funcType
                    val argumentTyping = tm2 ∈ ty1
                    val rule = TApp of (e1 := func, e2 := tm2, T1 := ty1, T2 := ty2)
                    val ruleResult = rule.statement.right.head
                    val withFunction = have((ruleResult +<< argumentTyping) ++<< funcTyping.statement) by
                      Cut.withParameters(functionTyping)(funcTyping, rule)
                    val applied = have((ruleResult ++<< funcTyping.statement) ++<< argTyping.statement) by
                      Cut.withParameters(argumentTyping)(argTyping, withFunction)
                    val typing = have(statement) by Restate(applied)
                    ProofJudgement(typing).map(_ => resultType)
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
          case Sabs(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            inferProofM(using SetTheoryLibrary)(newContext, body, memo).flatMap { (bodyType, bodyTyping) =>
              val resultType = Pi(ty)(λ(boundVar, bodyType))
              val resetBot = bodyTyping.statement -<< (boundVar ∈ ty)
              have((boundVar ∈ ty |- body ∈ bodyType) ++<< bodyTyping.statement) by Weakening(bodyTyping)
              thenHave((boundVar ∈ ty ==> body ∈ bodyType) ++<< resetBot) by RightImplies
              thenHave((∀(boundVar ∈ ty, body ∈ bodyType)) ++<< resetBot) by RightForall
              val typing = thenHave((tm ∈ resultType) ++<< resetBot) by Tautology.fromLastStep(
                TAbs of (T1 := ty, T2 := Abs(boundVar, bodyType), e := Abs(boundVar, body))
              )
              ProofJudgement(typing).map(_ => resultType)
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
              val (u1, u1Facts, u1Premises) = localContext
                .collectFirst {
                  case typeOf(s, u) if isSame(s, ty) => (u, Seq(), Set(isUniverse(u), ty ∈ u))
                }
                .getOrElse {
                  (universeOf(ty), Seq(universeOfIsUniverse of (x := ty)), Set())
                }
              val (maxU, minU, closureThm) =
                if getDepth(u1) > getDepth(u2) then (u1, u2, universeHierarchyPiClosureRight)
                else (u2, u1, universeHierarchyPiClosureLeft)
              subsetProof(using SetTheoryLibrary)(localContext, minU, maxU).flatMap { (_, subRel) =>
                val resetBot = bodyTyping.statement -<< (boundVar ∈ ty)
                have((boundVar ∈ ty |- body ∈ u2) ++<< bodyTyping.statement) by Weakening(bodyTyping)
                thenHave((boundVar ∈ ty ==> body ∈ u2) ++<< resetBot) by RightImplies
                thenHave((∀(boundVar ∈ ty, body ∈ u2)) ++<< resetBot) by RightForall
                val typing = thenHave((u1Premises ++ Set(isUniverse(u2)) |- tm ∈ maxU) ++<< resetBot) by Tautology.fromLastStep(
                  Seq(closureThm of (T1 := ty, T2 := Abs(boundVar, body), U1 := u1, U2 := u2), subRel) ++ u1Facts*
                )
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
          val typing = have(tm ∈ ty) by Restate.from(TSort of (U := tm))
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
              val typing = thenHave((tm ∈ ty) ++<< resetBot) by Tautology.fromLastStep(
                TAbs of (T1 := ty1, T2 := ty2, e := body)
              )
              ProofJudgement(typing)
            }

          /**
           * Conversion check:
           *
           *     Γ₁ |- tm ∈ inferredType    Γ₂ |- inferredType ⊆ expectedType
           *     ------------------------------------------------------------ TConvAdv
           *                   Γ₁, Γ₂ |- tm ∈ expectedType
           *
           * `inferProofM` supplies `inferredType` as payload and its typing
           * theorem as justification. Both flow directly into conversion.
           */
          case _ =>
            inferProofM(using SetTheoryLibrary)(localContext, tm, memo).flatMap { (inferredType, inferredTyping) =>
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

    // Construct subset proof(ty1 ⊆ ty2) for the given two expressions
    def subsetProof(using lib: SetTheoryLibrary.type, proof: Proof)(localContext: Set[Expr[Prop]], sub: Expr[Ind], sup: Expr[Ind]): ProofJudgement =
      import lib.*
      // println("Trying to construct subsetProof for: " + sub.toString() + " ⊆ " + sup.toString())
      Subproof {
        (sub, sup) match
          case (SPi(d1: Expr[Ind], Abs(v1: Expr[Ind], c1: Expr[Ind])), SPi(d2: Expr[Ind], Abs(v2: Expr[Ind], c2: Expr[Ind]))) =>
            val domainEquiv = have(d1 === d2) by RightRefl.withParameters(d1 === d2)
            val c2Replace = c2.substitute((v1, v2))
            val newContext = localContext ++ Set(v1 ∈ d1)
            val codomainProof = subsetProof(using SetTheoryLibrary)(newContext, c1, c2Replace)
            if !codomainProof.isValid then failWith(s"Cannot prove codomain covariance: '${c1} ⊆ ${c2Replace}' for variable ${v1}.")
            val h1 = have(codomainProof)
            have(c1 ⊆ c2Replace ++<< h1.statement) by Tautology.from(have(codomainProof))
            thenHave((v1 ∈ d1 ==> c1 ⊆ c2Replace) ++<< h1.statement) by Weakening
            thenHave(∀(v1 ∈ d1, c1 ⊆ c2Replace) ++<< h1.statement) by RightForall
            thenHave(sub ⊆ sup ++<< h1.statement) by Tautology.fromLastStep(domainEquiv, piCovariance of (T := d1, T1 := d2, T2 := Abs(v1, c1), T2p := Abs(v2, c2)))
          case _ =>
            val dSub = getDepth(sub)
            val dSup = getDepth(sup)
            if (dSub > dSup) then failWith(s"Depth mismatch: $sub (d=$dSub) cannot be subset of $sup (d=$dSup)")
            else if (dSub == dSup) then
              if (localContext.contains(sub ⊆ sup)) then have(sub ⊆ sup |- sub ⊆ sup) by Hypothesis
              else if (sub == sup) then have(sub ⊆ sup) by Tautology.from(reflexivity of (x := sub))
              else
                have(sub === sup) by RightRefl.withParameters(sub === sup)
                thenHave(sub ⊆ sup) by Tautology.fromLastStep(doubleInclusion of (x := sub, y := sup))
            else if (dSub == dSup - 1) then have(sub ⊆ universeOf(sub)) by Tautology.from(subsetOfUniverse of (A := sub))
            else
              val step1 = have(sub ⊆ universeOf(sub)) by Tautology.from(subsetOfUniverse of (A := sub))
              val step2Proof = subsetProof(using SetTheoryLibrary)(localContext, universeOf(sub), sup)
              if !step2Proof.isValid then failWith(s"Further subset proof failed: ${universeOf(sub)} and $sup")
              val step2 = have(step2Proof)
              have(sub ⊆ sup) by Tautology.from(
                step1,
                step2,
                transitivity of (x := sub, y := universeOf(sub), z := sup)
              )
      }
