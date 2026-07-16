package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.utilcfs.K
import lisa.maths.SetTheory.Base.Subset.doubleInclusion
import lisa.maths.SetTheory.Base.Subset.reflexivity
import lisa.maths.SetTheory.Base.Subset.transitivity
import lisa.maths.SetTheory.Cardinal.Predef.isUniverse
import lisa.maths.SetTheory.Cardinal.Predef.universeOf
import lisa.maths.SetTheory.Cardinal.Predef.universeOfIsUniverse
import lisa.maths.SetTheory.Functions.Predef._
import lisa.utilcfs.fol.{FOL => F}
import lisa.utilcfs.prooflib.Exports.*
import lisa.utilcfs.prooflib.ProofJudgement
import lisa.utilcfs.prooflib.Subproof
import lisa.utilcfs.prooflib.TacticHelpers.failWith

import scala.collection.Set

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
    // Helper function: get universe level
    def getDepth(e: Expr[Ind]): Int = e match
      case App(universeOf, inner: Expr[Ind]) => 1 + getDepth(inner)
      case _ => 1

    // Bidirectional type checking proof construct(infer, check, equal)
    def prove(using lib: SetTheoryLibrary.type, proof: lib.Proof)(bot: F.Sequent): ProofJudgement =
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
              val allFacts = Seq(stmt) ++ lemmaFacts
              have(stmt.statement.removeAllLeft(toEliminate)) by Tautology.from(allFacts*)
              thenHave(premises |- tm ∈ ty) by Weakening
            case _ => failWith("Type check can only check type relation(∈)")
        }

    def apply(using lib: SetTheoryLibrary.type, proof: lib.Proof)(bot: F.Sequent): ProofJudgement =
      prove(bot)

    /**
     * Infer the type of the given term(↑)
     */
    def inferProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind]): ProofJudgement =
      import lib.*
      // println("Infer term:" + tm.toString())
      Subproof {
        tm match
          // e1: Π(x:T1).T2, e2: T1 => e1(e2): T2(e2)
          case Sapp(func: Expr[Ind], tm2: Expr[Ind]) =>
            val funcProof = inferProof(using SetTheoryLibrary)(localContext, func)
            if !funcProof.isValid then failWith(s"Failed to infer the type of the given func($func)")
            val h1 = have(funcProof)
            val funcInferredType = h1.statement.right.head match
              case typeOf(tm, ty) => ty
              case _ => failWith("Failed to extract the inferred type from valid proof")
            funcInferredType match // func's type must be Π-class
              case SPi(ty1: Expr[Ind], ty2: Expr[Ind >>: Ind]) =>
                val typeLevelProof = checkProof(using SetTheoryLibrary)(localContext, tm2, ty1)
                if !typeLevelProof.isValid then failWith(s"Failed to construct the proof of $tm2 ∈ $ty1")
                val h2 = have(typeLevelProof)
                val (boundVar, typeBody) = ty2 match
                  case Abs(v, body) => (v, body)
                  case _ => failWith(s"Inferred type T2($ty2) is not a lambda expression")
                val statement = (tm ∈ typeBody.substitute((boundVar, tm2))) ++<< h1.statement ++<< h2.statement
                have(statement) by Tautology.from(h1, h2, TApp of (e1 := func, e2 := tm2, T1 := ty1, T2 := ty2))
              case _ => failWith(s"$funcInferredType must be a Π-type")

          // ∀(x ∈ T1, e(x) ∈ T2(x)) => abs(T1)(e) ∈ Pi(T1)(T2)
          case Sabs(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            val bodyProof = inferProof(using SetTheoryLibrary)(newContext, body)
            if !bodyProof.isValid then failWith(s"Sabs: Failed to infer the type of the given body($body)")
            val h1 = have(bodyProof)
            val bodyInferredType = h1.statement.right.head match
              case typeOf(tm, ty) => ty
              case _ => failWith("Sabs: Failed to extract the inferred type from valid proof")
            val resetBot = h1.statement -<< (boundVar ∈ ty)
            have((boundVar ∈ ty |- body ∈ bodyInferredType) ++<< h1.statement) by Weakening(h1)
            thenHave((boundVar ∈ ty ==> body ∈ bodyInferredType) ++<< resetBot) by RightImplies
            thenHave((∀(boundVar ∈ ty, body ∈ bodyInferredType)) ++<< resetBot) by RightForall
            thenHave((tm ∈ Pi(ty)(λ(boundVar, bodyInferredType))) ++<< resetBot) by Tautology.fromLastStep(
              TAbs of (T1 := ty, T2 := Abs(boundVar, bodyInferredType), e := Abs(boundVar, body))
            )

          // Π(x: T1).T2 : U, select the relative bigger type as the final product's type
          case SPi(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            val bodyProof = inferProof(using SetTheoryLibrary)(newContext, body)
            if !bodyProof.isValid then failWith(s"SPi: Failed to infer the type of the given body($body)")
            val h1 = have(bodyProof)
            val u2 = h1.statement.right.head match
              case typeOf(tm, ty) => ty
              case _ => failWith("SPi: Failed to extract the inferred type from valid proof")
            val (u1, u1Facts, u1Primises) = localContext
              .collectFirst {
                case typeOf(s, u) if s == ty => (u, Seq(), Set(isUniverse(u), ty ∈ u))
              }
              .getOrElse {
                (universeOf(ty), Seq(universeOfIsUniverse of (x := ty)), Set())
              }
            val (maxU, minU, closureThm) =
              if getDepth(u1) > getDepth(u2) then (u1, u2, universeHierarchyPiClosureRight)
              else (u2, u1, universeHierarchyPiClosureLeft)
            val subProof = subsetProof(using SetTheoryLibrary)(localContext, minU, maxU)
            if !subProof.isValid then failWith(s"SPi: Subset proof failed: $minU <= $maxU")
            val resetBot = h1.statement -<< (boundVar ∈ ty)
            val subRel = have(subProof)
            have((boundVar ∈ ty |- body ∈ u2) ++<< h1.statement) by Weakening(h1)
            thenHave((boundVar ∈ ty ==> body ∈ u2) ++<< resetBot) by RightImplies
            thenHave((∀(boundVar ∈ ty, body ∈ u2)) ++<< resetBot) by RightForall
            thenHave((u1Primises ++ Set(isUniverse(u2)) |- tm ∈ maxU) ++<< resetBot) by Tautology.fromLastStep(
              Seq(closureThm of (T1 := ty, T2 := Abs(boundVar, body), U1 := u1, U2 := u2), subRel) ++ u1Facts*
            )

          // Other cases, like single variable
          case tCst: TypedConstant => have(tCst.justif)
          case Multiapp(func, args: List[Expr[Ind]] @unchecked) if args.forall(_.sort == K.Ind) =>
            func match
              case tcf: TypedConstantFunctional[?] =>
                if tcf.arity != args.size then
                  throw new IllegalArgumentException(
                    "computeType can only handle fully applied functions. Function " + tcf + " has arity " + tcf.arity + " but was applied to " + args.size + " arguments."
                  )
                val subst = (tcf.typ.args zip args).map((v, a) => (v := a))
                have(tm ∈ tcf.typ.outTyp.substitute(subst*) ++<< (() |- localContext)) by Tautology.from(tcf.justif.of(subst*))

              case _ =>
                val tyOpt: Option[Expr[Ind]] = localContext.collectFirst { case typeOf(t1, t2) if t1 == tm => t2 }
                tyOpt match
                  case Some(ty) => have(tm ∈ ty |- tm ∈ ty) by Hypothesis
                  case None => have(tm ∈ universeOf(tm)) by Tautology.from(TSort of (U := tm))

          case _ =>
            val tyOpt: Option[Expr[Ind]] = localContext.collectFirst { case typeOf(t1, t2) if t1 == tm => t2 }
            tyOpt match
              case Some(ty) => have(tm ∈ ty |- tm ∈ ty) by Hypothesis
              case None => have(tm ∈ universeOf(tm)) by Tautology.from(TSort of (U := tm))
      }

    /**
     * Check the type of the given term(↓)
     */
    def checkProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind]): ProofJudgement =
      import lib.*
      // println("Check term's type: " + tm.toString() + " ∈ " + ty.toString())
      Subproof {
        (tm, ty) match
          // ∀(x ∈ T1, e(x) ∈ T2(x)) => abs(T1)(e) ∈ Pi(T1)(T2)
          case (Sabs(ty1: Expr[Ind], body: Expr[Ind >>: Ind]), SPi(ty1prime: Expr[Ind], ty2: Expr[Ind >>: Ind])) =>
            val (newBoundVariable, replaceVar, body1, body2) = (body, ty2) match
              case (Abs(v1, b1), Abs(v2, b2)) => (v1, v2, b1, b2)
              case _ => failWith("Term and Type must be lambda expressions")
            have(ty1 === ty1prime) by RightRefl.withParameters(ty1 === ty1prime)
            val newContext = localContext ++ Set(newBoundVariable ∈ ty1)
            val newBody2 = body2.substitute((replaceVar, newBoundVariable))
            val bodyProof = checkProof(using SetTheoryLibrary)(newContext, body1, newBody2)
            if bodyProof.isValid then
              val h1 = have(bodyProof)
              val resetBot = h1.statement -<< (newBoundVariable ∈ ty1)
              have((newBoundVariable ∈ ty1 |- body1 ∈ newBody2) ++<< h1.statement) by Weakening(h1)
              thenHave((newBoundVariable ∈ ty1 ==> body1 ∈ newBody2) ++<< resetBot) by RightImplies
              thenHave((∀(newBoundVariable ∈ ty1, body1 ∈ newBody2)) ++<< resetBot) by RightForall
              thenHave((tm ∈ ty) ++<< resetBot) by Tautology.fromLastStep(
                TAbs of (T1 := ty1, T2 := ty2, e := body)
              )
            else failWith("Failed to construct body proof")

          // e ∈ T, T === T' -> e ∈ T' for other cases
          case _ =>
            val inferredProof = inferProof(using SetTheoryLibrary)(localContext, tm)
            if !inferredProof.isValid then failWith(s"Failed to construct the inference proof for $tm")
            val h1 = have(inferredProof)
            val inferredType = h1.statement.right.head match
              case typeOf(tm, ty) => ty
              case _ => failWith("Failed to extract the inferred type from valid proof")
            val convProof = subsetProof(using SetTheoryLibrary)(localContext, inferredType, ty)
            if !convProof.isValid then failWith(s"Failed to construct the equivalence proof for $inferredType and $ty")
            val h2 = have(convProof)
            val statement = (tm ∈ ty) ++<< h1.statement ++<< h2.statement
            have(statement) by Tautology.from(
              h1,
              h2,
              TConvAdv of (
                e1 := tm,
                T := inferredType,
                T1 := ty
              )
            )
      }

    // Construct subset proof(ty1 ⊆ ty2) for the given two expressions
    def subsetProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], sub: Expr[Ind], sup: Expr[Ind]): ProofJudgement =
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
