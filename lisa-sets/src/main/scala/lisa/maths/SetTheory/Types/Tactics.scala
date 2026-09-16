package lisa.maths.SetTheory.Types

import lisa.SetTheoryLibrary
import lisa.utils.K
import lisa.maths.SetTheory.Base.Subset.reflexivity
import lisa.maths.SetTheory.Base.Subset.transitivity
import lisa.maths.SetTheory.Cardinal.Predef.isUniverse
import lisa.maths.SetTheory.Cardinal.Predef.universeOf
import lisa.maths.SetTheory.Cardinal.Predef.universeOfIsUniverse
import lisa.maths.SetTheory.Functions.Predef._
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.SimpleDeducedSteps._
import lisa.utils.prooflib.ProofTacticLib._

import scala.collection.Set

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

  object Typecheck extends ProofTactic:
    /** Extract a proved conjunct with explicit sequent steps. */
    private def conjunct(using lib: SetTheoryLibrary.type, proof: lib.Proof)(fact: proof.Fact, takeLeft: Boolean): proof.Fact =
      import lib.*
      fact.statement.right.head match
        case conjunction @ (left /\ right) =>
          val selected = if takeLeft then left else right
          val hypothesis = have((fact.statement.left ++ Set(left, right)) |- selected) by Hypothesis
          val fromConjunction = have((fact.statement.left + conjunction) |- selected) by
            LeftAnd.withParameters(left, right)(hypothesis)
          have(fact.statement.left |- selected) by Cut.withParameters(conjunction)(fact, fromConjunction)
        case _ => throw new IllegalArgumentException(s"Expected a proved conjunction, got ${fact.statement}")

    /** Cache only derivations whose imports are reusable library justifications. */
    private final class Memo:
      private case class Fragment(bot: F.Sequent, steps: Seq[K.SCProofStep], imports: Seq[SetTheoryLibrary.JUSTIFICATION])
      private val entries = scala.collection.mutable.HashMap.empty[(Set[Long], Long, Option[Long]), Fragment]

      def reuse(using lib: SetTheoryLibrary.type, proof: lib.Proof)(
          context: Set[Expr[Prop]], term: Expr[Ind], expected: Option[Expr[Ind]]
      )(compute: => proof.ProofTacticJudgement): proof.ProofTacticJudgement =
        val key = (context.map(_.underlying.uniqueNumber), term.underlying.uniqueNumber, expected.map(_.underlying.uniqueNumber))
        entries.get(key) match
          case Some(fragment) => proof.ValidProofTactic(fragment.bot, fragment.steps, fragment.imports)(using Typecheck)
          case None =>
            val result = compute
            result match
              case valid: proof.ValidProofTactic =>
                val imports = valid.imports.collect { case justification: SetTheoryLibrary.JUSTIFICATION => justification }
                // Never carry an outer proof's local indices into a sibling subproof.
                if imports.size == valid.imports.size then entries(key) = Fragment(valid.bot, valid.scps, imports)
              case _ => ()
            result

    // Helper function: get universe level
    def getDepth(e: Expr[Ind]): Int = e match
      case App(universeOf, inner: Expr[Ind]) => 1 + getDepth(inner)
      case _ => 1

    // Bidirectional type checking proof construct(infer, check, equal)
    def prove(using lib: SetTheoryLibrary.type, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
      import lib.*
      if (bot.right.size != 1) return proof.InvalidProofTactic("Typecheck cannot prove a sequent with multiple disjuncts in the conclusion.")
      val premises = bot.left
      val goal = bot.right.head
      TacticSubproof {
        goal match
          case typeOf(tm, ty) =>
            val innerProof = checkProof(using SetTheoryLibrary)(premises, tm, ty)
            val stmt = have(innerProof)
            val (toEliminate, toKeep) = stmt.bot.left.partition {
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
            have(stmt.bot.removeAllLeft(toEliminate)) by Weakening(cleaned)
            thenHave(premises |- tm ∈ ty) by Weakening
          case _ => return proof.InvalidProofTactic("Type check can only check type relation(∈)")
      }

    /**
     * Infer the type of the given term(↑)
     */
    def inferProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind]): proof.ProofTacticJudgement =
      inferMemo(localContext, tm, new Memo)

    private def inferMemo(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], memo: Memo): proof.ProofTacticJudgement =
      memo.reuse(localContext, tm, None)(inferUncached(localContext, tm, memo))

    private def inferUncached(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], memo: Memo): proof.ProofTacticJudgement =
      import lib.*
      TacticSubproof { ip ?=>
        ip.cleanAssumptions
        tm match
          // e1: Π(x:T1).T2, e2: T1 => e1(e2): T2(e2)
          case Sapp(func: Expr[Ind], tm2: Expr[Ind]) =>
            val funcProof = inferMemo(using SetTheoryLibrary)(localContext, func, memo)
            if !funcProof.isValid then return proof.InvalidProofTactic(s"Failed to infer the type of the given func($func)")
            val h1 = have(funcProof)
            val funcInferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Failed to extract the inferred type from valid proof")
            funcInferredType match // func's type must be Π-class
              case SPi(ty1: Expr[Ind], ty2: Expr[Ind >>: Ind]) =>
                val typeLevelProof = checkMemo(using SetTheoryLibrary)(localContext, tm2, ty1, memo)
                if !typeLevelProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the proof of $tm2 ∈ $ty1")
                val h2 = have(typeLevelProof)
                val (boundVar, typeBody) = ty2 match
                  case Abs(v, body) => (v, body)
                  case _ => return proof.InvalidProofTactic(s"Inferred type T2($ty2) is not a lambda expression")
                val statement = (tm ∈ typeBody.substitute((boundVar, tm2))) ++<< h1.bot ++<< h2.bot
                val rule = TApp of (e1 := func, e2 := tm2, T1 := ty1, T2 := ty2)
                val ruleResult = rule.statement.right.head
                val withFunction = have((ruleResult +<< (tm2 ∈ ty1)) ++<< h1.bot) by
                  Cut.withParameters(func ∈ funcInferredType)(h1, rule)
                val applied = have((ruleResult ++<< h1.bot) ++<< h2.bot) by
                  Cut.withParameters(tm2 ∈ ty1)(h2, withFunction)
                have(statement) by Restate.from(applied)
              case _ => return proof.InvalidProofTactic(s"$funcInferredType must be a Π-type")

          // ∀(x ∈ T1, e(x) ∈ T2(x)) => abs(T1)(e) ∈ Pi(T1)(T2)
          case Sabs(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            val bodyProof = inferMemo(using SetTheoryLibrary)(newContext, body, memo)
            if !bodyProof.isValid then return proof.InvalidProofTactic(s"Sabs: Failed to infer the type of the given body($body)")
            val h1 = have(bodyProof)
            val bodyInferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Sabs: Failed to extract the inferred type from valid proof")
            val resetBot = h1.bot -<< (boundVar ∈ ty)
            have((boundVar ∈ ty |- body ∈ bodyInferredType) ++<< h1.bot) by Weakening(h1)
            thenHave((boundVar ∈ ty ==> body ∈ bodyInferredType) ++<< resetBot) by RightImplies
            thenHave((∀(boundVar ∈ ty, body ∈ bodyInferredType)) ++<< resetBot) by RightForall
            val quantifiedTyping = lastStep
            val abstraction = TAbs of (T1 := ty, T2 := Abs(boundVar, bodyInferredType), e := Abs(boundVar, body))
            have(Discharge(quantifiedTyping)(abstraction))

          // Π(x: T1).T2 : U, select the relative bigger type as the final product's type
          case SPi(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            val bodyProof = inferMemo(using SetTheoryLibrary)(newContext, body, memo)
            if !bodyProof.isValid then return proof.InvalidProofTactic(s"SPi: Failed to infer the type of the given body($body)")
            val h1 = have(bodyProof)
            val u2 = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"SPi: Failed to extract the inferred type from valid proof")
            val (u1, u1Facts, u1Premises) = localContext
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
            if !subProof.isValid then return proof.InvalidProofTactic(s"SPi: Subset proof failed: $minU <= $maxU")
            val resetBot = h1.bot -<< (boundVar ∈ ty)
            val subRel = have(subProof)
            have((boundVar ∈ ty |- body ∈ u2) ++<< h1.bot) by Weakening(h1)
            thenHave((boundVar ∈ ty ==> body ∈ u2) ++<< resetBot) by RightImplies
            thenHave((∀(boundVar ∈ ty, body ∈ u2)) ++<< resetBot) by RightForall
            val quantifiedBody = lastStep
            val closure = closureThm of (T1 := ty, T2 := Abs(boundVar, body), U1 := u1, U2 := u2)
            val closed = have(Discharge(quantifiedBody, subRel)(closure))
            val universeFacts = u1Facts.flatMap(fact => Seq(conjunct(fact, true), conjunct(fact, false)))
            val withUniverse = have(Discharge(universeFacts*)(closed))
            have((u1Premises ++ Set(isUniverse(u2)) |- tm ∈ maxU) ++<< resetBot) by Weakening(withUniverse)

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
                val resultType = tcf.typ.outTyp.substitute(subst*)
                val typing = tm ∈ resultType
                val instantiated = tcf.justif.of(args*)
                def conjuncts(formula: Expr[Prop]): Set[Expr[Prop]] = formula match
                  case left /\ right => conjuncts(left) union conjuncts(right)
                  case _ => Set(formula)
                @annotation.tailrec
                def antecedents(formula: Expr[Prop], acc: Set[Expr[Prop]] = Set.empty): (Set[Expr[Prop]], Expr[Prop]) =
                  formula match
                    case premise ==> result => antecedents(result, acc union conjuncts(premise))
                    case result => acc -> result
                val (requirements, result) = antecedents(instantiated.statement.right.head)
                if !isSame(result, typing) then return proof.InvalidProofTactic(s"Instantiated typing theorem for $tcf concludes $result instead of $typing.")
                val baseTyping = have(requirements |- typing) by Restate.from(instantiated)
                have((localContext ++ requirements) |- typing) by Weakening(baseTyping)

              case _ =>
                val tyOpt: Option[Expr[Ind]] = localContext.collectFirst { case typeOf(t1, t2) if isSame(t1, tm) => t2 }
                tyOpt match
                  case Some(ty) => have(tm ∈ ty |- tm ∈ ty) by Hypothesis
                  case None => have(tm ∈ universeOf(tm)) by Restate.from(TSort of (U := tm))

          case _ =>
            val tyOpt: Option[Expr[Ind]] = localContext.collectFirst { case typeOf(t1, t2) if isSame(t1, tm) => t2 }
            tyOpt match
              case Some(ty) => have(tm ∈ ty |- tm ∈ ty) by Hypothesis
              case None => have(tm ∈ universeOf(tm)) by Restate.from(TSort of (U := tm))
      }

    /**
     * Check the type of the given term(↓)
     */
    def checkProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind]): proof.ProofTacticJudgement =
      checkMemo(localContext, tm, ty, new Memo)

    private def checkMemo(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind], memo: Memo): proof.ProofTacticJudgement =
      memo.reuse(localContext, tm, Some(ty))(checkUncached(localContext, tm, ty, memo))

    private def checkUncached(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind], memo: Memo): proof.ProofTacticJudgement =
      import lib.*
      TacticSubproof { ip ?=>
        ip.cleanAssumptions
        (tm, ty) match
          // ∀(x ∈ T1, e(x) ∈ T2(x)) => abs(T1)(e) ∈ Pi(T1)(T2)
          case (Sabs(ty1: Expr[Ind], body: Expr[Ind >>: Ind]), SPi(ty1prime: Expr[Ind], ty2: Expr[Ind >>: Ind])) =>
            if !isSame(ty1, ty1prime) then return proof.InvalidProofTactic(s"Abstraction domains differ: $ty1 and $ty1prime")
            val (newBoundVariable, replaceVar, body1, body2) = (body, ty2) match
              case (Abs(v1, b1), Abs(v2, b2)) => (v1, v2, b1, b2)
              case _ => return proof.InvalidProofTactic(s"Term and Type must be lambda expressions")
            have(ty1 === ty1prime) by RightRefl.withParameters(ty1 === ty1prime)
            val newContext = localContext ++ Set(newBoundVariable ∈ ty1)
            val newBody2 = body2.substitute((replaceVar, newBoundVariable))
            val bodyProof = checkMemo(using SetTheoryLibrary)(newContext, body1, newBody2, memo)
            if bodyProof.isValid then
              val h1 = lib.have(bodyProof)
              val resetBot = h1.bot -<< (newBoundVariable ∈ ty1)
              have((newBoundVariable ∈ ty1 |- body1 ∈ newBody2) ++<< h1.bot) by Weakening(h1)
              thenHave((newBoundVariable ∈ ty1 ==> body1 ∈ newBody2) ++<< resetBot) by RightImplies
              thenHave((∀(newBoundVariable ∈ ty1, body1 ∈ newBody2)) ++<< resetBot) by RightForall
              val quantifiedTyping = lastStep
              val abstraction = TAbs of (T1 := ty1, T2 := ty2, e := body)
              have(Discharge(quantifiedTyping)(abstraction))
            else return proof.InvalidProofTactic(s"Failed to construct body proof")

          // e ∈ T, T === T' -> e ∈ T' for other cases
          case _ =>
            val inferredProof = inferMemo(using SetTheoryLibrary)(localContext, tm, memo)
            if !inferredProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the inference proof for $tm")
            val h1 = have(inferredProof)
            val inferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Failed to extract the inferred type from valid proof")
            if isSame(inferredType, ty) then
              have((tm ∈ ty) ++<< h1.bot) by Restate.from(h1)
            else
              val convProof = subsetProof(using SetTheoryLibrary)(localContext, inferredType, ty)
              if !convProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the equivalence proof for $inferredType and $ty")
              val h2 = have(convProof)
              val statement = (tm ∈ ty) ++<< h1.bot ++<< h2.bot
              val rule = TConvAdv of (e1 := tm, T := inferredType, T1 := ty)
              val withInference = have(((tm ∈ ty) +<< (inferredType ⊆ ty)) ++<< h1.bot) by
                Cut.withParameters(tm ∈ inferredType)(h1, rule)
              have(statement) by Cut.withParameters(inferredType ⊆ ty)(h2, withInference)
      }

    // Construct subset proof(ty1 ⊆ ty2) for the given two expressions
    def subsetProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], sub: Expr[Ind], sup: Expr[Ind]): proof.ProofTacticJudgement =
      import lib.*
      TacticSubproof { ip ?=>
        ip.cleanAssumptions
        (sub, sup) match
          case _ if sub == sup => have(sub ⊆ sup) by Restate.from(reflexivity of (x := sub))
          case (SPi(d1: Expr[Ind], Abs(v1: Expr[Ind], c1: Expr[Ind])), SPi(d2: Expr[Ind], Abs(v2: Expr[Ind], c2: Expr[Ind]))) =>
            if !isSame(d1, d2) then return proof.InvalidProofTactic(s"Function domains differ: $d1 and $d2")
            val domainEquiv = have(d1 === d2) by RightRefl.withParameters(d1 === d2)
            val c2Replace = c2.substitute((v2, v1))
            val newContext = localContext ++ Set(v1 ∈ d1)
            val codomainProof = subsetProof(using SetTheoryLibrary)(newContext, c1, c2Replace)
            if !codomainProof.isValid then return proof.InvalidProofTactic(s"Cannot prove codomain covariance: '${c1} ⊆ ${c2Replace}' for variable ${v1}.")
            val h1 = have(codomainProof)
            val context = h1.bot -<< (v1 ∈ d1)
            have((v1 ∈ d1 ==> c1 ⊆ c2Replace) ++<< context) by RightImplies.withParameters(v1 ∈ d1, c1 ⊆ c2Replace)(h1)
            thenHave(∀(v1 ∈ d1, c1 ⊆ c2Replace) ++<< context) by RightForall.withParameters(v1 ∈ d1 ==> c1 ⊆ c2Replace, v1)
            val quantifiedCovariance = lastStep
            val covariance = piCovariance of (T := d1, T1 := d2, T2 := Abs(v1, c1), T2p := Abs(v2, c2))
            have(Discharge(domainEquiv, quantifiedCovariance)(covariance))
          case _ =>
            val dSub = getDepth(sub)
            val dSup = getDepth(sup)
            if (dSub > dSup) then proof.InvalidProofTactic(s"Depth mismatch: $sub (d=$dSub) cannot be subset of $sup (d=$dSup)")
            else if (dSub == dSup) then
              if (localContext.contains(sub ⊆ sup)) then have(sub ⊆ sup |- sub ⊆ sup) by Hypothesis
              else if !isSame(sub, sup) then return proof.InvalidProofTactic(s"No inclusion known between $sub and $sup")
              else
                val equality = have(sub === sup) by RightRefl.withParameters(sub === sup)
                val reflexive = have(sub ⊆ sub) by Restate.from(reflexivity of (x := sub))
                val rewritten = have(sub === sup |- sub ⊆ sup) by
                  RightSubstEq.withParameters(List((sub, sup)), (Seq(T), sub ⊆ T))(reflexive)
                have(Discharge(equality)(rewritten))
            else if (dSub == dSup - 1 && isSame(sup, universeOf(sub))) then have(sub ⊆ sup) by Restate.from(subsetOfUniverse of (A := sub))
            else if dSub == dSup - 1 then return proof.InvalidProofTactic(s"No universe inclusion known between $sub and $sup")
            else
              val step1 = have(sub ⊆ universeOf(sub)) by Restate.from(subsetOfUniverse of (A := sub))
              val step2Proof = subsetProof(using SetTheoryLibrary)(localContext, universeOf(sub), sup)
              if !step2Proof.isValid then return proof.InvalidProofTactic(s"Further subset proof failed: ${universeOf(sub)} and $sup")
              val step2 = have(step2Proof)
              val transitive = transitivity of (x := sub, y := universeOf(sub), z := sup)
              have(Discharge(step1, step2)(transitive))
      }
