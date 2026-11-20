package lisa.maths.SetTheory.Types.ADT.tactics

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.PatternMatching.syntax.CaseAccumulator
import lisa.maths.SetTheory.Types.ADT.interface.ADT
import lisa.maths.SetTheory.Types.ADT.interface.Constructor
import lisa.maths.SetTheory.Types.ADT.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.TypeAssign
import lisa.utils.prooflib.BasicStep.RightForall
import lisa.utils.prooflib.BasicStep.RightImplies
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.prooflib.ProofJudgement
import lisa.utils.prooflib.Subproof
import lisa.utils.prooflib.Thm

/**
 *  Tactic performing a structural induction proof over an algebraic data type.
 *
 *  ===Usage===
 *  {{{
 *  have(forall(x, x :: adt => P(x)) /*or*/ x :: adt |- P(x)) by Induction(x, adt) {
 *    Case(c1, x1, ..., xn) subproof {
 *      // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn))
 *    }
 *    ...
 *    Case(cm, x1, ..., xk) subproof {
 *      // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn'))
 *    }
 *  }
 *  }}}
 *
 *  x and adt are inferred from the context if not provided by the user.
 *
 *  Supports only 1 formula on the right hand side of the sequent.
 *  @param expectedVar the variable on which the induction is performed
 *  @param expectedADT the algebraic data type on which the induction is performed
 */
class Induction(
    expectedVar: Option[Variable[Ind]],
    expectedADT: Option[SpecializedADT[?]]
) {

  private def typeSubstitutionMap(adt: SpecializedADT[?]): Map[String, Expr[Ind]] =
    adt.base.typeVariablesSeq.map(_.id.toString).zip(adt.typeArgs).toMap

  private def instantiateForallSeq(formula: Expr[Prop], args: Seq[Expr[Ind]]): Expr[Prop] =
    args.foldLeft(formula) { (current, arg) =>
      current match
        case forall(v, phi) => phi.substitute(v := arg).asInstanceOf[Expr[Prop]]
        case _ => current
    }

  private def caseHypotheses(
      constructor: Constructor[?],
      adt: SpecializedADT[?],
      binders: Seq[Variable[Ind]],
      prop: Expr[Ind >>: Prop]
  ): Seq[(Variable[Ind], Seq[Expr[Prop]])] =
    val specializedTypeArgs = typeSubstitutionMap(adt)
    constructor.semantic.syntacticSignature(binders).map {
      case (v, SelfRef) => v -> Seq(v :: adt.term, prop(v))
      case (v, TypeArg(typeName)) =>
        val t = specializedTypeArgs.getOrElse(typeName, typeExprToTerm(typeName))
        v -> Seq(v :: t)
    }

  // forall interleaved per binder
  private def abstractConstructorCase(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      rawCaseProof: Thm,
      binders: Seq[Variable[Ind]],
      constructor: Constructor[?],
      adt: SpecializedADT[?],
      prop: Expr[Ind >>: Prop]
  ): Thm =
    caseHypotheses(constructor, adt, binders, prop).foldRight[Thm](rawCaseProof) { case ((v, hyps), acc) =>
      val withImpls = hyps.foldRight[Thm](acc) { (h, a) =>
        val accRight = a.statement.right.head
        have((a.statement -<? h).left |- h ==> accRight) by Weakening(a)
      }
      have(withImpls.statement.left |- forall(v, withImpls.statement.right.head)) by RightForall(withImpls)
    }

  // all foralls out front
  private def normalizeConstructorCase(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      rawCaseProof: Thm,
      binders: Seq[Variable[Ind]],
      assumptions: Seq[Expr[Prop]],
      context: Set[Expr[Prop]]
  ): Thm =
    val lifted = have(context |- seqAnd(assumptions) ==> rawCaseProof.statement.right.head) by Tautology.from(rawCaseProof)
    binders.reverse.foldLeft[Thm](lifted) { (acc2, binder) =>
      have(acc2.statement.left |- forall(binder, acc2.statement.right.head)) by RightForall(acc2)
    }

  /**
   *  Proves the inductive case for a single constructor, in the shape expected by the
   *  ADT induction principle: `forall(args, typing /\ inductionHypotheses ==> P(c(args)))`.
   *
   *  Each branch carries a payload proving the property for its pattern (possibly under a
   *  guard, when several branches share the constructor, e.g. `cons(tru, tl)` vs
   *  `cons(fals, tl)`). The branch payloads are normalized, instantiated at the
   *  constructor's variables and fresh inner witnesses. Branch selection discharges the
   *  existential guards by case analysis. The combined generic-case proof is abstracted into
   *  the quantified, hypothesis-laden form the induction principle consumes.
   *
   *  @tparam N the arity of the ADT
   *  @param proof the scope in which the case is proven
   *  @param constructor the constructor whose case is being established
   *  @param branches the compiled branches for `constructor`, each with its payload proof
   *  @param patternSystem the compiled pattern system, used for guard selection
   *  @param adt the (specialized) ADT being inducted over
   *  @param prop the property as a lambda (`λt. P(t)`)
   *  @param context the ambient hypotheses carried through every case
   */
  private def buildBranchProof(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      constructor: Constructor[?],
      branches: Seq[Clause[Thm]],
      patternSystem: PatternSystem[?],
      adt: SpecializedADT[?],
      prop: Expr[Ind >>: Prop],
      context: Set[Expr[Prop]]
  ): Thm =
    val forbidden = context.toSeq ++ Seq(prop, adt.term) ++ branches.flatMap(_.binders)
    val vars = constructor.semantic.variables2.foldLeft(Vector.empty[Variable[Ind]]) { (fresh, variable) =>
      fresh :+ Variable[Ind](freshId(forbidden ++ fresh, variable.id.name))
    }
    val inputTerm = constructor.semantic
      .appliedTerm(vars)
      .substitute(adt.base.typeVariablesSeq.zip(adt.typeArgs).map((v, a) => v := a)*)
      .asInstanceOf[Expr[Ind]]
    val hyps = caseHypotheses(constructor, adt, vars, prop)
    val typingAssumptions = hyps.map(_._2.head)
    val recursiveAssumptions = hyps.collect { case (_, Seq(_, ih)) => ih }
    val genericGoal = prop(inputTerm)

    val localContext = context ++ typingAssumptions ++ recursiveAssumptions
    val guardedImplications = branches.map { branch =>
      val (topBinders, innerBinders) = branch.binders.splitAt(constructor.semantic.arity)
      val innerTyping = branch.typingSignatureAt(branch.binders).drop(constructor.semantic.arity).map((v, typ) => v :: typ)
      val assumptions = caseHypotheses(constructor, adt, topBinders, prop).flatMap(_._2) ++ innerTyping :+ branch.branchCondition
      val abstracted = normalizeConstructorCase(branch.payload, branch.binders, assumptions, context)
      val innerVars = innerBinders.foldLeft(Vector.empty[Variable[Ind]]) { (acc, binder) =>
        acc :+ Variable[Ind](freshId(localContext.toSeq ++ Seq(genericGoal) ++ vars ++ acc, binder.id.name))
      }
      val arguments = vars ++ innerVars
      val instantiated = have(context |- instantiateForallSeq(abstracted.statement.right.head, arguments)) by
        InstantiateForallSeq(arguments)(abstracted)
      val substitutions = branch.binders.zip(arguments).map((from, to) => from := to)
      val guard = seqAnd(innerTyping :+ branch.branchCondition).substitute(substitutions*)
      val guarded = have((localContext + guard) |- genericGoal) by Tautology.from(instantiated)

      // Inner pattern variables are witnesses supplied by branch selection.
      val (selection, selectedProof) = innerVars.foldRight((guard, guarded: Thm)) { case (v, (condition, fact)) =>
        val existential = ∃(v, condition)
        val lifted = have((localContext + existential) |- genericGoal) by LeftExists(fact)
        (existential, lifted)
      }
      have(localContext |- selection ==> genericGoal) by RightImplies.withParameters(selection, genericGoal)(selectedProof)
    }
    val selectorSchema = patternSystem.branchSelectionFor(constructor.semantic, inputTerm)
    val selectorAtConstructor = have(instantiateForallSeq(selectorSchema.statement.right.head, vars)) by
      InstantiateForallSeq(vars)(selectorSchema)
    val branchGuardDisjunction = selectorAtConstructor.statement.right.head match
      case _ ==> consequent => have(localContext |- consequent) by Tautology.from(selectorAtConstructor)
      case _ => throw UnreachableException
    val genericCaseProof = have(localContext |- genericGoal) by Tautology.from((branchGuardDisjunction +: guardedImplications)*)

    abstractConstructorCase(genericCaseProof, vars, constructor, adt, prop)

  /**
   *  Given a proof of the claim for each case (possibly using the induction hypothesis),
   *  reassemble the subproofs to generate a proof of the claim for every element of the
   *  ADT.
   *
   *  @tparam N the arity of the ADT
   *  @param proof the scope in which the induction is performed
   *  @param cases the cases to prove. A [[CaseAccumulator]] is a mutable data structure
   *    that register every case that has been added to the tactic.
   *  @param bot the claim
   */
  def apply(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      cases: CaseAccumulator[
        Thm,
        (Sequent, SpecializedADT[?], Variable[Ind])
      ] ?=> Unit
  )(bot: Sequent): ProofJudgement = {
    if bot.right.size != 1 then return invalidTactic("Induction requires exactly one formula on the right of its goal.")

    Induction.inferArguments(bot, expectedVar, expectedADT) match
      case Some((inferedVar, inferedADT, inferedProp)) =>

        val body: Expr[Prop] = inferedProp.getOrElse(bot.right.head)
        val propertyVar = Variable[Ind](freshId(bot.left.toSeq ++ bot.right.toSeq :+ inferedADT.term, "t"))
        val prop: Expr[Ind >>: Prop] = λ(propertyVar, body.substitute(inferedVar -> propertyVar))

        val assignment = inferedVar :: inferedADT.term

        val missingTypingAssumption =
          inferedProp.isEmpty &&
            !bot.left.contains(assignment) &&
            bot.freeVars.contains(inferedVar)

        if missingTypingAssumption then
          invalidTactic(
            s"Induction on variable '$inferedVar' over ADT '${inferedADT.name}' requires the typing assumption '$assignment' in the goal context. " +
              s"Current goal is '$bot'. Add '( $assignment ) |- ...', or restate the goal as a universally quantified statement " +
              s"'|- forall($inferedVar, $assignment ==> P($inferedVar))'."
          )
        else
          val context = (if inferedProp.isDefined then bot else bot -<< assignment).left
          val builder =
            CaseAccumulator[Thm, (Sequent, SpecializedADT[?], Variable[Ind])](
              (context |- body, inferedADT, inferedVar)
            )
          cases(using builder)

          val compiledBranchSystem = builder.compile(inferedADT)

          compiledBranchSystem match
            case Right(branchSystem) => buildInductionProof(bot, inferedVar, inferedProp, body, prop, context, branchSystem)
            case Left(msg) => invalidTactic(msg)

      case None =>
        invalidTactic("No variable typed with the ADT found in the context.")
  }

  /**
   *  Assembles the whole induction proof from an already-compiled branch system.
   *
   *  Instantiates the ADT induction principle at `prop`, discharges every constructor case
   *  with [[buildBranchProof]], chains the results to obtain `forall(inferedVar,
   *  inferedVar :: adt ==> body)`, then derives the original goal `bot` — instantiating the
   *  universal quantifier when the goal was stated in typed-context form rather than
   *  quantified form.
   *
   *  @tparam N the arity of the ADT
   *  @param proof the scope in which the induction is performed
   *  @param bot the claim to conclude
   *  @param inferedVar the induction variable
   *  @param inferedProp the property body when the goal is universally quantified, `None`
   *    for the typed-context form `x :: adt |- P(x)` (drives the final instantiation step)
   *  @param body the property to establish (`P(inferedVar)`)
   *  @param prop the property as a lambda (`λt. body[inferedVar := t]`)
   *  @param context the ambient hypotheses (the goal minus the typing assumption)
   *  @param branchSystem the compiled per-constructor branches with their payload proofs
   */
  private def buildInductionProof(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      bot: Sequent,
      inferedVar: Variable[Ind],
      inferedProp: Option[Expr[Prop]],
      body: Expr[Prop],
      prop: Expr[Ind >>: Prop],
      context: Set[Expr[Prop]],
      branchSystem: PatternSystem[Thm]
  ): ProofJudgement = Subproof { sp ?=>

    val specializedADT = branchSystem.domain
    val typeVariablesSubstPairs =
      specializedADT.base.typeVariablesSeq.zip(specializedADT.typeArgs).map(SubstPair(_, _))
    val instantiatedInduction = have(
      specializedADT.base.semantic.induction.statement.substitute((typeVariablesSubstPairs :+ (P := prop))*)
    ) by Restate.from(
      specializedADT.base.semantic.induction.of((typeVariablesSubstPairs :+ (P := prop))*)
    )

    specializedADT.base.constructors.foldLeft[Thm](instantiatedInduction)((acc, constructor) =>
      val branchPairs = branchSystem
        .clausesFor(constructor.semantic)
        .map(
          _.map(payload => have(payload.statement) by Restate.from(payload): Thm)
        )
      val inductiveCaseProof = buildBranchProof(using sp)(
        constructor,
        branchPairs,
        branchSystem,
        specializedADT,
        prop,
        context
      )
      acc.statement.right.head match
        case implies(_, rest) =>
          have((acc.statement.left ++ inductiveCaseProof.statement.left) |- rest) by
            Tautology.from(acc, inductiveCaseProof)
        case _ => throw UnreachableException
    )
    thenHave(
      context |- ∀(inferedVar :: specializedADT.term, body)
    ) by Restate
    if !inferedProp.isDefined then
      lastStep.statement.right.head match
        case forall(_, phi) => thenHave(context |- phi) by InstantiateForall(inferedVar)
        case _ => throw UnreachableException
    thenHave(bot) by Restate
  }
}

object Induction {

  /**
   *  Reconciles the variable/ADT recovered from the goal with the ones the user
   *  may have supplied explicitly. Returns [[None]] on a mismatch.
   */
  private def checkFoundArguments(
      expectedVar: Option[Variable[Ind]],
      expectedADT: Option[SpecializedADT[?]],
      foundVar: Variable[Ind],
      foundADT: SpecializedADT[?]
  ): Option[(Variable[Ind], SpecializedADT[?])] = (expectedVar, expectedADT) match
    case (Some(v), _) if v != foundVar => None
    case (_, Some(a)) if a.base != foundADT.base || a.typeArgs != foundADT.typeArgs => None
    case _ => Some((foundVar, foundADT))

  /**
   *  Infers the variable, the ADT and the arguments of the ADT from a formula of the form
   *  `x :: ADT(T1, ..., Tn)`.
   *
   *  @param f the formula to infer these elements from
   */
  private def inferArgumentsExpr(
      f: Expr[Prop],
      expectedVar: Option[Variable[Ind]],
      expectedADT: Option[SpecializedADT[?]]
  ): Option[(Variable[Ind], SpecializedADT[?])] =
    f match
      case TypeAssign(Variable[Ind](id), typeTerm) =>
        inferADTFromTypeTerm(typeTerm)
          .flatMap(foundADT => checkFoundArguments(expectedVar, expectedADT, Variable[Ind](id), foundADT))
      case _ => None

  /**
   *  Reads a typing term such as `ADT(T1, ..., Tn)` back into the ADT it names and the
   *  terms it is applied to. The head symbol is matched by identity and the arguments are
   *  kept as they stand, so nothing is reconstructed from a name.
   */
  private def inferADTFromTypeTerm(typeTerm: Expr[Ind]): Option[SpecializedADT[?]] =
    val (head, args) = unfoldAllApp(typeTerm)
    head match
      case c: Constant[?] @unchecked =>
        ADT.getADT(c.id).map(_.specialize(args.map(_.asInstanceOf[Expr[Ind]])*))
      case _ => None

  /**
   *  Infers the variable, the ADT and the (optional) property body of an induction goal.
   *  Returns `None` unless the goal has exactly one conclusion.
   *
   *  It looks, in order, for:
   *    1. a typing premise `x :: ADT(...)` on the left of the sequent,
   *    2. a universally quantified goal `|- forall(x, x :: ADT(...) ==> P(x))`,
   *    3. the variable/ADT supplied explicitly to the tactic (the fallback used by
   *       calls such as `Induction(x, nat)` when no typing is present in the goal).
   *
   *  @param seq the sequent to infer these elements from
   *  @param expectedVar the variable supplied explicitly to the tactic, if any
   *  @param expectedADT the ADT supplied explicitly to the tactic, if any
   */
  def inferArguments(
      seq: Sequent,
      expectedVar: Option[Variable[Ind]],
      expectedADT: Option[SpecializedADT[?]]
  ): Option[(Variable[Ind], SpecializedADT[?], Option[Expr[Prop]])] =
    if seq.right.size != 1 then None
    else
      seq.left
        .foldLeft[Option[(Variable[Ind], SpecializedADT[?])]](None)((acc, prem) => acc.orElse(inferArgumentsExpr(prem, expectedVar, expectedADT)))
        .map(p => (p._1, p._2, None))
        .orElse(
          seq.right.head match
            case forall(x, implies(assignment, prop)) =>
              inferArgumentsExpr(assignment, expectedVar, expectedADT)
                .filter(p => p._1 == x)
                .map(p => (p._1, p._2, Some(prop)))
            case _ => None
        )
        .orElse(
          (expectedVar, expectedADT) match
            case (Some(v), Some(a)) => Some((v, a, None))
            case _ => None
        )

  def apply() = new Induction(None, None)

  def apply(adt: ADT[?]) =
    new Induction(None, Some(adt.specialize(adt.typeVariablesSeq*)))

  def apply(adt: SpecializedADT[?]) =
    new Induction(None, Some(adt))

  def apply(v: Variable[Ind]) =
    new Induction(Some(v), None)

  def apply(v: Variable[Ind], adt: ADT[?]) =
    new Induction(Some(v), Some(adt.specialize(adt.typeVariablesSeq*)))

  def apply(v: Variable[Ind], adt: SpecializedADT[?]) =
    new Induction(Some(v), Some(adt))
}
