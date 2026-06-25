package lisa.maths.SetTheory.Types.ADTv2.tactics

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction.InductionBranch
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction.InductionBranchSystem
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax.CaseAccumulator
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.debug.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.TypeAssign
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.BasicStepTactic.RightImplies
import lisa.utils.prooflib.ProofTacticLib.Arity

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
class Induction[M <: Arity](
    expectedVar: Option[Variable[Ind]],
    expectedADT: Option[SpecializedADT[M]]
) extends lisa.utils.prooflib.ProofTacticLib.ProofTactic {

  private def typeSubstitutionMap[N <: Arity](adt: SpecializedADT[N]): Map[String, Expr[Ind]] =
    adt.base.typeVariablesSeq.map(_.id.name).zip(adt.typeArgs).toMap

  private def instantiateForallSeq(formula: Expr[Prop], args: Seq[Expr[Ind]]): Expr[Prop] =
    args.foldLeft(formula) { (current, arg) =>
      current match
        case forall(v, phi) => phi.substitute(v := arg).asInstanceOf[Expr[Prop]]
        case _              => current
    }

  private def caseHypotheses[N <: Arity](
    constructor: Constructor[N],
    adt: SpecializedADT[N],
    binders: Seq[Variable[Ind]],
    prop: Expr[Ind >>: Prop]
  ): Seq[(Variable[Ind], Seq[Expr[Prop]])] =
    val specializedTypeArgs = typeSubstitutionMap(adt)
    constructor.semantic.syntacticSignature(binders).map {
      case (v, SelfRef)           => v -> Seq(v :: adt.term, prop(v))
      case (v, TypeArg(typeName)) =>
        val t = specializedTypeArgs.getOrElse(typeName, typeExprToTerm(typeName))
        v -> Seq(v :: t)
    }

  // forall interleaved per binder
  private def abstractConstructorCase[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      rawCaseProof: proof.Fact,
      binders: Seq[Variable[Ind]],
      constructor: Constructor[N],
      adt: SpecializedADT[N],
      prop: Expr[Ind >>: Prop]
  ): proof.Fact =
    caseHypotheses(constructor, adt, binders, prop).foldRight[proof.Fact](rawCaseProof) {
      case ((v, hyps), acc) =>
        val withImpls = hyps.foldRight[proof.Fact](acc) { (h, a) =>
          val accRight = a.statement.right.head
          have((a.statement -<? h).left |- h ==> accRight) by Weakening(a)
        }
        have(withImpls.statement.left |- forall(v, withImpls.statement.right.head)) by RightForall(withImpls)
    }

  // all foralls out front
  private def normalizeConstructorCase[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      rawCaseProof: proof.Fact,
      binders: Seq[Variable[Ind]],
      constructor: Constructor[N],
      adt: SpecializedADT[N],
      prop: Expr[Ind >>: Prop]
  ): proof.Fact =
    val perBinder   = caseHypotheses(constructor, adt, binders, prop)
    val assumptions = perBinder.flatMap(_._2)
    val lifted = assumptions.foldRight[proof.Fact](rawCaseProof) { (assumption, acc2) =>
      val accRight = acc2.statement.right.head
      have((acc2.statement -<? assumption).left |- assumption ==> accRight) by
        RightImplies.withParameters(assumption, accRight)(acc2)
    }
    binders.reverse.foldLeft[proof.Fact](lifted) { (acc2, binder) =>
      have(acc2.statement.left |- forall(binder, acc2.statement.right.head)) by RightForall(acc2)
    }

  /**
   *  Proves the inductive case for a single constructor, in the shape expected by the
   *  ADT induction principle: `forall(args, typing /\ inductionHypotheses ==> P(c(args)))`.
   *
   *  Each branch carries a payload proving the property for its pattern (possibly under a
   *  guard, when several branches share the constructor, e.g. `cons(tru, tl)` vs
   *  `cons(fals, tl)`). The branch payloads are normalized, instantiated at the
   *  constructor's variables, and combined: with a single branch the payload is used
   *  directly; with several, the pattern system's branch-selection theorem discharges the
   *  guards by case analysis. The combined generic-case proof is then abstracted back into
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
  private def buildBranchProof[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      constructor: Constructor[N],
      branches: Seq[InductionBranch[N, proof.Fact]],
      patternSystem: PatternSystem[N],
      adt: SpecializedADT[N],
      prop: Expr[Ind >>: Prop],
      context: Set[Expr[Prop]]
  ): proof.Fact =
    val vars = constructor.semantic.variables2
    val inputTerm = constructor.semantic
      .appliedTerm(vars)
      .substitute(adt.base.typeVariablesSeq.zip(adt.typeArgs).map((v, a) => v := a)*)
      .asInstanceOf[Expr[Ind]]
    val hyps = caseHypotheses(constructor, adt, vars, prop)
    val typingAssumptions   = hyps.map(_._2.head)
    val recursiveAssumptions = hyps.collect { case (_, Seq(_, ih)) => ih }
    val genericGoal = prop(inputTerm)

    val guardedConclusions = branches.map { branch =>
      val guarded = branch.guardAssumptions.foldRight[proof.Fact](branch.payload) { (guard, acc2) =>
        val accRight = acc2.statement.right.head
        have((acc2.statement -<? guard).left |- guard ==> accRight) by Weakening(acc2)
      }
      val abstracted = normalizeConstructorCase(guarded, branch.binders, branch.constructor, adt, prop)
      val instantiated = have(instantiateForallSeq(abstracted.statement.right.head, vars)) by
        InstantiateForallSeq(vars)(abstracted)
      val guardSubstitutions = branch.binders.zip(vars).map((from, to) => from := to)
      val instantiatedGuards = branch.guardAssumptions.map(
        _.substitute(guardSubstitutions*).asInstanceOf[Expr[Prop]]
      )
      val guardFormula = instantiatedGuards match
        case Nil => True: Expr[Prop]
        case head +: tail => tail.foldLeft(head)(_ /\ _)
      val guardedConclusion = have(
        (context ++ typingAssumptions ++ recursiveAssumptions ++ instantiatedGuards.toSet) |- genericGoal
        ) by Tautology.from(instantiated)
      (guardFormula, guardedConclusion)
    }
    val genericCaseProof = have((context ++ typingAssumptions ++ recursiveAssumptions) |- genericGoal) subproof {

      if guardedConclusions.size == 1 then
        have((context ++ typingAssumptions ++ recursiveAssumptions) |- genericGoal) by
          Tautology.from(guardedConclusions.head._2)
      else
        val selectorSchema = patternSystem.branchSelectionFor(constructor.semantic, inputTerm)
        val selectorAtConstructor = have(instantiateForallSeq(selectorSchema.statement.right.head, vars)) by
          InstantiateForallSeq(vars)(selectorSchema)
        val branchGuardDisjunction = selectorAtConstructor.statement.right.head match
          case premise ==> consequent =>
            val localContext = context ++ typingAssumptions ++ recursiveAssumptions
            val typingFacts = typingAssumptions.map(assumption => have(localContext |- assumption) by Hypothesis)
            val inputEqInContext = have(localContext |- inputTerm === inputTerm) by Restate
            val selectorPremise = have(localContext |- premise) by Tautology.from((inputEqInContext +: typingFacts)*)
            have(localContext |- consequent) by Tautology.from(selectorAtConstructor, selectorPremise)
          case _ => throw UnreachableException
          
        val guardedImplications = guardedConclusions.map((guard, fact) =>
          have((fact.statement -<? guard).left |- guard ==> genericGoal) by
            RightImplies.withParameters(guard, genericGoal)(fact)
        )
        have((context ++ typingAssumptions ++ recursiveAssumptions) |- genericGoal) by
          Tautology.from((branchGuardDisjunction +: guardedImplications)*)
    }

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
  def apply[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      cases: CaseAccumulator[
        N,
        proof.ProofStep,
        (Sequent, Seq[Expr[Ind]], Variable[Ind])
      ] ?=> Unit
  )(bot: Sequent): proof.ProofTacticJudgement = Time.measure("Induction tactic") {
    Induction.inferArguments(bot, expectedVar, expectedADT) match
      case Some((inferedVar, inferedADT, _)) if expectedADT.isEmpty && inferedADT.typeArgs.nonEmpty =>
        proof.InvalidProofTactic(
          s"Induction cannot infer the type-instantiated ADT '${inferedADT.name}' from the goal '$bot'. " +
            s"Inference is only supported for non-parametric ADTs; for a parametric ADT, pass it explicitly, " +
            s"e.g. 'Induction($inferedVar, <adt>)'."
        )

      case Some((inferedVar, inferedADT, inferedProp)) =>

        val body: Expr[Prop] = inferedProp.getOrElse(bot.right.head)
        val prop: Expr[Ind >>: Prop] = λ(t, body.substitute(inferedVar -> t))

        val assignment = inferedVar :: inferedADT.term

        val missingTypingAssumption =
          inferedProp.isEmpty &&
            !bot.left.contains(assignment) &&
            bot.freeVars.contains(inferedVar)

        if missingTypingAssumption then
          proof.InvalidProofTactic(
            s"Induction on variable '$inferedVar' over ADT '${inferedADT.name}' requires the typing assumption '$assignment' in the goal context. " +
              s"Current goal is '$bot'. Add '( $assignment ) |- ...', or restate the goal as a universally quantified statement " +
              s"'|- forall($inferedVar, $assignment ==> P($inferedVar))'."
          )
        else
          val context = (if inferedProp.isDefined then bot else bot -<< assignment).left
          val builder =
            CaseAccumulator[N, proof.ProofStep, (Sequent, Seq[Expr[Ind]], Variable[Ind])](
              (context |- body, inferedADT.typeArgs, inferedVar)
            )
          cases(using builder)

          val compiledBranchSystem = builder.compileForInduction(inferedADT.asInstanceOf[SpecializedADT[N]])

          compiledBranchSystem match
            case Right(branchSystem) => buildInductionProof(bot, inferedVar, inferedProp, body, prop, context, branchSystem)
            case Left(msg) => proof.InvalidProofTactic(msg)

      case None =>
        proof.InvalidProofTactic("No variable typed with the ADT found in the context.")
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
  private def buildInductionProof[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      bot: Sequent,
      inferedVar: Variable[Ind],
      inferedProp: Option[Expr[Prop]],
      body: Expr[Prop],
      prop: Expr[Ind >>: Prop],
      context: Set[Expr[Prop]],
      branchSystem: InductionBranchSystem[N, proof.ProofStep]
  ): proof.ProofTacticJudgement = TacticSubproof { sp ?=>

    val specializedADT = branchSystem.domain
    val typeVariablesSubstPairs =
      specializedADT.base.typeVariablesSeq.zip(specializedADT.typeArgs).map(SubstPair(_, _))
    val instantiatedInduction = have(
      specializedADT.base.semantic.induction.statement.substitute((typeVariablesSubstPairs :+ (P := prop))*)
    ) by Restate.from(
      specializedADT.base.semantic.induction.of((typeVariablesSubstPairs :+ (P := prop))*)
    )

    specializedADT.base.constructors.foldLeft[sp.Fact](instantiatedInduction)((acc, constructor) =>
      val branchPairs = branchSystem.branchesFor(constructor).map(
        _.map(payload => have(payload.statement) by Restate.from(payload): sp.Fact)
      )
      val inductiveCaseProof = buildBranchProof(using sp)(
        constructor,
        branchPairs,
        branchSystem.system,
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
        TypeTermParser.inferADTFromTypeTerm(typeTerm)
          .flatMap(foundADT => checkFoundArguments(expectedVar, expectedADT, Variable[Ind](id), foundADT))
      case _ => None

  /**
   *  Infers the variable, the ADT and the (optional) property body of an induction goal.
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
    seq.left.foldLeft[Option[(Variable[Ind], SpecializedADT[?])]](None)(
      (acc, prem) => acc.orElse(inferArgumentsExpr(prem, expectedVar, expectedADT))
    )
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
          case _                  => None
      )

  def apply() = new Induction(None, None)

  def apply[N <: Arity](adt: ADT[N]) =
    new Induction(None, Some(adt.specialize(adt.typeVariablesSeq*)))

  def apply[N <: Arity](adt: SpecializedADT[N]) =
    new Induction(None, Some(adt))

  def apply(v: Variable[Ind]) =
    new Induction(Some(v), None)

  def apply[N <: Arity](v: Variable[Ind], adt: ADT[N]) =
    new Induction(Some(v), Some(adt.specialize(adt.typeVariablesSeq*)))

  def apply[N <: Arity](v: Variable[Ind], adt: SpecializedADT[N]) =
    new Induction(Some(v), Some(adt))
}
