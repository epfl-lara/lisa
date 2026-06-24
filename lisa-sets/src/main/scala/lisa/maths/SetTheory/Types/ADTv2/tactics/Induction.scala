package lisa.maths.SetTheory.Types.ADTv2.tactics

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction.InductionBranch
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction.InductionBranchSystemWithPayload
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

  private def constructorTypingAssumptions[N <: Arity](
      constructor: Constructor[N],
      adt: SpecializedADT[N],
      vars: Seq[Variable[Ind]]
  ): Seq[Expr[Prop]] =
    val specializedTypeArgs = typeSubstitutionMap(adt)
    constructor.semantic.syntacticSignature(vars).map {
      case (v, SelfRef) => v :: adt.term
      case (v, TypeArg(typeName)) =>
        v :: specializedTypeArgs.getOrElse(typeName, typeExprToTerm(typeName))
    }

  private def constructorRecursiveAssumptions[N <: Arity](
      constructor: Constructor[N],
      vars: Seq[Variable[Ind]],
      prop: Expr[Ind >>: Prop]
  ): Seq[Expr[Prop]] =
    constructor.semantic.recursiveBinders(vars).map(v => prop(v))

  private def abstractConstructorCase[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      rawCaseProof: proof.Fact,
      binders: Seq[Variable[Ind]],
      constructor: Constructor[N],
      adt: SpecializedADT[N],
      prop: Expr[Ind >>: Prop]
  ): proof.Fact =
    val specializedTypeArgs = typeSubstitutionMap(adt)
    constructor.semantic.syntacticSignature(binders).foldRight[proof.Fact](rawCaseProof) { case ((v, ty), acc2) =>
      val accRight: Expr[Prop] = acc2.statement.right.head
      ty match
        case SelfRef =>
          have((acc2.statement -<? prop(v)).left |- prop(v) ==> accRight) by Weakening(acc2)
          thenHave(
            (lastStep.statement -<? (v :: adt.term)).left |-
              v :: adt.term ==> (prop(v) ==> accRight)
          ) by Weakening
          thenHave(lastStep.statement.left |- forall(v, v :: adt.term ==> (prop(v) ==> accRight))) by RightForall
        case TypeArg(typeName) =>
          val t = specializedTypeArgs.getOrElse(typeName, typeExprToTerm(typeName))
          thenHave((acc2.statement -<? (v :: t)).left |- v :: t ==> accRight) by Weakening
          thenHave(lastStep.statement.left |- forall(v, v :: t ==> accRight)) by RightForall
    }

  private def normalizeConstructorCase[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      rawCaseProof: proof.Fact,
      binders: Seq[Variable[Ind]],
      constructor: Constructor[N],
      adt: SpecializedADT[N],
      prop: Expr[Ind >>: Prop]
  ): proof.Fact =
    val specializedTypeArgs = typeSubstitutionMap(adt)
    val assumptions = constructor.semantic.syntacticSignature(binders).flatMap {
      case (v, SelfRef) =>
        Seq(v :: adt.term, prop(v))
      case (v, TypeArg(typeName)) =>
        val t = specializedTypeArgs.getOrElse(typeName, typeExprToTerm(typeName))
        Seq(v :: t)
    }
    val lifted = assumptions.foldRight[proof.Fact](rawCaseProof) { (assumption, acc2) =>
      val accRight = acc2.statement.right.head
      have((acc2.statement -<? assumption).left |- assumption ==> accRight) by
        RightImplies.withParameters(assumption, accRight)(acc2)
    }
    binders.reverse.foldLeft[proof.Fact](lifted) { (acc2, binder) =>
      have(acc2.statement.left |- forall(binder, acc2.statement.right.head)) by RightForall(acc2)
    }

  private def abstractInductionBranch[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      rawBranchProof: proof.Fact,
      branch: InductionBranch[N],
      adt: SpecializedADT[N],
      prop: Expr[Ind >>: Prop]
  ): proof.Fact =
    val guarded = branch.guardAssumptions.foldRight[proof.Fact](rawBranchProof) { (guard, acc2) =>
      val accRight = acc2.statement.right.head
      have((acc2.statement -<? guard).left |- guard ==> accRight) by Weakening(acc2)
    }
    normalizeConstructorCase(guarded, branch.binders, branch.constructor, adt, prop)

  private def proveConstructorFromBranches[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      constructor: Constructor[N],
      branches: Seq[(InductionBranch[N], proof.Fact)],
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
    val typingAssumptions = constructorTypingAssumptions(constructor, adt, vars)
    val recursiveAssumptions = constructorRecursiveAssumptions(constructor, vars, prop)
    val genericGoal = prop(inputTerm)

    val genericCaseProof = have((context ++ typingAssumptions ++ recursiveAssumptions) |- genericGoal) subproof {
      val selectorSchema = patternSystem.branchSelectionFor(constructor.semantic, inputTerm)
      val selectorAtConstructor =
        selectorSchema.statement.right.head match
          case _ =>
            val instantiatedSelector = vars.foldLeft(selectorSchema.statement.right.head) { (current, arg) =>
              current match
                case forall(v, phi) => phi.substitute(v := arg).asInstanceOf[Expr[Prop]]
                case _ => current
            }
            have(instantiatedSelector) by InstantiateForallSeq(vars)(selectorSchema)
      val branchGuardDisjunction = selectorAtConstructor.statement.right.head match
        case premise ==> consequent =>
          val inputEq = inputTerm match
            case term => have(term === term) by Congruence
          val localContext = context ++ typingAssumptions ++ recursiveAssumptions
          val typingFacts = typingAssumptions.map(assumption => have(localContext |- assumption) by Hypothesis)
          val inputEqInContext = have(localContext |- inputEq.statement.right.head) by Tautology.from(inputEq)
          val selectorPremise = have(localContext |- premise) by Tautology.from((inputEqInContext +: typingFacts)*)
          have(localContext |- consequent) by Tautology.from(selectorAtConstructor, selectorPremise)
        case _ => throw UnreachableException

      val guardedConclusions = branches.map { case (branch, payload) =>
        val abstracted = abstractInductionBranch(payload, branch, adt, prop)
        val instantiatedTarget = vars.foldLeft(abstracted.statement.right.head) { (current, arg) =>
          current match
            case forall(v, phi) => phi.substitute(v := arg).asInstanceOf[Expr[Prop]]
            case _ => current
        }
        val instantiated = have(instantiatedTarget) by InstantiateForallSeq(vars)(abstracted)
        val guardSubstitutions = branch.binders.zip(vars).map((from, to) => from := to)
        val instantiatedGuards = branch.guardAssumptions.map(
          _.substitute(guardSubstitutions*).asInstanceOf[Expr[Prop]]
        )
        val guardFormula = instantiatedGuards match
          case Nil => True: Expr[Prop]
          case head +: tail => tail.foldLeft(head)(_ /\ _)
        val guardedConclusion =
          have((context ++ typingAssumptions ++ recursiveAssumptions ++ instantiatedGuards.toSet) |- genericGoal) by
            Tautology.from(instantiated)
        (guardFormula, guardedConclusion)
      }

      if guardedConclusions.size == 1 then
        have((context ++ typingAssumptions ++ recursiveAssumptions) |- genericGoal) by
          Tautology.from(guardedConclusions.head._2)
      else
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
   *  reassemble them to generate a proof of the claim of the form `∀x. x :: adt => P(x)`
   *
   *  @param proof the proof in which the induction is performed
   *  @param cases the proofs of the claim for each case in addition to the variables used
   *    by the user
   *  @param inductionVariable the variable over which the induction is performed
   *  @param adt the algebraic data type to perform induction on
   *  @param prop the property to prove
   */
  private def proveForallPredicate[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      cases: Map[Constructor[N], (Seq[Variable[Ind]], proof.Fact)],
      inductionVariable: Variable[Ind],
      adt: SpecializedADT[N],
      prop: Expr[Ind >>: Prop],
      context: Set[Expr[Prop]]
  ): proof.Fact =

    val typeVariablesSubstPairs = adt.base.typeVariablesSeq
      .zip(adt.typeArgs)
      .map(SubstPair(_, _))
    val instTerm = adt.term

    val instantiatedInduction = have(
      adt.base.semantic.induction.statement.substitute((typeVariablesSubstPairs :+ (P := prop))*)
    ) by Restate.from(adt.base.semantic.induction.of((typeVariablesSubstPairs :+ (P := prop))*))

    adt.base.constructors.foldLeft[proof.Fact](instantiatedInduction)((acc, c) =>
      val inductiveCaseProof =
        abstractConstructorCase(cases(c)._2, cases(c)._1, c, adt, prop)
      acc.statement.right.head match
        case implies(_, rest) =>
          have((acc.statement.left ++ inductiveCaseProof.statement.left) |- rest) by
            Tautology.from(acc, inductiveCaseProof)
        case _ => throw UnreachableException
    )
    thenHave(
      context |- forall(
        inductionVariable,
        inductionVariable :: instTerm ==> prop(inductionVariable)
      )
    ) by Tautology // Change

  private def checkFoundArguments(
      foundVar: Variable[Ind],
      foundADT: SpecializedADT[?]
  ): Option[(Variable[Ind], SpecializedADT[?])] = (expectedVar, expectedADT) match
    case (Some(v), _) if v != foundVar => None
    case (_, Some(a)) if a.base != foundADT.base || a.typeArgs != foundADT.typeArgs => None
    case _ => Some((foundVar, foundADT))

  private def parseTypeExprRepr(repr: String): Option[TypeExpr] =
    def splitTopLevelArgs(raw: String): Option[Seq[String]] =
      if raw.isEmpty then Some(Seq.empty)
      else
        val args = scala.collection.mutable.ArrayBuffer.empty[String]
        val current = new StringBuilder
        var depth = 0
        var i = 0
        var bad = false
        val n = raw.length
        while i < n && !bad do
          raw.charAt(i) match
            case '[' =>
              depth += 1
              current.append('[')
            case ']' =>
              depth -= 1
              if depth < 0 then bad = true
              else current.append(']')
            case ',' if depth == 0 =>
              val arg = current.toString.trim
              if arg.isEmpty then bad = true
              else
                args += arg
                current.clear()
            case ch => current.append(ch)
          i += 1

        if bad || depth != 0 then None
        else
          val lastArg = current.toString.trim
          if lastArg.isEmpty then None
          else
            args += lastArg
            Some(args.toSeq)

    val s = repr.trim
    if s.isEmpty then None
    else
      val bracketIdx = s.indexOf('[')
      if bracketIdx < 0 then Some(TypeRef(s))
      else if !s.endsWith("]") then None
      else
        val name = s.substring(0, bracketIdx)
        val inner = s.substring(bracketIdx + 1, s.length - 1)
        splitTopLevelArgs(inner).flatMap { args =>
          args
            .foldLeft[Option[Seq[TypeExpr]]](Some(Seq.empty)) { (acc, arg) =>
              acc.flatMap(seq => parseTypeExprRepr(arg).map(seq :+ _))
            }
            .map(parsed => TypeApply(name, parsed))
        }

  private def typeTermToTypeExpr(term: Expr[Ind]): Option[TypeExpr] = {

    def parseTypeExprArgs(args: Seq[Expr[?]]): Option[Seq[TypeExpr]] =
      args.foldLeft[Option[Seq[TypeExpr]]](Some(Seq.empty))((acc, arg) => acc.flatMap(parsed => typeTermToTypeExpr(arg.asInstanceOf[Expr[Ind]]).map(parsed :+ _)))

    val (head, args) = unfoldAllApp(term)
    val maybeADT = ADT.allADTs.collectFirst {
      case adt if (head match
            case c: Constant[Ind] @unchecked => c.id == adt.semantic.id
            case _ => false
          ) =>
        adt
    }

    maybeADT
      .flatMap(adt => parseTypeExprArgs(args).map(typeArgs => if typeArgs.isEmpty then TypeRef(adt.name) else TypeApply(adt.name, typeArgs)))
      .orElse(
        head match
          case c: Constant[Ind] @unchecked =>
            parseTypeExprArgs(args).flatMap(parsedArgs =>
              parseTypeExprRepr(c.id.name).map {
                case TypeRef(name) if parsedArgs.nonEmpty => TypeApply(name, parsedArgs)
                case base if parsedArgs.isEmpty => base
                case _ => TypeApply(c.id.name, parsedArgs)
              }
            )
          case _ => None
      )
  }

  private def inferADTFromTypeTerm(
      typeTerm: Expr[Ind]
  ): Option[SpecializedADT[?]] = typeTermToTypeExpr(typeTerm)
    .flatMap((tpe: TypeExpr) => ADT.unapply(tpe))
    .map { case (adt, typeArgs) =>
      adt.specialize(typeArgs.map(typeExprToTerm)*)
    }

  /**
   *  Infers the variable, the ADT and the arguments of the ADT from a formula of the form
   *  `x :: ADT(T1, ..., Tn)`.
   *
   *  @param f the formula to infer these elements from
   */
  def inferArguments(f: Expr[Prop]): Option[(Variable[Ind], SpecializedADT[?])] =

    f match
      case TypeAssign(Variable[Ind](id), typeTerm) =>
        inferADTFromTypeTerm(typeTerm)
          .flatMap { foundADT =>
            checkFoundArguments(Variable[Ind](id), foundADT)
          }
      case _ => None

  /**
   *  Infers the variable, the ADT and the arguments of the ADT from a set of formula
   *  containing one is of the form `x :: ADT(T1, ..., Tn)`.
   *
   *  @param s the set of formula to infer these elements from
   */
  def inferArguments(
      s: Set[Expr[Prop]]
  ): Option[(Variable[Ind], SpecializedADT[?])] = s
    .foldLeft[Option[(Variable[Ind], SpecializedADT[?])]](None)((acc, prem) => acc.orElse(inferArguments(prem)))

  /**
   *  Infers the variable, the ADT and the arguments of the ADT from a sequent whose one
   *  of the premises is of the form `x :: ADT(T1, ..., Tn)`.
   *
   *  @param seq the sequent to infer these elements from
   */
  def inferArguments(
      seq: Sequent
  ): Option[(Variable[Ind], SpecializedADT[?], Option[Expr[Prop]])] = inferArguments(
    seq.left
  ).map(p => (p._1, p._2, None))
    .orElse(
      seq.right.head match
        case forall(x, implies(assignment, prop)) =>
          inferArguments(assignment)
            .filter(p => p._1 == x)
            .map(p => (p._1, p._2, Some(prop)))
        case _ => None
    )

  /**
   *  Fallback when ADT typing is not explicitly present in the sequent context.
   *
   *  This enables calls such as `Induction(x, nat)` on goals of the form `|- P(x)`.
   */
  private val inferArgumentsFromExpected: Option[(Variable[Ind], SpecializedADT[?], Option[Expr[Prop]])] =
    (expectedVar, expectedADT) match
      case (Some(v), Some(a)) =>
        Some((v, a, None))
      case _ => None

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
    inferArguments(bot).orElse(inferArgumentsFromExpected) match
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

          val maybeSimpleCases = builder.validateAndBuild(inferedADT.base.asInstanceOf[ADT[N]])
          val compiledPatternSystem = builder.compilePatterns(inferedADT.asInstanceOf[SpecializedADT[N]])
          val compiledBranchSystem = builder.compileForInduction(inferedADT.asInstanceOf[SpecializedADT[N]])

          (maybeSimpleCases, compiledPatternSystem, compiledBranchSystem) match
            case (Right(cases), _, _) =>
              TacticSubproof { sp ?=>
                proveForallPredicate(using sp)(
                  cases,
                  inferedVar,
                  inferedADT.asInstanceOf[SpecializedADT[N]],
                  prop,
                  context
                )
                if !inferedProp.isDefined then
                  lastStep.statement.right.head match
                    case forall(_, phi) =>
                      thenHave(context |- phi) by
                        InstantiateForall(inferedVar)
                    case _ => throw UnreachableException

                thenHave(bot) by Tautology
              }
            case (Left(_), Right(patternSystem), Right(branchSystem)) if !branchSystem.supportsSingleBranchPerConstructor =>
              TacticSubproof { sp ?=>
                val specializedAdt = inferedADT.asInstanceOf[SpecializedADT[N]]
                val typedPatternSystem = patternSystem.asInstanceOf[PatternSystem[N]]
                val typedBranchSystem = branchSystem.asInstanceOf[InductionBranchSystemWithPayload[N, proof.ProofStep]]
                val typeVariablesSubstPairs =
                  specializedAdt.base.typeVariablesSeq.zip(specializedAdt.typeArgs).map(SubstPair(_, _))
                val instantiatedInduction = have(
                  specializedAdt.base.semantic.induction.statement.substitute((typeVariablesSubstPairs :+ (P := prop))*)
                ) by Restate.from(
                  specializedAdt.base.semantic.induction.of((typeVariablesSubstPairs :+ (P := prop))*)
                )

                specializedAdt.base.constructors.foldLeft[sp.Fact](instantiatedInduction)((acc, constructor) =>
                  val branchPairs = typedBranchSystem.branchesFor(constructor).map(p => (p.branch, p.payload))
                  val inductiveCaseProof = proveConstructorFromBranches(using sp)(
                    constructor,
                    branchPairs,
                    typedPatternSystem,
                    specializedAdt,
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
                  context |- forall(
                    inferedVar,
                    inferedVar :: specializedAdt.term ==> body
                  )
                ) by Tautology
                if !inferedProp.isDefined then
                  lastStep.statement.right.head match
                    case forall(_, phi) => thenHave(context |- phi) by InstantiateForall(inferedVar)
                    case _ => throw UnreachableException
                thenHave(bot) by Tautology
              }
            case (Left(msg), _, _) => proof.InvalidProofTactic(msg)

      case None =>
        proof
          .InvalidProofTactic("No variable typed with the ADT found in the context.")
  }

}

/**
 * Placeholder for ADT v2 induction tactic implementation.
 */
object Induction {
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
