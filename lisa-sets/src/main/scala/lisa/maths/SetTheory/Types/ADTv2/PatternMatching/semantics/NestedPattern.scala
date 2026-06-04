package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Types.ADTv2.encoding.{SemanticADT, SemanticConstructor}
import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity, constructorTagDisequality}
import lisa.utils.prooflib.BasicStepTactic.{LeftExists, LeftOr, RightExists, RightForall}
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * A constructor-headed pattern where some arguments are compiled into branch
 * guards instead of being kept as user binders.
 *
 * For example, `cons(tru, tl)` is represented with binders `(_cons0, tl)` and
 * branch condition `_cons0 === tru`.
 */
final case class ResolvedNullaryGuard(
    constructor: Constructor[?],
    appliedTerm: Expr[Ind]
)

final case class BranchGuard(
    position: Int,
    binder: Variable[Ind],
    guardTerm: Expr[Ind],
    resolvedNullary: Option[ResolvedNullaryGuard]
)

final case class NestedConstructorPattern[N <: Arity](
    semanticConstructor: SemanticConstructor[N],
    binders: Seq[Variable[Ind]],
    body: Expr[Ind],
    override val branchCondition: Expr[Prop],
    guards: Seq[BranchGuard],
    override val typeSubstitutions: Seq[TypeSubstitution] = Seq.empty,
    override val specializedAdtTerm: Expr[Ind]
) extends ConstructorHeadPattern[N] {
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

  override def withBody(newBody: Expr[Ind]): Pattern[N] = copy(body = newBody)
}

object NestedConstructorPattern {
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
    val binders: Seq[Variable[Ind]] = args.zipWithIndex.map {
      case (Left(v), _)  => v
      case (Right(_), i) => variable[Ind](s"${constructor.name}/arg$i")
    }
    val guards: Seq[BranchGuard] = args.zipWithIndex.collect {
      case (Right(term), i) =>
        BranchGuard(
          position = i,
          binder = binders(i),
          guardTerm = term,
          resolvedNullary = resolveNullaryGuard(term)
        )
    }
    val conditions: Seq[Expr[Prop]] = args.zip(binders).collect {
      case (Right(term), binder) => binder === term
    }
    val condition = conditions match
      case Nil          => ⊤
      case head +: tail => tail.foldLeft(head)(_ /\ _)
    NestedConstructorPattern(constructor, binders, body, condition, guards, typeSubstitutions, specializedAdtTerm)
}

/**
 * Pattern system supporting several guarded branches for the same constructor.
 *
 * Proof obligations are intentionally left open for now.
 */
final case class NestedPatternSystem[N <: Arity](
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

  override def coverage(domain: SemanticADT[N]): THM = {
    require(domain == this.domain, "NestedPatternSystem.coverage expects its compiled base domain.")
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
                case premise ==> consequent =>
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
  ): THM = {
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
  }

  override def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM = {
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
  }

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
        case premise ==> consequent => have(consequent) by Tautology.from(constructor1Def)
        case consequent            => have(consequent) by Tautology.from(constructor1Def)
      val constructor2Def = have(constructor2.shortDefinition.statement.right.head) by
        Tautology.from(constructor2.shortDefinition)
      val constructor2Eq = constructor2Def.statement.right.head match
        case premise ==> consequent => have(consequent) by Tautology.from(constructor2Def)
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
      val tagsFromStructuralEq = have(
        constructor1.structuralTerm1 === constructor2.structuralTerm2 |-
          (constructor1.underlying.tagTerm === constructor2.underlying.tagTerm) /\
          (constructor1.underlying.subterm1 === constructor2.underlying.subterm2)
      ) by Tautology.from(
        Pair.extensionality of (
          a := constructor1.underlying.tagTerm,
          b := constructor1.underlying.subterm1,
          c := constructor2.underlying.tagTerm,
          d := constructor2.underlying.subterm2
        )
      )
      val tagsEqual = have(constructor1.underlying.tagTerm === constructor2.underlying.tagTerm) by
        Tautology.from(structuralEq, tagsFromStructuralEq)
      val minTag = Math.min(constructor1.underlying.tag, constructor2.underlying.tag)
      val maxTag = Math.max(constructor1.underlying.tag, constructor2.underlying.tag)
      val tagsDifferent = have(!(constructor1.underlying.tagTerm === constructor2.underlying.tagTerm)) by
        Tautology.from(
          constructorTagDisequality(
            constructor1.underlying.tagTerm,
            constructor2.underlying.tagTerm,
            minTag,
            maxTag
          )
        )
      have(thesis) by Tautology.from(tagsEqual, tagsDifferent)
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

object NestedPatternSystem {
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
