package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.Quantifiers.universalEquivalenceDistribution
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedTheorem
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.normalizeTypeSubstitutions
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.resolvedTypeArguments
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.theoremAt
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.**
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

/**
 *  Semantic set theoretical interpretation of an algebraic data type. That is the least
 *  set closed under [[SemanticConstructor]].
 *
 *  E.g. list is the smallest set containing nil and closed under the cons function.
 *
 *  Injectivity between different constructors, structural induction and elimination rule
 *  are proved within this class.
 *
 *  Exported semantic lemmas are kept in formula form. Type variables and the induction
 *  predicate remain schematic, while value arguments are explicitly quantified.
 *
 *  @constructor generates a semantic interpretation for this ADT out of a syntactic one
 *  @param underlying the syntactic representation of this ADT
 *  @param constructors constructors of this ADT
 */
class SemanticADT[N <: Arity](
    val underlying: SyntacticADT[N],
    val constructors: Seq[SemanticConstructor[N]]
) {

  private def normalizedTypeArguments(
      substitutions: Seq[TypeSubstitution]
  ): Seq[Expr[Ind]] =
    resolvedTypeArguments(
      typeVariablesSeq,
      normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions)
    )

  final class HeightAdapter private[SemanticADT] () {
    def predicate(h: Expr[Ind]): Expr[Prop] = underlying.isHeight(h)
    lazy val function: Expr[Ind] = underlying.height
    lazy val valid: THM = underlying.heightValid
    val exists: THM = underlying.heightExists
    val monotonic: THM = underlying.heightMonotonic
    val membershipMonotonic: THM = underlying.heightMembershipMonotonic
    val successorInclusion: THM = underlying.heightSuccessorInclusion
    val zero: THM = underlying.heightZero
    val successorStrong: THM = underlying.heightSuccessorStrong
    val termHasHeight: THM = underlying.termHasHeight
    def termsHaveHeight(c: SyntacticConstructor): THM = underlying.termsHaveHeight(c)
    def termsHaveHeight(c: SemanticConstructor[N]): THM = underlying.termsHaveHeight(c.underlying)

    def validAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/valid",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = valid
      )

    def existsAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/exists",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = exists
      )

    def monotonicAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/monotonic",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = monotonic
      )

    def zeroAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/zero",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = zero
      )

    def membershipMonotonicAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/membershipMonotonic",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = membershipMonotonic
      )

    def successorInclusionAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/successorInclusion",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = successorInclusion
      )

    def successorStrongAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/successorStrong",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = successorStrong
      )

    def termHasHeightAt(
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/termHasHeight",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = termHasHeight
      )

    def termsHaveHeightAt(
        c: SyntacticConstructor,
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      instantiatedTheorem(
        theoremOwner = renderAppliedSymbol(name, typeVariablesSeq.size, normalizedTypeArguments(substitutions)),
        suffix = "height/termsHaveHeight",
        substitutions = normalizeTypeSubstitutions("ADT", name, typeVariablesSeq, substitutions),
        baseTheorem = termsHaveHeight(c)
      )

    def termsHaveHeightAt(
        c: SemanticConstructor[N],
        substitutions: Seq[TypeSubstitution]
    )(using sourcecode.Line, sourcecode.File): THM =
      termsHaveHeightAt(c.underlying, substitutions)
  }

  val height = HeightAdapter()

  /** Name of this ADT. */
  val name: String = underlying.name

  /** Identifier of this ADT. */
  val id: Identifier = underlying.polymorphicTerm.id

  /** Type variables of this ADT. */
  val typeVariables: Variable[Ind] ** N = underlying.typeVariables

  /** Sequence of type variables of this ADT. */
  val typeVariablesSeq: Seq[Variable[Ind]] = underlying.typeVariablesSeq

  /** Number of type variables in this ADT. */
  val typeArity: N = underlying.typeArity

  /**
   *  Term representing this ADT where type variables are instantiated with given
   *  arguments.
   *
   *  @param args the instances of this ADT type variables
   */
  def term(args: Seq[Expr[Ind]]) = underlying.termAt(args)

  /**
   *  Term representing this ADT where type variables are instantiated with schematic
   *  variables.
   */
  val term: Expr[Ind] = underlying.term

  /**
   *  Theorem --- Injectivity of constructors.
   *
   *  Two instances of different construcors are always different.
   *
   *  e.g. Nil != Cons(head, tail)
   */
  def injectivity(c1: SemanticConstructor[N], c2: SemanticConstructor[N]) =

    val vars1WellTyped: Set[Expr[Prop]] = wellTypedSet(c1.semanticSignature1)
    val vars2WellTyped: Set[Expr[Prop]] = wellTypedSet(c2.semanticSignature2)
    val typedAssumption =
      simplify(wellTypedFormula(c1.semanticSignature1 ++ c2.semanticSignature2))

    Lemma(forallSeq(
      c1.variables1 ++ c2.variables2,
      typedAssumption ==> !(c1.appliedTerm1 === c2.appliedTerm2)
    )) {

      val defUnfolding = have(
        (vars1WellTyped ++ vars2WellTyped) + (c1.appliedTerm1 === c2.appliedTerm2) |-
          c1.structuralTerm1 === c2.structuralTerm2
      ) subproof {
        have(forallSeq(
          c1.variables1,
          wellTypedFormula(c1.semanticSignature1) ==>
            (c1.appliedTerm1 === c1.structuralTerm1)
        )) by Restate.from(c1.shortDefinition)

        c1.variables1.foldLeft(lastStep)((fact, v) =>
          fact.statement.right.head match
            case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )

        val tappTerm1Def =
          thenHave(vars1WellTyped |- c1.structuralTerm1 === c1.appliedTerm1) by Restate
          

        have(forallSeq(
          c2.variables2,
          wellTypedFormula(c2.semanticSignature2) ==>
            (c2.appliedTerm2 === c2.structuralTerm2)
        )) by Restate.from(c2.shortDefinition)

        c2.variables2.foldLeft(lastStep)((fact, v) =>
          fact.statement.right.head match
            case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        val tappTerm2Def =
          thenHave(vars2WellTyped |- c2.appliedTerm2 === c2.structuralTerm2) by Restate

        val s0 = have(
          vars2WellTyped + (c1.appliedTerm1 === c2.appliedTerm2) |-
            c1.appliedTerm1 === c2.structuralTerm2
        ) by Cut(
          tappTerm2Def,
          altEqualityTransitivity of
            (x := c1.appliedTerm1, y := c2.appliedTerm2, z := c2.structuralTerm2)
        )
        have(
          vars1WellTyped + (c1.appliedTerm1 === c2.structuralTerm2) |-
            c1.structuralTerm1 === c2.structuralTerm2
        ) by Cut(
          tappTerm1Def,
          altEqualityTransitivity of
            (x := c1.structuralTerm1, y := c1.appliedTerm1, z := c2.structuralTerm2)
        )
        have(thesis) by Cut(s0, lastStep)
      }

      have(!(c1.structuralTerm1 === c2.structuralTerm2)) by
        Restate.from(underlying.injectivity(c1.underlying, c2.underlying))
      thenHave(c1.structuralTerm1 === c2.structuralTerm2 |- ()) by Restate

      val contradiction = have(
        (vars1WellTyped ++ vars2WellTyped) + (c1.appliedTerm1 === c2.appliedTerm2) |- ()
      ) by Cut(defUnfolding, lastStep)

      val disjointness = thenHave(
        vars1WellTyped ++ vars2WellTyped |- !(c1.appliedTerm1 === c2.appliedTerm2)
      ) by Restate

      have(typedAssumption ==> !(c1.appliedTerm1 === c2.appliedTerm2)) subproof {
        assume(typedAssumption)
        val typed = have(typedAssumption) by Hypothesis
        have(!(c1.appliedTerm1 === c2.appliedTerm2)) by Tautology.from(disjointness, typed)
      }
      thenHave(thesis) by QuantifiersIntro(c1.variables1 ++ c2.variables2)
    }

  /**
   *  Theorem --- Structural induction principle for this ADT.
   *
   *  `base cases => inductive cases => ∀x ∈ ADT. P(x)`
   */
  val induction = Lemma(
    constructors.foldRight[Expr[Prop]](forall(x, x :: term ==> P(x)))((c, f) =>
      c.inductiveCase ==> f
    )
  ) { sp ?=>
    constructors.foldRight[(Expr[Prop], Expr[Prop], sp.Fact)] {
      val prop = forall(x, x :: term ==> P(x))
      (prop, prop, have(prop <=> prop) by Restate)
    }((c, acc) =>
      val (oldBefore, oldAfter, fact) = acc
      val newBefore = underlying.inductiveCase(c.underlying) ==> oldBefore
      val newAfter = c.inductiveCase ==> oldAfter

      have(underlying.inductiveCase(c.underlying) <=> c.inductiveCase) subproof {
        val wellTypedVars: Seq[Expr[Prop]] = wellTyped(c.semanticSignature)
        val wellTypedVarsSet = wellTypedVars.toSet

        have(forallSeq(
          c.variables,
          wellTypedFormula(c.semanticSignature) ==> (c.appliedTerm === c.structuralTerm)
        )) by Restate.from(c.shortDefinition)
        if c.arity > 0 then
          c.variables1.foldLeft(lastStep)((l, _) =>
            lastStep.statement.right.head match
              case forall(v, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException
          )

        val eq = thenHave(wellTypedVarsSet |- c.appliedTerm === c.structuralTerm) by
          Restate
        have(P(c.appliedTerm) <=> P(c.appliedTerm)) by Restate
        thenHave(
          c.structuralTerm === c.appliedTerm |- P(c.structuralTerm) <=> P(c.appliedTerm)
        ) by RightSubstEq.withParameters(
          List((c.structuralTerm, c.appliedTerm)),
          (Seq(s), P(s) <=> P(c.appliedTerm))
        )
        have(wellTypedVarsSet |- P(c.structuralTerm) <=> P(c.appliedTerm)) by
          Cut(eq, lastStep)

        c.syntacticSignature.foldRight[(Expr[Prop], Expr[Prop], Seq[Expr[Prop]])](
          (P(c.structuralTerm), P(c.appliedTerm), wellTypedVars)
        )((el, fc) =>
          val (v, ty) = el
          val (fc1, fc2, wellTypedVars) = fc
          ty match
            case SelfRef =>
              val wellTypedV: Expr[Prop] = v :: term
              have(wellTypedVars |- (P(v) ==> fc1) <=> (P(v) ==> fc2)) by Cut(
                lastStep,
                leftImpliesEquivalenceWeak of (p := P(v), p1 := fc1, p2 := fc2)
              )
              thenHave(
                wellTypedVars.init |- wellTypedV ==> ((P(v) ==> fc1) <=> (P(v) ==> fc2))
              ) by RightImplies
              have(
                wellTypedVars.init |- (wellTypedV ==> (P(v) ==> fc1)) <=>
                  (wellTypedV ==> (P(v) ==> fc2))
              ) by Cut(
                lastStep,
                leftImpliesEquivalenceStrong of
                  (p := wellTypedV, p1 := P(v) ==> fc1, p2 := P(v) ==> fc2)
              )
              thenHave(
                wellTypedVars.init |- forall(
                  v,
                  (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2))
                )
              ) by RightForall
              have(
                wellTypedVars.init |-
                  forall(v, wellTypedV ==> (P(v) ==> fc1)) <=>
                  forall(v, wellTypedV ==> (P(v) ==> fc2))
              ) by Cut(
                lastStep,
                universalEquivalenceDistribution of
                  (
                    P := lambda(v, wellTypedV ==> (P(v) ==> fc1)),
                    Q := lambda(v, wellTypedV ==> (P(v) ==> fc2))
                  )
              )
              (
                forall(v, wellTypedV ==> (P(v) ==> fc1)),
                forall(v, wellTypedV ==> (P(v) ==> fc2)),
                wellTypedVars.init
              )
            // case RegularArg(t_) =>
            case TypeArg(typeName) =>
              val t = typeExprToTerm(typeName)
              thenHave(wellTypedVars.init |- v :: t ==> (fc1 <=> fc2)) by RightImplies
              have(wellTypedVars.init |- (in(v, t) ==> fc1) <=> (v :: t ==> fc2)) by Cut(
                lastStep,
                leftImpliesEquivalenceStrong of (p := in(v, t), p1 := fc1, p2 := fc2)
              )
              thenHave(
                wellTypedVars.init |- forall(v, (in(v, t) ==> fc1) <=> (v :: t ==> fc2))
              ) by RightForall
              have(
                wellTypedVars.init |-
                  forall(v, in(v, t) ==> fc1) <=> forall(v, v :: t ==> fc2)
              ) by Cut(
                lastStep,
                universalEquivalenceDistribution of
                  (P := lambda(v, in(v, t) ==> fc1), Q := lambda(v, v :: t ==> fc2))
              )
              (forall(v, in(v, t) ==> fc1), forall(v, v :: t ==> fc2), wellTypedVars.init)
        )
        have(thesis) by Restate.from(lastStep)
      }
      val newFact = have(newBefore <=> newAfter) by Tautology.from(impliesEquivalence, lastStep, fact)
      (newBefore, newAfter, newFact)
    )
    have(underlying.induction.statement.right.head |- thesis.right.head) by Cut(
      lastStep,
      equivalenceApply of (
        p1 := underlying.induction.statement.right.head, p2 := thesis.right.head
      )
    )
    have(thesis) by Cut(underlying.induction, lastStep)
  }

  /**
   *  Returns a map binding each constructor to formula describing whether x is an
   *  instance of it.
   */
  private lazy val isConstructorMap: Map[SemanticConstructor[N], Expr[Prop]] =
    constructors.map(c =>
      c -> existsSeq(
        c.variables2,
        wellTypedFormula(c.semanticSignature2) /\ (x === c.appliedTerm2)
      )
    ).toMap

  /**
   *  Returns a formula describing whether x is an instance of one of this ADT's
   *  constructors.
   */
  private lazy val isConstructor = seqOr(constructors.map(c => isConstructorMap(c)))

  /**
   *  Theorem --- Pattern matching principle (also known as elimination rule) for this
   *  ADT.
   *
   *  `∀x. x ∈ ADT ==> x = c * x1 * ... * xn for some constructor c and xi, ..., xj ∈ ADT`
   */
  lazy val elim = Lemma(forall(x, x :: term ==> simplify(isConstructor))) {

    // Induction preconditions with P(z) = z != x
    val inductionPreconditionIneq = constructors
      .map(c =>
        c -> betaReduce(c.inductiveCase.substitute(P -> lambda(z, !(x === z))))
      )
      .toMap
    val inductionPreconditionsIneq = seqAnd(inductionPreconditionIneq.map(_._2))

    // Weakening of the negation of the induction preconditions
    val weakNegInductionPreconditionIneq: Map[SemanticConstructor[N], Expr[Prop]] =
      constructors.map(c =>
        c -> c.semanticSignature2.foldRight[Expr[Prop]](x === c.appliedTerm2)((el, fc) =>
          val (v, t) = el
          exists(v, (v :: t) /\ fc)
        )
      ).toMap

    // STEP 1: Prove that if the induction preconditions with P(z) = z != x do not hold then x is the instance of some constructor
    val strengtheningOfInductionPreconditions =
      have(!inductionPreconditionsIneq |- isConstructor) subproof {
        if constructors.isEmpty then have(thesis) by Restate
        else

          // STEP 1.1: Prove the claim for each constructor
          val negInductionPreconditionsOrSequence =
            for c <- constructors yield

              // STEP 1.1.1: Prove the strengthening of the negations of the induction preconditions
              val conditionStrenghtening = have(
                !inductionPreconditionIneq(c) |- weakNegInductionPreconditionIneq(c)
              ) subproof {

                val baseF = !(x === c.appliedTerm2)
                val baseW = x === c.appliedTerm2
                val seed = (baseF, baseW, have(!baseF |- baseW) by Restate)

                val (_, _, finalFact) = c.syntacticSignature(c.variables2).foldRight(seed)((el, acc) =>
                  val (v, ty) = el
                  val (currF, currW, currFact) = acc
                  val argType = ty.getOrElse(term)

                  have(!currF |- currW) by Restate.from(currFact)

                  val nextF = ty match
                    case SelfRef => 
                      thenHave(!(!(x === v) ==> currF) |- currW) by Tautology
                      (!(x === v) ==> currF)
                    case _ => 
                      currF

                  val nextF2 = (v :: argType) ==> nextF
                  thenHave( !nextF2 |- currW ) by Tautology

                  val newW = exists(v, (v :: argType) /\ currW)
                  thenHave(!nextF2 |- (v :: argType) /\ currW) by Restate
                  thenHave(!nextF2 |- newW) by RightExists

                  val newF = forall(v, nextF2)
                  thenHave(exists(v, !(nextF2)) |- newW) by LeftExists
                  
                  val newFact = have(!newF |- newW) by Tautology.from(lastStep, existsNeg)
                  
                  (newF, newW, newFact)
                )

                have(thesis) by Restate.from(finalFact)
              }

              // STEP 1.1.2: Conclude
              // `weakNegInductionPreconditionIneq(c)` is the *nested* existential
              //   ∃v1.((v1::t1) ∧ ∃v2.((v2::t2) ∧ … ∧ (x = c(v1,…,vk)))),
              // while `isConstructorMap(c)` is the *flat* one
              //   ∃v1…∃vk.((v1::t1) ∧ … ∧ (vk::tk) ∧ (x = c(v1,…,vk))).
              // They are first-order equivalent; rather than calling `Tableau`, peel the
              // nested ∃ accumulating the typing hypotheses, rebuild the flat ∃ with
              // `RightExists`, then fold the typings back in with `LeftExists`.
              have(weakNegInductionPreconditionIneq(c) |- isConstructorMap(c)) subproof {
                val sig = c.semanticSignature2
                val vars = c.variables2
                val base = x === c.appliedTerm2
                val typings: Seq[Expr[Prop]] = sig.map((v, t) => v :: t)
                val flatBody = wellTypedFormula(sig) /\ base

                // core: all typing hypotheses + base entail the flat existential.
                val coreFact = have((typings.toSet + base) |- isConstructorMap(c)) subproof {
                  assume((typings :+ base)*)
                  have(flatBody) by Restate
                  vars.indices.reverse.foreach { i =>
                    val phi = existsSeq(vars.drop(i + 1), flatBody)
                    thenHave(∃(vars(i), phi)) by RightExists.withParameters(phi, vars(i), vars(i))
                  }
                }

                // Fold each typing hypothesis back under its existential, rebuilding the
                // nested `weakNeg` formula incrementally as we go.
                var nested: Expr[Prop] = base
                var fact = coreFact
                for (i <- (vars.size - 1) to 0 by -1) {
                  val combined = (vars(i) :: sig(i)._2) /\ nested
                  val outer = typings.take(i).toSet
                  have((outer + combined) |- isConstructorMap(c)) by Restate.from(fact)
                  nested = ∃(vars(i), combined)
                  fact = thenHave((outer + nested) |- isConstructorMap(c)) by LeftExists
                }
                have(thesis) by Restate.from(fact)
              }
              have(!inductionPreconditionIneq(c) |- isConstructorMap(c)) by
                Cut(conditionStrenghtening, lastStep)
              thenHave(!inductionPreconditionIneq(c) |- isConstructor) by Weakening

          have(thesis) by LeftOr(negInductionPreconditionsOrSequence*)
      }

    // STEP 2: Conclude
    have(inductionPreconditionsIneq |- forall(z, z :: term ==> !(x === z))) by
      Restate.from(induction of (P := lambda(z, !(x === z))))
    thenHave(inductionPreconditionsIneq |- x :: term ==> !(x === x)) by
      InstantiateForall(x)
    val ind = thenHave(x :: term |- !inductionPreconditionsIneq) by Restate
    val eliminationCase = have(x :: term |- isConstructor) by
      Cut(lastStep, strengtheningOfInductionPreconditions)

    have(x :: term ==> simplify(isConstructor)) subproof {
      assume(x :: term)
      val xTyped = have(x :: term) by Hypothesis
      have(simplify(isConstructor)) by Tautology.from(eliminationCase, xTyped)
    }
    thenHave(thesis) by RightForall
  }

  def inductionAt(
      substitutions: Seq[TypeSubstitution]
  )(using sourcecode.Line, sourcecode.File): THM =
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = normalizedTypeArguments(substitutions),
      suffix = "induction",
      baseTheorem = induction
    )

  def elimAt(
      substitutions: Seq[TypeSubstitution]
  )(using sourcecode.Line, sourcecode.File): THM =
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = normalizedTypeArguments(substitutions),
      suffix = "elimination",
      baseTheorem = elim
    )

  def injectivityAt(
      c1: SemanticConstructor[N],
      c2: SemanticConstructor[N],
      substitutions: Seq[TypeSubstitution]
  )(using sourcecode.Line, sourcecode.File): THM =
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = normalizedTypeArguments(substitutions),
      suffix = s"${c1.name}-${c2.name}/injectivity",
      baseTheorem = injectivity(c1, c2)
    )

}
