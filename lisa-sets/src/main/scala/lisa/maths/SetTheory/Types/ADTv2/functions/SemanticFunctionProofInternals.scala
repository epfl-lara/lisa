package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Base.{Comprehension, CartesianProduct}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.maths.SetTheory.Functions.Pi.{->:}
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall

private[functions] final class SemanticFunctionProofInternals[N <: Arity](
    adt: SemanticADT[N],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    returnType: Expr[Ind],
    checkReturnType: Map[SemanticConstructor[N], THM],
    typ: Expr[Ind]
) {

  private val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq

  val untypedDefinition = (f :: typ) /\ simplify(seqAnd(cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    forallSeq(
      vars,
      wellTypedFormula(c.semanticSignature(vars)) ==> (f * c.appliedTerm(vars) === body)
    )
  )))

  private val pairWitness = variable[Ind]

  private val caseMembership = (p: Expr[Ind]) => seqOr(cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    val freshVars = c.variables2
    val freshBody = body
      .substitute(vars.zip(freshVars).map((from, to) => from := to)*)
      .asInstanceOf[Expr[Ind]]
    existsSeq(
      freshVars,
      wellTypedFormula(c.semanticSignature2) /\ (p === pair(c.appliedTerm2, freshBody))
    )
  ))

  private val witnessBound = lisa.maths.SetTheory.Base.CartesianProduct.×(adt.term)(returnType)
  private val witness = { pairWitness ∈ witnessBound | caseMembership(pairWitness) }

  private def constructorTagDisequality(c1: SemanticConstructor[N], c2: SemanticConstructor[N]): THM = {
    require(c1 != c2, "constructorTagDisequality requires two distinct constructors.")

    val tagTerm1 = c1.underlying.tagTerm
    val tagTerm2 = c2.underlying.tagTerm

    val minTag: Int = Math.min(c1.underlying.tag, c2.underlying.tag)
    val maxTag: Int = Math.max(c1.underlying.tag, c2.underlying.tag)

    Lemma(!(tagTerm1 === tagTerm2)) {
      val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Congruence

      (1 to minTag).foldLeft(start)((fact, i) =>
        val midMaxTag = toTerm(maxTag - i)
        val midMinTag = toTerm(minTag - i)
        have(
          successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag
        ) by Cut(
          successorInjectivity of (n := midMaxTag, m := midMinTag),
          equivalenceApply of (
            p1 := successor(midMaxTag) === successor(midMinTag),
            p2 := midMaxTag === midMinTag
          )
        )
        have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
      )

      val chainInjectivity =
        thenHave(!(toTerm(maxTag - minTag) === ∅) |- !(tagTerm1 === tagTerm2)) by Restate

      have(toTerm(maxTag - minTag) =/= ∅) by Restate.from(
        zeroIsNotSucc of (n := toTerm(maxTag - minTag - 1))
      )

      have(thesis) by Cut(lastStep, chainInjectivity)
    }
  }

  private lazy val constructorTagDisequalities: Map[(SemanticConstructor[N], SemanticConstructor[N]), THM] =
    (for
      c1 <- adt.constructors
      c2 <- adt.constructors
      if c1 != c2
    yield (c1, c2) -> constructorTagDisequality(c1, c2)).toMap

  private def constructorApplicationTyping(
      c: SemanticConstructor[N],
      args: Seq[Variable[Ind]]
  ): THM = Lemma(
    wellTypedFormula(c.semanticSignature(args)) |- (c.appliedTerm(args) :: adt.term)
  ) {
    have(forallSeq(typeVariablesSeq, c.term(typeVariablesSeq) :: c.typ)) by Restate.from(c.intro)

    val introAtTypeVars = typeVariablesSeq.foldLeft(lastStep)((fact, typeVariable) =>
      fact.statement.right.head match
        case forall(_, phi) => thenHave(phi) by InstantiateForall(typeVariable)
        case _ => fact
    )

    val argsWellTyped = assume(wellTypedFormula(c.semanticSignature(args)))

    val finalTyping = args.foldLeft(
      (introAtTypeVars, c.term(typeVariablesSeq): Expr[Ind], c.typ: Expr[Ind])
    ) { case ((accFact, accTerm, accType), argument) =>
      accType match
        case domainTy ->: codomainTy =>
          val argumentTyping = have(wellTypedFormula(c.semanticSignature(args)) |- argument :: domainTy) by
            Tautology.from(argsWellTyped)
          val nextTyping = have(
            wellTypedFormula(c.semanticSignature(args)) |- (accTerm * argument) :: codomainTy
          ) by Tautology.from(
            accFact,
            funEqDef of (f := accTerm, a := domainTy, b := codomainTy, x := argument),
            argumentTyping
          )
          (nextTyping, accTerm * argument, codomainTy)
        case _ => throw UnreachableException
    }._1

    have(thesis) by Restate.from(finalTyping)
  }

  private val witnessDefinition = untypedDefinition.substitute(f := witness)

  private val witnessCases = simplify(seqAnd(cases.map((c, caseDef) =>
    val (vars, body) = caseDef
    forallSeq(
      vars,
      wellTypedFormula(c.semanticSignature(vars)) ==> (witness * c.appliedTerm(vars) === body)
    )
  )))

  private val witnessHasTypeProof = new SemanticFunctionWitnessHasType[N](
    adt = adt,
    cases = cases,
    returnType = returnType,
    checkReturnType = checkReturnType,
    typ = typ,
    witness = witness,
    witnessBound = witnessBound,
    pairWitness = pairWitness,
    caseMembership = caseMembership,
    constructorApplicationTyping = (c, args) => constructorApplicationTyping(c, args),
    constructorTagDisequalities = constructorTagDisequalities
  )

  private lazy val witnessMembershipByConstructor: Map[SemanticConstructor[N], THM] =
    witnessHasTypeProof.witnessMembershipByConstructor

  private val witnessHasType: THM = witnessHasTypeProof.witnessHasType

  private val witnessCaseByConstructorProof = new SemanticFunctionWitnessCaseByConstructor[N](
    adt = adt,
    cases = cases,
    returnType = returnType,
    witness = witness,
    witnessHasType = witnessHasType,
    witnessMembershipByConstructor = witnessMembershipByConstructor,
    constructorApplicationTyping = (c, args) => constructorApplicationTyping(c, args)
  )

  private lazy val witnessCaseByConstructor: Map[SemanticConstructor[N], THM] =
    witnessCaseByConstructorProof.witnessCaseByConstructor

  val uniqueness = Lemma(existsOne(f, untypedDefinition)) {
    val definitionFormula = (v: Variable[Ind]) => untypedDefinition.substitute(f := v)

    val constructorCaseFacts = cases.keys.toSeq.map(c => witnessCaseByConstructor(c))
    have(witnessCases) by Tautology.from(constructorCaseFacts*)

    have(witnessDefinition) by Tautology.from(lastStep, witnessHasType)
    val existence = thenHave(∃(f, untypedDefinition)) by RightExists

    val existencePart = have(∃(x, definitionFormula(x))) by Restate.from(existence of (f := x))
    val uniquenessPointwise =
      have(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) subproof {
        assume(definitionFormula(x) /\ definitionFormula(y))
        val xDefinition = have(definitionFormula(x)) by Tautology
        val yDefinition = have(definitionFormula(y)) by Tautology

        val xTyped = have(x :: typ) by Tautology.from(xDefinition)
        val yTyped = have(y :: typ) by Tautology.from(yDefinition)

        val xBetween = have(Function.functionBetween(x)(adt.term)(returnType)) by Tautology.from(
          BasicTheorems.funcBetweenEqInFuncSpace of (
            f := x,
            A := adt.term,
            B := returnType
          ),
          xTyped
        )
        val yBetween = have(Function.functionBetween(y)(adt.term)(returnType)) by Tautology.from(
          BasicTheorems.funcBetweenEqInFuncSpace of (
            f := y,
            A := adt.term,
            B := returnType
          ),
          yTyped
        )

        val xOnDomain = have(Function.functionOn(x)(adt.term)) by Tautology.from(
          BasicTheorems.functionBetweenIsFunctionOn of (
            f := x,
            A := adt.term,
            B := returnType
          ),
          xBetween
        )
        val yOnDomain = have(Function.functionOn(y)(adt.term)) by Tautology.from(
          BasicTheorems.functionBetweenIsFunctionOn of (
            f := y,
            A := adt.term,
            B := returnType
          ),
          yBetween
        )

        val pointInput = variable[Ind]
        val constructorBranch = adt.constructors.map(c =>
          c -> simplify(
            existsSeq(
              c.variables2,
              wellTypedFormula(c.semanticSignature2) /\ (pointInput === c.appliedTerm2)
            )
          )
        ).toMap
        val constructorDisjunction = simplify(seqOr(adt.constructors.map(c => constructorBranch(c))))

        val decompositionAtInput = have(pointInput ∈ adt.term |- constructorDisjunction) by
          Tautology.from(adt.elim of (x := pointInput))

        val branchEqualities = adt.constructors.map(c =>
          val (caseVars, caseBody) = cases(c)

          val directBranch = have(
            wellTypedFormula(c.semanticSignature2) /\ (pointInput === c.appliedTerm2) |- (x * pointInput === y * pointInput)
          ) subproof {
            assume(wellTypedFormula(c.semanticSignature2) /\ (pointInput === c.appliedTerm2))
            val argsTyped = have(wellTypedFormula(c.semanticSignature2)) by Tautology
            val pointEqCtor = have(pointInput === c.appliedTerm2) by Tautology

            val xCaseSchema = have(
              forallSeq(
                caseVars,
                wellTypedFormula(c.semanticSignature(caseVars)) ==> (x * c.appliedTerm(caseVars) === caseBody)
              )
            ) by Tautology.from(xDefinition)
            val yCaseSchema = have(
              forallSeq(
                caseVars,
                wellTypedFormula(c.semanticSignature(caseVars)) ==> (y * c.appliedTerm(caseVars) === caseBody)
              )
            ) by Tautology.from(yDefinition)

            val substitutions = caseVars.zip(c.variables2).map((from, to) =>
              lisa.utils.fol.FOL.SubstPair(from, to)
            )
            val instantiatedCaseBody: Expr[Ind] =
              caseBody.substitute(substitutions*).asInstanceOf[Expr[Ind]]

            val xCaseAtVars2 = caseVars.zip(c.variables2).foldLeft(xCaseSchema)((fact, varsPair) =>
              fact.statement.right.head match
                case forall(v, phi) =>
                  have(phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]) by InstantiateForall(varsPair._2)(fact)
                case _ => fact
            )
            val xAtCtor = xCaseAtVars2.statement.right.head match
              case _ ==> consequent =>
                have(consequent) by Tautology.from(xCaseAtVars2, argsTyped)
              case _ => throw UnreachableException

            val yCaseAtVars2 = caseVars.zip(c.variables2).foldLeft(yCaseSchema)((fact, varsPair) =>
              fact.statement.right.head match
                case forall(v, phi) =>
                  have(phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]) by InstantiateForall(varsPair._2)(fact)
                case _ => fact
            )
            val yAtCtor = yCaseAtVars2.statement.right.head match
              case _ ==> consequent =>
                have(consequent) by Tautology.from(yCaseAtVars2, argsTyped)
              case _ => throw UnreachableException

            val xAtInputArg = have(x * pointInput === x * c.appliedTerm2) by Congruence.from(pointEqCtor)
            val xAtInput = have(x * pointInput === instantiatedCaseBody) by
              Congruence.from(xAtInputArg, xAtCtor)

            val yAtInputArg = have(y * pointInput === y * c.appliedTerm2) by Congruence.from(pointEqCtor)
            val yAtInput = have(y * pointInput === instantiatedCaseBody) by
              Congruence.from(yAtInputArg, yAtCtor)
            val yAtInputRev = have(instantiatedCaseBody === y * pointInput) by
              Congruence.from(yAtInput)

            have(x * pointInput === y * pointInput) by Tautology.from(
              altEqualityTransitivity of (
                x := x * pointInput,
                y := instantiatedCaseBody,
                z := y * pointInput
              ),
              xAtInput,
              yAtInputRev
            )
          }

          val rawBranch = c.variables2.reverse.foldLeft(directBranch)((fact, v) =>
            thenHave(∃(v, fact.statement.left.head) |- (x * pointInput === y * pointInput)) by LeftExists
          )

          have(constructorBranch(c) |- (x * pointInput === y * pointInput)) by Tautology.from(rawBranch)
        )

        val equalityFromCases =
          if branchEqualities.size == 1 then
            have(constructorDisjunction |- (x * pointInput === y * pointInput)) by
              Restate.from(branchEqualities.head)
          else
            have(constructorDisjunction |- (x * pointInput === y * pointInput)) by
              LeftOr(branchEqualities*)

        have(pointInput ∈ adt.term |- (x * pointInput === y * pointInput)) by
          Cut(decompositionAtInput, equalityFromCases)
        thenHave(pointInput ∈ adt.term ==> (x * pointInput === y * pointInput)) by RightImplies
        val pointwiseOnDomain = thenHave(
          ∀(pointInput, pointInput ∈ adt.term ==> (x * pointInput === y * pointInput))
        ) by RightForall

        have(x === y) by Tautology.from(
          BasicTheorems.extensionality of (
            f := x,
            g := y,
            A := adt.term,
            x := pointInput
          ),
          xOnDomain,
          yOnDomain,
          pointwiseOnDomain
        )
        thenHave(thesis) by Tautology
      }

    val uniquenessAll = have(
      ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) subproof {
      have(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) by
        Restate.from(uniquenessPointwise)
      thenHave(∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y))) by RightForall
      thenHave(thesis) by RightForall
    }

    have(
      ∃(x, definitionFormula(x)) /\
        ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) by Tautology.from(existencePart, uniquenessAll)

    have(thesis) by Tautology.from(
      lastStep,
      lisa.maths.Quantifiers.existsOneAlternativeDefinition of (
        x := f,
        P := λ(f, untypedDefinition)
      )
    )
  }
}
