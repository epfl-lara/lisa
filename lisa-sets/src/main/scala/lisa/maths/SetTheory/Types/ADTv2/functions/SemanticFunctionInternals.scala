package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.Functions.Pi.{->:}
import lisa.maths.SetTheory.Base.CartesianProduct.×
import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.utils.prooflib.BasicStepTactic.Restate

private[functions] final class SemanticFunctionInternals[N <: Arity](
  functionName: String,
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

  private val witnessBody = { pairWitness ∈ (adt.term × returnType) | caseMembership(pairWitness) }

  // Keep the witness as a polymorphic DEF-backed symbol (same pattern as recursive internals).
  private val witnessClass: Constant[?] = {
    val witnessExpr: Expr[?] = lisa.utils.fol.FOL.Abs.apply(
      xs = typeVariablesSeq,
      t = witnessBody
    )
    type S
    given lisa.utils.fol.FOL.IsSort[S] =
      lisa.utils.fol.FOL.unsafeSortEvidence(witnessExpr.sort)
    DEF(using name = s"${functionName}/witness")(witnessExpr.asInstanceOf[Expr[S]])
  }

  private val witness: Expr[Ind] =
    (witnessClass #@@ typeVariablesSeq).asInstanceOf[Expr[Ind]]

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
    have(c.term(typeVariablesSeq) :: c.typ) by Restate.from(c.intro)

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

  private val witnessHasTypeProof = new WitnessTyping[N](
    adt = adt,
    cases = cases,
    returnType = returnType,
    checkReturnType = checkReturnType,
    typ = typ,
    witness = witness,
    witnessDef = witnessClass.definition,
    witnessBound = adt.term × returnType,
    pairWitness = pairWitness,
    caseMembership = caseMembership,
    constructorApplicationTyping = (c, args) => constructorApplicationTyping(c, args),
    constructorTagDisequalities = constructorTagDisequalities
  )

  private lazy val witnessMembershipByConstructor: Map[SemanticConstructor[N], THM] =
    witnessHasTypeProof.witnessMembershipByConstructor

  private val witnessHasType: THM = witnessHasTypeProof.witnessHasType

  private val witnessCaseByConstructorProof = new WitnessCases[N](
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

  private val extensionalUniqueness = new ExtensionalUniqueness[N](
    adt = adt,
    cases = cases,
    returnType = returnType,
    typ = typ,
    untypedDefinition = untypedDefinition
  )

  val uniqueness = Lemma(existsOne(f, untypedDefinition)) {
    val definitionFormula = (v: Variable[Ind]) => untypedDefinition.substitute(f := v)

    val constructorCaseFacts = cases.keys.toSeq.map(c => witnessCaseByConstructor(c))
    have(witnessCases) by Tautology.from(constructorCaseFacts*)

    have(witnessDefinition) by Tautology.from(lastStep, witnessHasType)
    val existence = thenHave(∃(f, untypedDefinition)) by RightExists

    val existencePart = have(∃(x, definitionFormula(x))) by Restate.from(existence of (f := x))
    val uniquenessPointwise = have(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) by
      Restate.from(extensionalUniqueness.nonRecursivePointwise)

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
      existsOneAlternativeDefinition of (
        x := f,
        P := λ(f, untypedDefinition)
      )
    )
  }
}
