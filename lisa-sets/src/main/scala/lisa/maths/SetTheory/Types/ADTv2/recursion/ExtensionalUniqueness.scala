package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.maths.SetTheory.Functions.Function.app
import lisa.utils.fol.FOL.App
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

type ConstructorSchemas[N <: Arity] =
  Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Prop])]

def asIndEquality(formula: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = formula match
  case App(App(eqFun, lhs: Expr[Ind]), rhs: Expr[Ind]) if eqFun == equality => Some((lhs, rhs))
  case _ => None

def splitConjunctions(formula: Expr[Prop]): Seq[Expr[Prop]] = formula match
  case left /\ right => splitConjunctions(left) ++ splitConjunctions(right)
  case other => Seq(other)

// ─────────────────────────────────────────────────────────────────────────────
// Induction skeletons
// ─────────────────────────────────────────────────────────────────────────────

private[recursion] object RecFunctionInduction {

  private def requireSchemaCoverage[N <: Arity](
      adt: SemanticADT[N],
      schemas: ConstructorSchemas[N],
      schemaLabel: String,
      functionName: String
  ): Unit = {
    val expectedConstructors = adt.constructors.toSet
    require(
      schemas.keySet == expectedConstructors,
      s"$schemaLabel($functionName): constructor schemas do not cover the ADT constructors."
    )
    adt.constructors.foreach(c =>
      val (vars, _) = schemas(c)
      require(
        vars.length == c.variables1.length,
        s"$schemaLabel($functionName): constructor schema for ${c.name} has arity ${vars.length}, expected ${c.variables1.length}."
      )
    )
  }

  private def instantiateSchemaAtBranch(using proof: lisa.SetTheoryLibrary.Proof)(
      localAssumptions: Set[Expr[Prop]],
      branchVars: Seq[Variable[Ind]],
      argsTyped: proof.Fact,
      schema: (Seq[Variable[Ind]], Expr[Prop]),
      schemaFact: proof.Fact,
      errorContext: String
  ): proof.Fact = {
    val (schemaVars, _) = schema

    require(
      schemaVars.length == branchVars.length,
      s"$errorContext: schema arity mismatch (${schemaVars.length} vs ${branchVars.length})."
    )

    val schemaAtBranch = schemaVars.zip(branchVars).foldLeft(schemaFact)((fact, varsPair) =>
      fact.statement.right.head match
        case forall(v, phi) =>
          val instantiated = phi.substitute(v := varsPair._2).asInstanceOf[Expr[Prop]]
          have(fact.statement.left |- instantiated) by InstantiateForall(varsPair._2)(fact)
        case _ => throw UnreachableException
    )

    schemaAtBranch.statement.right.head match
      case _ ==> consequent =>
        have(localAssumptions |- consequent.asInstanceOf[Expr[Prop]]) by Tautology.from(schemaAtBranch, argsTyped)
      case equalityFormula =>
        have(localAssumptions |- equalityFormula.asInstanceOf[Expr[Prop]]) by Restate.from(schemaAtBranch)
  }

  private def extractBodyAtConstructor(using proof: lisa.SetTheoryLibrary.Proof)(
      equalityAtConstructor: proof.Fact,
      functionHead: Expr[Ind],
      constructorTerm: Expr[Ind],
      constructorName: String,
      sideLabel: String
  ): Expr[Ind] = {
    asIndEquality(equalityAtConstructor.statement.right.head.asInstanceOf[Expr[Prop]]) match
      case Some((leftEq, rightEq)) =>
        if leftEq == (functionHead * constructorTerm) then rightEq
        else if rightEq == (functionHead * constructorTerm) then leftEq
        else
          throw IllegalArgumentException(
            s"Unexpected $sideLabel-constructor equality shape for $constructorName: ${equalityAtConstructor.statement.right.head}"
          )
      case _ =>
        throw IllegalArgumentException(
          s"Unexpected $sideLabel-constructor equality shape for $constructorName: ${equalityAtConstructor.statement.right.head}"
        )
  }

  private def proveBodyEqualityFromRecursiveFacts(using proof: lisa.SetTheoryLibrary.Proof)(
      localAssumptions: Set[Expr[Prop]],
      leftBody: Expr[Ind],
      rightBody: Expr[Ind],
      recursiveFacts: Seq[proof.Fact],
      constructorName: String,
      contextLabel: String
  ): proof.Fact = {
    if leftBody == rightBody then
      val refl = have(leftBody === rightBody) by RightRefl
      have(localAssumptions |- leftBody === rightBody) by Weakening(refl)
    else if recursiveFacts.nonEmpty then
      have(localAssumptions |- leftBody === rightBody) by Congruence.from(recursiveFacts*)
    else
      throw IllegalArgumentException(
        s"$contextLabel: constructor $constructorName has mismatching bodies without recursive arguments: $leftBody vs $rightBody."
      )
  }

  private def liftBranchToInductiveCase[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      adt: SemanticADT[N],
      syntacticSignature: Seq[(Variable[Ind], ConstructorArg)],
      propertyAt: Expr[Ind] => Expr[Prop],
      branchEquality: proof.Fact,
      selectSelfRefAssumption: (Variable[Ind], Set[Expr[Prop]]) => Expr[Prop]
  ): proof.Fact = {
    var liftedInductiveCase = branchEquality
    syntacticSignature.reverse.foreach((el) =>
      val (v, typ) = el
      val accRight = liftedInductiveCase.statement.right.head

      typ match
        case SelfRef =>
          val ihAssumptionAtVar = selectSelfRefAssumption(v, liftedInductiveCase.statement.left)
          val selfTypingAtVar = liftedInductiveCase.statement.left.find(typing =>
            typing == (v ∈ adt.term) || typing == (v :: adt.term)
          ).getOrElse(v ∈ adt.term)
          val ihLifted = have((liftedInductiveCase.statement -<? ihAssumptionAtVar).left |- ihAssumptionAtVar ==> accRight) by
            RightImplies.withParameters(ihAssumptionAtVar, accRight)(liftedInductiveCase)
          val typingLifted = have((ihLifted.statement -<? selfTypingAtVar).left |- selfTypingAtVar ==> (ihAssumptionAtVar ==> accRight)) by
            RightImplies.withParameters(selfTypingAtVar, ihAssumptionAtVar ==> accRight)(ihLifted)
          liftedInductiveCase = have(typingLifted.statement.left |- forall(v, selfTypingAtVar ==> (ihAssumptionAtVar ==> accRight))) by
            RightForall(typingLifted)

        case TypeArg(typeName) =>
          val t = typeExprToTerm(typeName)
          val typingAtVar = liftedInductiveCase.statement.left.find(typing =>
            typing == (v ∈ t) || typing == (v :: t)
          ).getOrElse(v ∈ t)
          val typingLifted = have((liftedInductiveCase.statement -<? typingAtVar).left |- typingAtVar ==> accRight) by
            RightImplies.withParameters(typingAtVar, accRight)(liftedInductiveCase)
          liftedInductiveCase = have(typingLifted.statement.left |- forall(v, typingAtVar ==> accRight)) by
            RightForall(typingLifted)
    )
    liftedInductiveCase
  }

  private def assemblePointwiseFromConstructorCases[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      adt: SemanticADT[N],
      assumptions: Set[Expr[Prop]],
      pointwiseGoal: Expr[Prop],
      prop: Expr[lisa.utils.fol.FOL.Arrow[Ind, Prop]],
      constructorCases: Seq[(SemanticConstructor[N], proof.Fact)],
      contextLabel: String
  ): proof.Fact = {
    val rawInductionGoal =
      adt.constructors.foldRight[Expr[Prop]](pointwiseGoal)((c, fc) =>
        c.inductiveCase.substitute(P := prop).asInstanceOf[Expr[Prop]] ==> fc
      )
    val inductionInstantiation = have(rawInductionGoal) by Restate.from(adt.induction of (P := prop))

    val constructorImplications: Seq[proof.Fact] = constructorCases.map { case (constructor, caseFact) =>
      val expectedCase = constructor.inductiveCase.substitute(P := prop).asInstanceOf[Expr[Prop]]
      val normalizedExpectedCase = normalForm(expectedCase)
      val normalizedCase = have(assumptions |- normalizedExpectedCase) by Tableau.from(caseFact)
      have(assumptions |- expectedCase) by Restate.from(normalizedCase)
    }

    val assembledInduction = constructorImplications.foldLeft[proof.Fact](inductionInstantiation)((acc, caseImplication) =>
      acc.statement.right.head match
        case _ ==> remainder =>
          have(assumptions |- remainder.asInstanceOf[Expr[Prop]]) by Tautology.from(acc, caseImplication)
        case other =>
          throw IllegalArgumentException(
            s"Unexpected induction shape while assembling $contextLabel: $other"
          )
    )

    have(assumptions |- pointwiseGoal) by Restate.from(assembledInduction)
  }

  /**
   * Pointwise induction plan used for extensional uniqueness.
   *
   * The caller must provide already-resolved recursive-definition formulas and
   * constructor schemas for both compared functions.
   */
  def pointwiseUniquenessAt[N <: Arity](
      adt: SemanticADT[N],
      inductionVariable: Variable[Ind],
      assumptions: Set[Expr[Prop]],
      propertyAt: Expr[Ind] => Expr[Prop],
      xFun: Expr[Ind],
      yFun: Expr[Ind],
      xDefinitionFormula: Expr[Prop],
      yDefinitionFormula: Expr[Prop],
      xConstructorSchemas: ConstructorSchemas[N],
      yConstructorSchemas: ConstructorSchemas[N]
  ): JUSTIFICATION = {
    requireSchemaCoverage(adt, xConstructorSchemas, "pointwiseUniquenessAt/x", "<anonymous>")
    requireSchemaCoverage(adt, yConstructorSchemas, "pointwiseUniquenessAt/y", "<anonymous>")

    val pointwiseGoal = ∀(inductionVariable, inductionVariable ∈ adt.term ==> propertyAt(inductionVariable))

    Lemma(assumptions |- pointwiseGoal) {
      val prop = λ(inductionVariable, propertyAt(inductionVariable))

      val constructorCases = adt.constructors.map(c =>
        val branchVars = c.variables1
        val branchTarget = propertyAt(c.appliedTerm(branchVars))
        val constructorCaseGoal = normalForm(c.inductiveCase.substitute(P := prop).asInstanceOf[Expr[Prop]])
        val localAssumptions = assumptions ++
          wellTypedSet(c.semanticSignature(branchVars)) ++
          c.syntacticSignature(branchVars).collect {
            case (v, SelfRef) => propertyAt(v)
          }.toSet

        c -> Lemma(assumptions |- constructorCaseGoal) {
          val argsTyped = have(localAssumptions |- wellTypedFormula(c.semanticSignature(branchVars))) by Tautology

          def instantiateCaseFromDefinition(
              definition: Expr[Prop],
              schema: (Seq[Variable[Ind]], Expr[Prop])
          ) = {
            val (caseVars, caseSchemaFormula) = schema
            val definitionFact = have(localAssumptions |- definition) by Tautology
            val schemaFromDefinition = have(definition |- caseSchemaFormula) by Tautology
            val caseSchema = have(localAssumptions |- caseSchemaFormula) by
              Cut.withParameters(definition)(definitionFact, schemaFromDefinition)
            instantiateSchemaAtBranch(
              localAssumptions = localAssumptions,
              branchVars = branchVars,
              argsTyped = argsTyped,
              schema = caseVars -> caseSchemaFormula,
              schemaFact = caseSchema,
              errorContext = s"pointwiseUniquenessAt/${c.name}"
            )
          }

          val xAtConstructor = instantiateCaseFromDefinition(
            definition = xDefinitionFormula,
            schema = xConstructorSchemas(c)
          )

          val yAtConstructor = instantiateCaseFromDefinition(
            definition = yDefinitionFormula,
            schema = yConstructorSchemas(c)
          )

          val xBody = extractBodyAtConstructor(
            equalityAtConstructor = xAtConstructor,
            functionHead = xFun,
            constructorTerm = c.appliedTerm(branchVars),
            constructorName = c.name,
            sideLabel = "x"
          )

          val yBody = extractBodyAtConstructor(
            equalityAtConstructor = yAtConstructor,
            functionHead = yFun,
            constructorTerm = c.appliedTerm(branchVars),
            constructorName = c.name,
            sideLabel = "y"
          )

          val recursiveEqualityFacts = c.syntacticSignature(branchVars).collect {
            case (v, SelfRef) =>
              have(localAssumptions |- propertyAt(v)) by Tautology
          }

          val bodyEquality = proveBodyEqualityFromRecursiveFacts(
            localAssumptions = localAssumptions,
            leftBody = xBody,
            rightBody = yBody,
            recursiveFacts = recursiveEqualityFacts,
            constructorName = c.name,
            contextLabel = "pointwiseUniquenessAt"
          )

          val yBodyToYConstructor = have(localAssumptions |- yBody === (yFun * c.appliedTerm(branchVars))) by Congruence.from(yAtConstructor)
          val xBodyToYConstructor = have(localAssumptions |- xBody === (yFun * c.appliedTerm(branchVars))) by Tautology.from(
            altEqualityTransitivity of (
              x := xBody,
              y := yBody,
              z := yFun * c.appliedTerm(branchVars)
            ),
            bodyEquality,
            yBodyToYConstructor
          )

          val branchEquality = have(localAssumptions |- branchTarget) by Tautology.from(
            altEqualityTransitivity of (
              x := xFun * c.appliedTerm(branchVars),
              y := xBody,
              z := yFun * c.appliedTerm(branchVars)
            ),
            xAtConstructor,
            xBodyToYConstructor
          )

          val liftedInductiveCase = liftBranchToInductiveCase(
            adt = adt,
            syntacticSignature = c.syntacticSignature(branchVars),
            propertyAt = propertyAt,
            branchEquality = branchEquality,
            selectSelfRefAssumption = (v, leftAssumptions) =>
              leftAssumptions.collectFirst {
                case assumption if asIndEquality(assumption).exists((lhs, rhs) =>
                    lhs == (xFun * v) && rhs == (yFun * v)
                  ) => assumption
              }.getOrElse(propertyAt(v))
          )

          have(thesis) by Tautology.from(liftedInductiveCase)
        }
      )

      val pointwiseFromInduction = assemblePointwiseFromConstructorCases(
        adt = adt,
        assumptions = assumptions,
        pointwiseGoal = pointwiseGoal,
        prop = prop,
        constructorCases = constructorCases,
        contextLabel = "pointwise uniqueness proof"
      )
      have(thesis) by Restate.from(pointwiseFromInduction)
    }
  }

}

// ─────────────────────────────────────────────────────────────────────────────
// ExtensionalUniqueness
// ─────────────────────────────────────────────────────────────────────────────

private[recursion] final class ExtensionalUniqueness[N <: Arity](
    adt: SemanticADT[N],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    returnType: Expr[Ind],
    typ: Expr[Ind],
    untypedDefinition: Expr[Prop]
) {


  private def stripForalls(formula: Expr[Prop]): (Seq[Variable[Ind]], Expr[Prop]) = formula match
    case forall(v, phi) =>
      val (restVars, core) = stripForalls(phi)
      (v +: restVars, core)
    case other => (Seq.empty, other)


  private def extractConstructorCaseSchema(
      definition: Expr[Prop],
      functionHead: Expr[Ind],
      constructor: SemanticConstructor[N]
  ): (Seq[Variable[Ind]], Expr[Prop]) = {
    val maybeSchema = splitConjunctions(definition).iterator.flatMap(candidate =>
      val (vars, core) = stripForalls(candidate)
      val maybeEquality = core match
        case _ ==> equalityFormula => asIndEquality(equalityFormula)
        case equalityFormula => asIndEquality(equalityFormula)

      maybeEquality.flatMap((lhs, _) =>
        lhs match
          case Sapp(fun: Expr[Ind], arg: Expr[Ind])
              if fun == functionHead && arg == constructor.appliedTerm(vars) =>
            Some(vars -> candidate)
          case _ => None
      )
    ).toSeq.headOption

    maybeSchema.getOrElse(
      throw IllegalArgumentException(
        s"Unable to extract constructor case schema for constructor ${constructor.name} and function ${functionHead}."
      )
    )
  }

  private def extractConstructorSchemas(
      definition: Expr[Prop],
      functionHead: Expr[Ind]
  ): ConstructorSchemas[N] =
    adt.constructors.map(c => c -> extractConstructorCaseSchema(definition, functionHead, c)).toMap

  private def definitionFormula(v: Variable[Ind]): Expr[Prop] =
    untypedDefinition.substitute(f := v)

  val recursivePointwisePlan: THM =
    Lemma(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)){
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
      val xDefFormula = definitionFormula(x)
      val yDefFormula = definitionFormula(y)
      val xConstructorSchemas = extractConstructorSchemas(xDefFormula, x)
      val yConstructorSchemas = extractConstructorSchemas(yDefFormula, y)

      val pointwiseCoreLemma = RecFunctionInduction.pointwiseUniquenessAt(
        adt = adt,
        inductionVariable = pointInput,
        assumptions = Set(definitionFormula(x), definitionFormula(y)),
        propertyAt = t => x * t === y * t,
        xFun = x,
        yFun = y,
        xDefinitionFormula = xDefFormula,
        yDefinitionFormula = yDefFormula,
        xConstructorSchemas = xConstructorSchemas,
        yConstructorSchemas = yConstructorSchemas
      )

      val pointwiseByHeight = have(
        ∀(pointInput, pointInput ∈ adt.term ==> (x * pointInput === y * pointInput))
      ) by Tautology.from(pointwiseCoreLemma, xDefinition, yDefinition)

      have(x === y) by Tautology.from(
        BasicTheorems.extensionality of (
          f := x,
          g := y,
          A := adt.term,
          x := pointInput
        ),
        xOnDomain,
        yOnDomain,
        pointwiseByHeight
      )
      thenHave(thesis) by Tautology
    }
}
