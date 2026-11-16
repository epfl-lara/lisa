package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.{FunctionSemanticsBase, SemanticFunctionInputs}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution

final class SemanticFunction(
    semanticName: String,
    parameters: Seq[Variable[Ind]],
    semanticAdt: SemanticADT,
    semanticArgType: Expr[Ind],
    typeSubstitutions: Seq[TypeSubstitution],
    selfPlaceholder: Variable[Ind],
    patternMatching: PatternSystem,
    semanticReturnType: Expr[Ind]
) extends FunctionSemanticsBase(
      new SemanticFunctionInputs {

        val spec: FunSpec = new FunSpec(
          functionName = semanticName,
          typeVariablesSeq = parameters,
          adt = semanticAdt,
          argType = semanticArgType,
          typeSubstitutions = typeSubstitutions,
          selfPlaceholder = selfPlaceholder,
          patternMatching = patternMatching,
          returnType = semanticReturnType
        )

        private val rawPatterns: Seq[Pattern] = spec.cases

        private val witness: Witness = (new Witness(spec))
        private val approxSeq = (new ApproxSequence(spec, witness))
        private val witnessAgreement = (new helpers.WitnessAgreement(spec, witness))
        private val approxStab = (new ApproxStabilization(spec, witness, approxSeq, witnessAgreement))
        private val limitConstruction = (new LimitConstruction(spec, approxSeq, approxStab))

        def name: String = semanticName
        val existence: Existence = (new Existence(spec, witness, approxSeq, approxStab, limitConstruction, witnessAgreement))
        val uniqueness: Uniqueness = (new Uniqueness(spec))
        def buildPatterns(term: Expr[Ind]): Seq[Pattern] =
          rawPatterns.map(pattern => pattern.withBody(pattern.body.substitute(spec.selfPlaceholder := term)))
      }
    )
