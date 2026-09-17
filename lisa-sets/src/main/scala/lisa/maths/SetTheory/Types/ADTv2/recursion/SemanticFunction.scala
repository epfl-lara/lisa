package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.{FunctionSemanticsBase, SemanticFunctionInputs}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.utils.prooflib.ProofTacticLib.Arity

final class SemanticFunction[N <: Arity](
    semanticName: String,
    semanticAdt: SemanticADT[N],
    semanticArgType: Expr[Ind],
    typeSubstitutions: Seq[TypeSubstitution],
    selfPlaceholder: Variable[Ind],
    patternMatching: PatternSystem[N],
    semanticReturnType: Expr[Ind]
) extends FunctionSemanticsBase[N](
      new SemanticFunctionInputs[N] {

        val spec: FunSpec[N] = new FunSpec[N](
          functionName = semanticName,
          adt = semanticAdt,
          argType = semanticArgType,
          typeSubstitutions = typeSubstitutions,
          selfPlaceholder = selfPlaceholder,
          patternMatching = patternMatching,
          returnType = semanticReturnType
        )

        private val rawPatterns: Seq[Pattern[N]] = spec.cases

        private val witness: Witness[N] = (new Witness[N](spec))
        private val approxSeq = (new ApproxSequence[N](spec, witness))
        private val witnessAgreement = (new helpers.WitnessAgreement[N](spec, witness))
        private val approxStab = (new ApproxStabilization[N](spec, witness, approxSeq, witnessAgreement))
        private val limitConstruction = (new LimitConstruction[N](spec, approxSeq, approxStab))

        def name: String = semanticName
        val existence: Existence[N] = (new Existence[N](spec, witness, approxSeq, approxStab, limitConstruction, witnessAgreement))
        val uniqueness: Uniqueness[N] = (new Uniqueness[N](spec))
        def buildPatterns(term: Expr[Ind]): Seq[Pattern[N]] =
          rawPatterns.map(pattern => pattern.withBody(pattern.body.substitute(spec.selfPlaceholder := term)))
      }
    )
