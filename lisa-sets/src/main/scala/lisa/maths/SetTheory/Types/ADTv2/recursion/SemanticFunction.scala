package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.{FunctionSemanticsBase, SemanticFunctionInputs}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.utils.debug.Time
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

        private val witness: Witness[N] = Time.measure(s"Witness")(new Witness[N](spec))
        private val approxSeq = Time.measure(s"ApproxSequence")(new ApproxSequence[N](spec, witness))
        private val witnessAgreement = Time.measure(s"WitnessAgreement")(new helpers.WitnessAgreement[N](spec, witness))
        private val approxStab = Time.measure(s"ApproxStabilization")(new ApproxStabilization[N](spec, witness, approxSeq, witnessAgreement))
        private val limitConstruction = Time.measure(s"LimitConstruction")(new LimitConstruction[N](spec, approxSeq, approxStab))

        def name: String = semanticName
        val existence: Existence[N] = Time.measure(s"Existence")(new Existence[N](spec, witness, approxSeq, approxStab, limitConstruction, witnessAgreement))
        val uniqueness: Uniqueness[N] = Time.measure(s"Uniqueness")(new Uniqueness[N](spec))
        def buildPatterns(term: Expr[Ind]): Seq[Pattern[N]] =
          rawPatterns.map(pattern => pattern.withBody(pattern.body.substitute(spec.selfPlaceholder := term)))
      }
    )
