package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.{FunSpecBase, FunctionSemanticsBase, SemanticFunctionInputs}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.Time
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

      private val witness: Witness[N] = Time.measure(s"Witness", false)(new Witness[N](spec))
      private val approx = Time.measure(s"Approx", false)(new Approx[N](spec, witness))
      private val witnessAgreement = Time.measure(s"WitnessAgreement", false)(new helpers.WitnessAgreement[N](spec, witness))
      private val approxProp = Time.measure(s"ApproxProp", false)(new ApproxProp[N](spec, witness, approx, witnessAgreement))
      private val limitConstruction = Time.measure(s"LimitConstruction", false)(new LimitConstruction[N](spec, approx, approxProp))

      def name: String = semanticName
      val existence: Existence[N] = Time.measure(s"Existence", false)(new Existence[N](spec, witness, approx, approxProp, limitConstruction, witnessAgreement))
      val uniqueness: Uniqueness[N] = Time.measure(s"Uniqueness", false)(new Uniqueness[N](spec))
      def buildPatterns(term: Expr[Ind]): Seq[Pattern[N]] =
        rawPatterns.map(pattern =>
          pattern.withBody(pattern.body.substitute(spec.selfPlaceholder := term))
        )
    }
)
