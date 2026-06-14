package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.{FunctionSemanticsBase, SemanticFunctionInputs}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.utils.prooflib.ProofTacticLib.Arity

final class SemanticFunction[N <: Arity](
    semanticName: String,
    semanticAdt: SemanticADT[N],
    semanticArgType: Expr[Ind],
    patternMatching: PatternSystem[N],
    semanticReturnType: Expr[Ind]
) extends FunctionSemanticsBase[N](
    new SemanticFunctionInputs[N] {
      
      val spec: FunSpec[N] = new FunSpec[N](
        functionName = semanticName,
        adt = semanticAdt,
        argType = semanticArgType,
        patternMatching = patternMatching,
        returnType = semanticReturnType
      )

      private val witness: Witness[N] = Time.measure(s"Witness", false)(new Witness[N](spec))

      def name: String = semanticName
      val existence: Existence[N] = Time.measure(s"Existence", false)(new Existence[N](spec, witness))
      val uniqueness: Uniqueness[N] = new Uniqueness[N](spec)
      def buildPatterns(term: Expr[Ind]): Seq[Pattern[N]] = spec.cases
    }
)
