package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.{FunctionSemanticsBase, SemanticFunctionInputs}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._

final class SemanticFunction(
    semanticName: String,
    semanticAdt: SemanticADT,
    semanticArgType: Expr[Ind],
    patternMatching: PatternSystem,
    semanticReturnType: Expr[Ind]
) extends FunctionSemanticsBase(
      new SemanticFunctionInputs {

        val spec: FunSpec = new FunSpec(
          functionName = semanticName,
          adt = semanticAdt,
          argType = semanticArgType,
          patternMatching = patternMatching,
          returnType = semanticReturnType
        )

        private val witness: Witness = (new Witness(spec))

        def name: String = semanticName
        val existence: Existence = (new Existence(spec, witness))
        val uniqueness: Uniqueness = new Uniqueness(spec)
        def buildPatterns(term: Expr[Ind]): Seq[Pattern] = spec.cases
      }
    )
