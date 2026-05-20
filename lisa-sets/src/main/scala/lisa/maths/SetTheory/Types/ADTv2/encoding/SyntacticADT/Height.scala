package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.height.HeightADT
import lisa.maths.SetTheory.Types.ADTv2.height.HeightConstructors
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTHeight[N <: Arity]
    extends SyntacticADTInjectivity[N] {
  this: SyntacticADT[N] =>

  val heightTHY = HeightADT[N](
    name,
    typeVariablesSeq,
    isConstructor
  )

  val heightConstructorsTHY = HeightConstructors[N](
    heightTHY,
    constructors,
    isConstructor
  )

  val isHeight = heightTHY.isHeight
  val heightExists = heightTHY.heightExists
  val heightZero = heightTHY.heightZero
  val heightFunUniqueEq = heightTHY.heightFunUniqueEq
  val heightMonotonic = heightConstructorsTHY.heightMonotonic
  val heightSuccessorWeak = heightConstructorsTHY.heightSuccessorWeak
  val heightSuccessorStrong = heightConstructorsTHY.heightSuccessorStrong

  def unfoldIsHeight(using
      lib: lisa.utils.prooflib.Library,
      proof: lib.Proof
  ): proof.Fact = heightTHY.unfoldIsHeight
}
