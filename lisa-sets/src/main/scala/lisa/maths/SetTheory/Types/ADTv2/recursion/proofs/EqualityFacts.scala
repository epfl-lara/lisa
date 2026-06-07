package lisa.maths.SetTheory.Types.ADTv2.recursion.proofs

import lisa.maths.SetTheory.SetTheory.{*, given}

private[recursion] object EqualityFacts {

  private val leftEq  = variable[Ind]
  private val rightEq = variable[Ind]

  private val symmetry = Lemma((leftEq === rightEq) |- (rightEq === leftEq)) {
    have(thesis) by Congruence
  }

  def symmetryAt(
      left: Expr[Ind],
      right: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    have((left === right) |- (right === left)) by Restate.from(
      symmetry of (leftEq := left, rightEq := right)
    )

  def initialize(): Unit = {
    val _ = symmetry
  }
}
