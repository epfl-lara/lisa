package lisa.proven.mathematics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.proven.tactics.ProofTactics.*
import lisa.proven.PeanoArithmeticsLibrary
import lisa.utils.Helpers.{_, given}
import lisa.utils.Library

object Peano {
  export lisa.proven.PeanoArithmeticsLibrary.{*, given}

  /////////////////////////// OUTPUT CONTROL //////////////////////////
  given output: (String => Unit) = println
  given finishOutput: (Throwable => Nothing) = e => throw e

  def main(args: Array[String]): Unit = {}
  /////////////////////////////////////////////////////////////////////

  THEOREM("x + 0 = 0 + x") of "∀x. plus(x, zero) === plus(zero, x)" PROOF {
    val refl0: SCProofStep = RightRefl(() |- s(x) === s(x), s(x) === s(x))
    val subst1 = RightSubstEq((x === plus(zero, x)) |- s(x) === s(plus(zero, x)), 0, (x, plus(zero, x)) :: Nil, LambdaTermFormula(Seq(y), s(x) === s(y)))
    val implies2 = RightImplies(() |- (x === plus(zero, x)) ==> (s(x) === s(plus(zero, x))), 1, x === plus(zero, x), s(x) === s(plus(zero, x)))
    val transform3 = RightSubstEq(
      (plus(zero, s(x)) === s(plus(zero, x))) |- (x === plus(zero, x)) ==> (s(x) === plus(zero, s(x))),
      2,
      (plus(zero, s(x)), s(plus(zero, x))) :: Nil,
      LambdaTermFormula(Seq(y), (x === plus(zero, x)) ==> (s(x) === y))
    )

    // result: ax4plusSuccessor |- 0+Sx = S(0 + x)
    val instanceAx4_4 = SCSubproof(
      instantiateForall(SCProof(IndexedSeq[SCProofStep](Hypothesis(ax4plusSuccessor |- ax4plusSuccessor, ax4plusSuccessor)), IndexedSeq(() |- ax4plusSuccessor)), zero, x),
      Seq(-1)
    )
    val cut5 = Cut(ax4plusSuccessor |- (x === plus(zero, x)) ==> (s(x) === plus(zero, s(x))), 4, 3, plus(zero, s(x)) === s(plus(zero, x)))

    val transform6 = RightSubstEq(
      Set(ax4plusSuccessor, plus(x, zero) === x, plus(s(x), zero) === s(x)) |- (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      5,
      (plus(x, zero), x) :: (plus(s(x), zero), s(x)) :: Nil,
      LambdaTermFormula(Seq(y, z), (y === plus(zero, x)) ==> (z === plus(zero, s(x))))
    )
    val leftAnd7 = LeftAnd(
      Set(ax4plusSuccessor, (plus(x, zero) === x) /\ (plus(s(x), zero) === s(x))) |- (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      6,
      plus(x, zero) === x,
      plus(s(x), zero) === s(x)
    )

    val instancePlusZero8 = SCSubproof(
      instantiateForall(SCProof(IndexedSeq[SCProofStep](Hypothesis(ax3neutral |- ax3neutral, ax3neutral)), IndexedSeq(() |- ax3neutral)), x),
      Seq(-2)
    )
    val instancePlusZero9 = SCSubproof(
      instantiateForall(SCProof(IndexedSeq[SCProofStep](Hypothesis(ax3neutral |- ax3neutral, ax3neutral)), IndexedSeq(() |- ax3neutral)), s(x)),
      Seq(-2)
    )
    val rightAnd10 = RightAnd(ax3neutral |- (plus(x, zero) === x) /\ (plus(s(x), zero) === s(x)), Seq(8, 9), Seq(plus(x, zero) === x, plus(s(x), zero) === s(x)))

    val cut11 = Cut(
      Set(ax4plusSuccessor, ax3neutral) |- (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      10,
      7,
      (plus(x, zero) === x) /\ (plus(s(x), zero) === s(x))
    )

    val forall12 = RightForall(
      cut11.bot.left |- forall(x, (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x)))),
      11,
      (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      x
    )

    val hypConclusion13 = hypothesis(forall(x, plus(x, zero) === plus(zero, x)))
    val inductionLhs14 = LeftImplies(
      Set(ax4plusSuccessor, ax3neutral, forall(x, (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x)))) ==> forall(x, plus(x, zero) === plus(zero, x))) |- forall(
        x,
        plus(x, zero) === plus(zero, x)
      ),
      12,
      13,
      forall(x, (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x)))),
      forall(x, plus(x, zero) === plus(zero, x))
    )
    val inductionInstance15: SCProofStep = InstPredSchema(
      () |- ((plus(zero, zero) === plus(zero, zero)) /\ forall(x, (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))))) ==> forall(
        x,
        plus(x, zero) === plus(zero, x)
      ),
      -3,
      Map(sPhi -> LambdaTermFormula(Seq(x), plus(x, zero) === plus(zero, x)))
    )
    val commutesWithZero16 = Cut(
      Set(ax4plusSuccessor, ax3neutral) |- forall(x, plus(x, zero) === plus(zero, x)),
      15,
      14,
      ((plus(zero, zero) === plus(zero, zero)) /\ forall(x, (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))))) ==> forall(
        x,
        plus(x, zero) === plus(zero, x)
      )
    )

    SCProof(
      IndexedSeq(
        refl0,
        subst1,
        implies2,
        transform3,
        instanceAx4_4,
        cut5,
        transform6,
        leftAnd7,
        instancePlusZero8,
        instancePlusZero9,
        rightAnd10,
        cut11,
        forall12,
        hypConclusion13,
        inductionLhs14,
        inductionInstance15,
        commutesWithZero16
      ),
      IndexedSeq(ax"ax4plusSuccessor", ax"ax3neutral", ax"ax7induction")
    )
  } using (ax"ax4plusSuccessor", ax"ax3neutral", ax"ax7induction")
  show
}
