package lisa.maths.SetTheory.Types.ADTv2.support.core

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.BasicStepTactic.Restate

object InstantiateForallSeq extends lisa.utils.prooflib.ProofTacticLib.ProofTactic {

  /**
   * Repeatedly instantiates the right-hand side of a fact through a sequence of
   * universal quantifiers.
   *
   * Typical use:
   *   from `forallSeq(vars, phi(vars))`
   *   derive `phi(args)`.
   */
  def apply(using
      lib: lisa.utils.prooflib.Library,
      proof: lib.Proof
  )(
      args: Seq[Expr[Ind]]
  )(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof { sp ?=>
    var current = lib.have(fact.statement) by Restate.from(fact)

    for arg <- args do
      current.statement.right.head match
        case forall(v, phi) =>
          current = lib.have(phi.substitute(v := arg).asInstanceOf[Expr[Prop]]) by InstantiateForall(arg)(current)
        case _ =>
          proof.InvalidProofTactic(
            s"InstantiateForallSeq expected a universally quantified formula, got: ${current.statement.right.head}"
          )

    lib.have(bot) by Tautology.from(current)
  }
}
