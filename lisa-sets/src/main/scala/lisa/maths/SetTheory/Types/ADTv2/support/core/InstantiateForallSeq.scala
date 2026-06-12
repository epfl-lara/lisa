package lisa.maths.SetTheory.Types.ADTv2.support.core

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.BasicStepTactic.Restate
import scala.util.boundary
import scala.util.boundary.break

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
  )(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = boundary:
    TacticSubproof { sp ?=>
      val initialCurrent = TacticErrors.attemptOrInvalid(using lib)(proof)(
        tacticName = "InstantiateForallSeq",
        summary = "failed before any instantiation while importing the original fact",
        factStatement = fact.statement,
        bot = bot,
        "Arguments requested" -> args.mkString(", ")
      ) {
        lib.have(fact.statement) by Restate.from(fact)
      } match
        case Left(judgement) => break(judgement)
        case Right(value)    => value

      var current = initialCurrent

      for (arg, index) <- args.zipWithIndex do
        current.statement.right.head match
          case forall(v, phi) =>
            current = TacticErrors.attemptOrInvalid(using lib)(proof)(
              tacticName = "InstantiateForallSeq",
              summary = s"failed while instantiating argument #${index + 1} with `$arg`",
              factStatement = fact.statement,
              bot = bot,
              "Arguments requested" -> args.mkString(", "),
              "Current intermediate statement" -> current.statement.toString,
              "Current quantified variable" -> v.toString
            ) {
              lib.have(phi.substitute(v := arg).asInstanceOf[Expr[Prop]]) by InstantiateForall(arg)(current)
            } match
              case Left(judgement) => break(judgement)
              case Right(value)    => value
          case _ =>
            break(TacticErrors.invalid(using lib)(proof)(
              tacticName = "InstantiateForallSeq",
              summary = s"expected a universally quantified formula while instantiating argument #${index + 1}",
              factStatement = fact.statement,
              bot = bot,
              "Argument" -> arg.toString,
              "Arguments requested" -> args.mkString(", "),
              "Current intermediate statement" -> current.statement.toString,
              "Current right-hand formula" -> current.statement.right.head.toString
            ))

      TacticErrors.attemptOrInvalid(using lib)(proof)(
        tacticName = "InstantiateForallSeq",
        summary = "failed while closing the instantiated theorem",
        factStatement = fact.statement,
        bot = bot,
        "Arguments requested" -> args.mkString(", "),
        "Current intermediate statement" -> current.statement.toString
      ) {
        lib.have(bot) by Tautology.from(current)
      } match
        case Left(judgement) => break(judgement)
        case Right(value)    => value
  }
}
