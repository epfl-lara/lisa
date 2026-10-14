package lisa.maths.SetTheory.Types.ADTv2.support.tactics

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.ProofTacticLib.UnapplicableProofTactic
import scala.util.boundary

/**
 *  Tactic chaining several [[Cut]]s in a single step.
 *
 *  Given a `main` fact and a list of `sideFacts`, it folds [[Cut]] over the side
 *  facts, discharging from `main` (one after the other) every formula that a side
 *  fact proves. It is the explicit, cut-only counterpart of combining the same
 *  facts with `Tautology.from`, useful when each hypothesis of `main` is proved
 *  outright (a side fact of the shape `... |- hyp`) so that no propositional
 *  reasoning beyond cutting is needed.
 *
 *  A side fact whose conclusion no longer matches any open assumption of the
 *  accumulator is simply skipped: this happens when two side facts share a
 *  conclusion (a previous cut already discharged it) or when distinct
 *  hypotheses of `main` collapse to the same formula after instantiation. The
 *  final [[Restate]] against `bot` still checks that everything needed was
 *  actually discharged, so skipping cannot mask a genuine gap.
 *
 *  ===Usage===
 *  {{{
 *  have(thesis) by Cuts(mainFact)(
 *    sideFact1,
 *    sideFact2,
 *    ...
 *  )
 *  }}}
 *
 *  is equivalent to the chain
 *
 *  {{{
 *  val s1 = have(...) by Cut(sideFact1, mainFact)
 *  val s2 = have(...) by Cut(sideFact2, s1)
 *  ...
 *  }}}
 */
object Cuts extends lisa.utils.prooflib.ProofTacticLib.ProofTactic {

  override val name: String = "Cuts"

  def apply(using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      main: proof.Fact
  )(
      sideFacts: proof.Fact*
  )(bot: Sequent): proof.ProofTacticJudgement =
    boundary[proof.ProofTacticJudgement]:
      TacticSubproof { ip ?=>
        val combined = sideFacts.foldLeft[ip.Fact](main) { (acc, fact) =>
          // Cut on the formula `fact` proves and `acc` still assumes. Formulas are
          // compared up to OL-normalization (`isSame`), not syntactically.
          fact.statement.right.find(r => acc.statement.left.exists(l => isSame(l, r))) match
            case None =>
              // Conclusion already discharged (e.g. duplicate side facts, or `main`
              // hypotheses that coincided after instantiation): nothing left to cut.
              acc
            case Some(phi) =>
              val resLeft = fact.statement.left ++ acc.statement.left.filterNot(l => isSame(l, phi))
              val resRight = fact.statement.right.filterNot(r => isSame(r, phi)) ++ acc.statement.right
              have(resLeft |- resRight) by Cut.withParameters(phi)(fact, acc)
        }
        // The closing `Restate` carries this file's location, so a failure here
        // points at `Cuts.scala` rather than the call site. Re-raise with the
        // caller's `line`/`file` and the leftover sequent, which is what actually
        // helps diagnose an undischarged hypothesis or an unmatched side fact.
        try have(bot) by Restate.from(combined)
        catch
          case _: UnapplicableProofTactic =>
            throw UnapplicableProofTactic(
              Cuts,
              proof,
              s"""after cutting every side fact, the accumulated sequent was
                 |    ${combined.statement}
                 |which Restate could not reconcile with the goal
                 |    $bot
                 |Each hypothesis of `main` must be discharged by a side fact whose
                 |conclusion matches it (up to OL-normalization), and whatever remains
                 |must be OL-equivalent to the goal. A leftover hypothesis, or a side
                 |fact whose conclusion does not match any hypothesis, is the usual
                 |cause.""".stripMargin
            )(using line, file)
      }

}
