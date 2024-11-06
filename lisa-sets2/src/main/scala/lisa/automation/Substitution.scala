package lisa.automation

import lisa.utils.fol.FOL as F
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus
import lisa.utils.prooflib.BasicStepTactic
import lisa.utils.prooflib.SimpleDeducedSteps
import lisa.utils.prooflib.ProofTacticLib.{*, given}
import lisa.utils.prooflib.*
import lisa.utils.K
import lisa.utils.UserLisaException
import lisa.utils.unification.UnificationUtils.*
import lisa.utils.collection.Extensions.*

import scala.annotation.nowarn
import scala.collection.mutable.{Map as MMap}

import F.{*, given}
import lisa.utils.collection.VecSet

object Substitution:

  /**
   * Extracts a raw substitution into a `RewriteRule`.
   */
  def extractRule(using lib: Library, proof: lib.Proof)(rule: proof.Fact | Expr[Formula]): RewriteRule =
    rule match
      case f: Expr[Formula] @unchecked =>
        (f: @unchecked) match
          case === #@ (l: Expr[Term]) #@ (r: Expr[Term]) => TermRewriteRule(l, r)
          case <=> #@ (l: Expr[Formula]) #@ (r: Expr[Formula]) => FormulaRewriteRule(l, r)
      case f: proof.Fact @unchecked => extractRule(proof.getSequent(f).right.head)

  /**
   * Partitions raw substitution rules into free and confined rules, also
   * creating a source map, mapping each rule to the `Fact` it was derived from,
   * for proof construction.
   */
  def partition(using lib: Library, proof: lib.Proof)(substitutions: Seq[proof.Fact | Expr[Formula]]): (Map[RewriteRule, proof.Fact], RewriteContext) =
    substitutions.foldLeft((Map.empty, RewriteContext.empty)):
      case ((source, ctx), rule) =>
        val erule = extractRule(rule)
        rule match
          case f: Expr[Formula] @unchecked =>
            (source + (erule -> erule.source) + (erule.swap -> erule.source), ctx.withConfinedRule(erule).withConfinedRule(erule.swap))
          case j: lib.JUSTIFICATION =>
            (source + (erule -> j) + (erule.swap -> j), ctx.withFreeRule(erule).withFreeRule(erule.swap))
          case f: proof.Fact @unchecked =>
            (source + (erule -> f) + (erule.swap -> f), ctx.withConfinedRule(erule).withConfinedRule(erule.swap))

  /**
   * Checks if a raw substitution input can be used as a rewrite rule (is === or
   * <=>, basically).
   */
  def validSubstitutionRule(using lib: lisa.utils.prooflib.Library, proof: lib.Proof)(rule: (proof.Fact | Expr[Formula])): Boolean =
    rule match
      // as formula
      case f: Expr[Formula] @unchecked =>
        f match
          case === #@ l #@ r => true
          case <=> #@ l #@ r => true
          case _ => false
      // as a justification
      case just: proof.Fact @unchecked =>
        val sequent = proof.getSequent(just)
        sequent.right.size == 1 && validSubstitutionRule(sequent.right.head)

  object Apply extends ProofTactic:
    def apply(using lib: Library, proof: lib.Proof)(substitutions: (proof.Fact | Expr[Formula])*)(premiseStep: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =

      // are all substitution rules actually valid?
      // if not, exit early

      val violatingFacts = substitutions.collect:
        case f: proof.Fact @unchecked if !validSubstitutionRule(f) => proof.getSequent(f)

      val violatingFormulas = substitutions.collect:
        case f: Expr[Formula] @unchecked if !validSubstitutionRule(f) => f

      if violatingFacts.nonEmpty then
        val msgBase = "Substitution rules must have a single equality or equivalence on the right-hand side. Violating sequents passed:\n"
        val msgList = violatingFacts.zipWithIndex.map:
          case (f, i) => s"\t${i + 1}. $f"

        proof.InvalidProofTactic(msgBase + msgList.mkString("\n"))
      else if violatingFormulas.nonEmpty then
        val msgBase = "Substitution rules must be equalities or equivalences. Violating formulas passed:\n"
        val msgList = violatingFacts.zipWithIndex.map:
          case (f, i) => s"\t${i + 1}. $f"

        proof.InvalidProofTactic(msgBase + msgList.mkString("\n"))
      else
        // continue, we have a list of rules to work with

        // rewrite base
        val premise = proof.getSequent(premiseStep)
        // the target is bot

        // metadata:
        // maintain a list of where substitutions come from
        // and categorize them for the rewrite context
        val (sourceMap, prectx) = partition(substitutions)
        val ctx = prectx.withBound(premise.left.flatMap(_.freeVars))

        // TODO: CHECK is this really necessary?
        // remove from the premise equalities we are rewriting with, as these
        // terms themselves are not targets for the rewriting
        // val filteredPrem = ???

        // check whether this rewrite is even possible.
        // if it is, get the context (term with holes) corresponding to the
        // single-step simultaneous rewrite

        // for each formula in the premise left (resp. right), there must be a
        // corresponding formula in the conclusion left (resp. right) that it
        // can be rewritten into.

        // discover a (possibly non-injective non-surjective) mapping from one
        // formula set to another where a formula maps to another by the
        // rewrites above
        inline def collectRewritingPairs(base: Set[Expr[Formula]], target: Set[Expr[Formula]]): Option[Seq[FormulaRewriteResult]] =
          base.iterator
            .map: formula =>
              target.collectFirstDefined: target =>
                rewrite(using ctx)(formula, target)
            .toOptionSeq

        // collect the set of formulas in `base` that rewrite to *no* formula
        // in `target`. Guaranteed to be non-empty if
        // `collectRewritingPairs(base, target)` is None.
        inline def collectViolatingPairs(base: Set[Expr[Formula]], target: Set[Expr[Formula]]): Set[Expr[Formula]] =
          premise.left.filter: formula =>
            bot.left.forall: target =>
              rewrite(using ctx)(formula, target).isEmpty

        val leftSubsts = collectRewritingPairs(premise.left, bot.left)
        val rightSubsts = collectRewritingPairs(premise.right, bot.right)

        if leftSubsts.isEmpty then
          // error, find formulas that failed to rewrite
          val msgBase = "Could not rewrite LHS of premise into conclusion with given substitutions.\nViolating Formulas:"
          val msgList =
            collectViolatingPairs(premise.left, bot.left).zipWithIndex
              .map:
                case (formula, i) => s"\t${i + 1}. $formula"

          proof.InvalidProofTactic(msgBase + msgList.mkString("\n"))
        else if rightSubsts.isEmpty then
          // error, find formulas that failed to rewrite
          val msgBase = "Could not rewrite LHS of premise into conclusion with given substitutions.\nViolating Formulas:"
          val msgList =
            collectViolatingPairs(premise.right, bot.right).zipWithIndex
              .map:
                case (formula, i) => s"\t${i + 1}. $formula"

          proof.InvalidProofTactic(msgBase + msgList.mkString("\n"))
        else
          // rewriting is possible, construct the proof

          import lib.{have, thenHave, lastStep}
          import BasicStepTactic.{TacticSubproof, Weakening, Cut, LeftSubstEq, RightSubstEq}
          import SimpleDeducedSteps.Restate

          TacticSubproof:
            val leftRewrites = leftSubsts.get
            val rightRewrites = rightSubsts.get
            val leftRules = leftRewrites.to(VecSet).flatMap(_.rules)
            val rightRules = rightRewrites.to(VecSet).flatMap(_.rules)

            // instantiated discharges

            val leftDischarges = leftRules.map(r => r -> proof.InstantiatedFact(sourceMap(r.rule), r.subst.asSubstPair))
            val rightDischarges = rightRules.map(r => r -> proof.InstantiatedFact(sourceMap(r.rule), r.subst.asSubstPair))

            val discharges = leftDischarges ++ rightDischarges

            // start proof
            have(andAll(premise.left) |- premise.right) by Restate.from(premiseStep)

            // left rewrites
            val leftFormulas = leftRules.map(_.toFormula)
            val preLeft = leftRewrites.map(_.toLeft)
            val postLeft = leftRewrites.map(_.toRight)
            val leftVars = leftRewrites.head.vars
            val leftLambda = andAll(leftRewrites.map(_.lambda))
            thenHave(andAll(preLeft) |- premise.right) by Restate
            thenHave(leftFormulas + andAll(preLeft) |- premise.right) by Weakening
            thenHave(leftFormulas + andAll(postLeft) |- premise.right) by LeftSubstEq.withParameters(leftRules.map(r => r.l -> r.r).toSeq, leftVars -> leftLambda)

            val rpremise = lastStep.bot

            // right rewrites
            val rightFormulas = rightRules.map(_.toFormula)
            val preRight = rightRewrites.map(_.toLeft).toSet
            val postRight = rightRewrites.map(_.toRight).toSet
            val rightVars = rightRewrites.head.vars
            val rightLambda = orAll(rightRewrites.map(_.lambda))
            thenHave(rpremise.left |- orAll(preRight)) by Restate
            thenHave(rightFormulas ++ rpremise.left |- orAll(preRight)) by Weakening
            thenHave(rightFormulas ++ rpremise.left |- orAll(postRight)) by RightSubstEq.withParameters(rightRules.map(r => r.l -> r.r).toSeq, rightVars -> rightLambda)

            // rewrite to destruct sequent
            thenHave(postLeft ++ leftFormulas ++ rightFormulas |- postRight) by Restate

            val dpremise = lastStep.bot

            // discharge assumptions
            discharges.foldLeft(dpremise):
              case (premise, (rule, source)) =>
                val sseq = proof.getSequent(source)
                val form = rule.toFormula
                val nextSequent = premise.left - form ++ sseq.left |- premise.right ++ sseq.right - form
                have(nextSequent) by Cut.withParameters(form)(source, lastStep)
                nextSequent

            // restate to the result
            thenHave(bot) by Weakening

  end Apply

  object Unfold extends ProofTactic:
    def apply(using lib: Library, proof: lib.Proof)(definition: lib.theory.Definition)(premise: proof.Fact): proof.ProofTacticJudgement =
      ???

  end Unfold

end Substitution
