package lisa.automation

import lisa.fol.FOL as F
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus
import lisa.prooflib.BasicStepTactic
import lisa.prooflib.SimpleDeducedSteps
import lisa.prooflib.ProofTacticLib.{*, given}
import lisa.prooflib.*
import lisa.utils.K
import lisa.utils.UserLisaException
import lisa.utils.unification.UnificationUtils.*
import lisa.utils.collection.Extensions.*

import scala.annotation.nowarn
import scala.collection.mutable.{Map as MMap}

import F.{*, given}

object Substitution:
  /*

  /**
   * Extracts a raw substitution into a `RewriteRule`.
   */
  def extractRule
    (using lib: Library, proof: lib.Proof)
    (rule: proof.Fact | F.Formula): RewriteRule =
      rule match
        case f: Formula @unchecked => (f: @unchecked) match
          case === #@ (l: Term) #@ (r: Term) => TermRewriteRule(l, r)
          case <=> #@ (l: Formula) #@ (r: Formula) => FormulaRewriteRule(l, r)
        case f: proof.Fact @unchecked => extractRule(proof.getSequent(f).right.head)

  /**
   * Partitions raw substitution rules into free and confined rules, also
   * creating a source map, mapping each rule to the `Fact` it was derived from,
   * for proof construction.
   */
  def partition
    (using lib: Library, proof: lib.Proof)
    (substitutions: Seq[proof.Fact | F.Formula]): (Map[RewriteRule, proof.Fact], RewriteContext) =
      substitutions.foldLeft((Map.empty, RewriteContext.empty)):
        case ((source, ctx), rule) =>
          val erule = extractRule(rule)
          val (l, r) = (erule.l, erule.r)
          rule match
            case f: Formula @unchecked => 
              (source + (erule -> erule.source), ctx.withConfinedRule(l, r).withBound(f.freeVars))
            case j: lib.JUSTIFICATION =>
              (source + (erule -> j), ctx.withFreeRule(l, r))
            case f: proof.Fact @unchecked =>
              (source + (erule -> f), ctx.withConfinedRule(l, r))
  
  /**
   * Checks if a raw substitution input can be used as a rewrite rule (is === or
   * <=>, basically).
   */ 
  def validSubstitutionRule
    (using lib: lisa.prooflib.Library, proof: lib.Proof)
    (rule: (proof.Fact | F.Formula)): Boolean =
      rule match
        // as formula
        case f: Formula @unchecked => f match
          case === #@ l #@ r => true
          case <=> #@ l #@ r => true
          case _ => false
        // as a justification
        case just: proof.Fact @unchecked => 
          val sequent = proof.getSequent(just)
          sequent.right.size == 1 && validSubstitutionRule(sequent.right.head)

  object Apply extends ProofTactic:
    def apply
      (using lib: Library, proof: lib.Proof)
      (substitutions: (proof.Fact | F.Formula)*)
      (premiseStep: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = 

        // are all substitution rules actually valid?
        // if not, exit early

        val violatingFacts = substitutions.collect: 
          case f: proof.Fact @unchecked if !validSubstitutionRule(f) => proof.getSequent(f)

        val violatingFormulas = substitutions.collect:
          case f: F.Formula @unchecked  if !validSubstitutionRule(f) => f

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
          inline def collectRewritingPairs
            (base: Set[Formula], target: Set[Formula]): Option[Seq[RewriteResult]] =
              base.iterator.map: formula =>
                target.collectFirstDefined: target =>
                  rewrite(using ctx)(formula, target)
              .toOptionSeq

          // collect the set of formulas in `base` that rewrite to *no* formula
          // in `target`. Guaranteed to be non-empty if
          // `collectRewritingPairs(base, target)` is None.
          inline def collectViolatingPairs
            (base: Set[Formula], target: Set[Formula]): Set[Formula] =
                premise.left.filter: formula =>
                  bot.left.forall: target =>
                    rewrite(using ctx)(formula, target).isEmpty


          val leftSubsts = collectRewritingPairs(premise.left, bot.left)
          val rightSubsts = collectRewritingPairs(premise.right, bot.right)

          if leftSubsts.isEmpty then
            // error, find formulas that failed to rewrite
            val msgBase = "Could not rewrite LHS of premise into conclusion with given substitutions.\nViolating Formulas:"
            val msgList = 
                collectViolatingPairs(premise.left, bot.left)
                .zipWithIndex
                .map: 
                  case (formula, i) => s"\t${i + 1}. $formula"

            proof.InvalidProofTactic(msgBase + msgList.mkString("\n"))
          else if rightSubsts.isEmpty then
            // error, find formulas that failed to rewrite
            val msgBase = "Could not rewrite LHS of premise into conclusion with given substitutions.\nViolating Formulas:"
            val msgList = 
                collectViolatingPairs(premise.right, bot.right)
                .zipWithIndex
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
              val leftRules = leftRewrites.map(_.rule)
              val rightRules = rightRewrites.map(_.rule)

              // instantiated discharges

              val leftDischarges = leftRules.map(r => r -> sourceMap(r))
              val rightDischarges = rightRules.map(r => r -> sourceMap(r))

              val discharges = leftDischarges ++ rightDischarges

              // start proof
              have(andAll(premise.left) |- premise.right) by Restate.from(premiseStep)
              
              // left rewrites
              val leftFormulas = leftRules.map(_.toFormula)
              val preLeft = leftRewrites.map(_.toLeft)
              val postLeft = leftRewrites.map(_.toRight)
              val leftVars = leftRewrites.head.lambda._1
              val leftLambda = andAll(leftRewrites.map(_.lambda._2))
              thenHave(andAll(preLeft) |- premise.right) by Restate
              thenHave(andAll(preLeft) +: leftFormulas |- premise.right) by Weakening
              thenHave(andAll(postLeft) +: leftFormulas |- premise.right) by LeftSubstEq.withParameters(leftRules.map(r => r.l -> r.r), leftVars -> leftLambda)

              val rpremise = lastStep.bot

              // right rewrites
              val rightFormulas = rightRules.map(_.toFormula)
              val preRight = rightRewrites.map(_.toLeft).toSet
              val postRight = rightRewrites.map(_.toRight).toSet
              val rightVars = rightRewrites.head.lambda._1
              val rightLambda = orAll(rightRewrites.map(_.lambda._2))
              thenHave(rpremise.left |- orAll(preRight)) by Restate
              thenHave(rpremise.left ++ rightFormulas |- orAll(preRight)) by Weakening
              thenHave(rpremise.left ++ rightFormulas |- orAll(postRight)) by RightSubstEq.withParameters(rightRules.map(r => r.l -> r.r), rightVars -> rightLambda)

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

  */

  // object applySubst extends ProofTactic {

  //   private def condflat[T](s: Seq[(T, Boolean)]): (Seq[T], Boolean) = (s.map(_._1), s.exists(_._2))

  //   private def findSubterm2(t: Term, subs: Seq[(Variable, Term)]): (Term, Boolean) = {
  //     val eq = subs.find(s => isSameTerm(t, s._2))
  //     if (eq.nonEmpty) (eq.get._1, true)
  //     else {
  //       val induct = condflat(t.args.map(te => findSubterm2(te, subs)))
  //       if (!induct._2) (t, false)
  //       else
  //         (t.label.applySeq(induct._1), true)

  //     }

  //   }
  //   private def findSubterm2(f: Formula, subs: Seq[(Variable, Term)]): (Formula, Boolean) = {
  //     f match {
  //       case f: VariableFormula => (f, false)
  //       case f: ConstantFormula => (f, false)
  //       case AppliedPredicate(label, args) =>
  //         val induct = condflat(args.map(findSubterm2(_, subs)))
  //         if (!induct._2) (f, false)
  //         else (AppliedPredicate(label, induct._1), true)
  //       case AppliedConnector(label, args) =>
  //         val induct = condflat(args.map(findSubterm2(_, subs)))
  //         if (!induct._2) (f, false)
  //         else (AppliedConnector(label, induct._1), true)
  //       case BinderFormula(label, bound, inner) =>
  //         val fv_in_f = subs.flatMap(e => e._2.freeVariables + e._1)
  //         if (!fv_in_f.contains(bound)) {
  //           val induct = findSubterm2(inner, subs)
  //           if (!induct._2) (f, false)
  //           else (BinderFormula(label, bound, induct._1), true)
  //         } else {
  //           val newv = Variable(freshId((f.freeVariables ++ fv_in_f).map(_.id), bound.id))
  //           val newInner = inner.substitute(bound := newv)
  //           val induct = findSubterm2(newInner, subs)
  //           if (!induct._2) (f, false)
  //           else (BinderFormula(label, newv, induct._1), true)
  //         }
  //     }
  //   }

  //   private def findSubformula2(f: Formula, subs: Seq[(VariableFormula, Formula)]): (Formula, Boolean) = {
  //     val eq = subs.find(s => isSame(f, s._2))
  //     if (eq.nonEmpty) (eq.get._1, true)
  //     else
  //       f match {
  //         case f: AtomicFormula => (f, false)
  //         case AppliedConnector(label, args) =>
  //           val induct = condflat(args.map(findSubformula2(_, subs)))
  //           if (!induct._2) (f, false)
  //           else (AppliedConnector(label, induct._1), true)
  //         case BinderFormula(label, bound, inner) =>
  //           val fv_in_f = subs.flatMap(_._2.freeVariables)
  //           if (!fv_in_f.contains(bound)) {
  //             val induct = findSubformula2(inner, subs)
  //             if (!induct._2) (f, false)
  //             else (BinderFormula(label, bound, induct._1), true)
  //           } else {
  //             val newv = Variable(freshId((f.freeVariables ++ fv_in_f).map(_.id), bound.id))
  //             val newInner = inner.substitute(bound := newv)
  //             val induct = findSubformula2(newInner, subs)
  //             if (!induct._2) (f, false)
  //             else (BinderFormula(label, newv, induct._1), true)
  //           }
  //       }
  //   }

  //   def findSubterm(t: Term, subs: Seq[(Variable, Term)]): Option[LambdaExpression[Term, Term, ?]] = {
  //     val vars = subs.map(_._1)
  //     val r = findSubterm2(t, subs)
  //     if (r._2) Some(LambdaExpression(vars, r._1, vars.size))
  //     else None
  //   }

  //   def findSubterm(f: Formula, subs: Seq[(Variable, Term)]): Option[LambdaExpression[Term, Formula, ?]] = {
  //     val vars = subs.map(_._1)
  //     val r = findSubterm2(f, subs)
  //     if (r._2) Some(LambdaExpression(vars, r._1, vars.size))
  //     else None
  //   }

  //   def findSubformula(f: Formula, subs: Seq[(VariableFormula, Formula)]): Option[LambdaExpression[Formula, Formula, ?]] = {
  //     val vars = subs.map(_._1)
  //     val r = findSubformula2(f, subs)
  //     if (r._2) Some(LambdaExpression(vars, r._1, vars.size))
  //     else None
  //   }

  //   def applyLeftRight(using lib: lisa.prooflib.Library, proof: lib.Proof)(
  //       phi: Formula
  //   )(premise: proof.Fact)(rightLeft: Boolean = false, toLeft: Boolean = true, toRight: Boolean = true): proof.ProofTacticJudgement = {
  //     import lisa.utils.K
  //     val originSequent = proof.getSequent(premise)
  //     val leftOrigin = AppliedConnector(And, originSequent.left.toSeq)
  //     val rightOrigin = AppliedConnector(Or, originSequent.right.toSeq)

  //     if (!toLeft && !toRight) return proof.InvalidProofTactic("applyLeftRight called with no substitution selected (toLeft or toRight).")

  //     phi match {
  //       case AppliedPredicate(label, args) if label == equality =>
  //         val left = args(0)
  //         val right = args(1)
  //         val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.allSchematicLabels).map(_.id)
  //         val v = Variable(nFreshId(fv_in_phi, 1).head)
  //         lazy val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
  //         lazy val isolatedRight = originSequent.right.map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
  //         if ((!toLeft || isolatedLeft.forall(_._2.isEmpty)) && (!toRight || isolatedRight.forall(_._2.isEmpty)))
  //           if (rightLeft)
  //             return proof.InvalidProofTactic(s"There is no instance of ${right} to replace.")
  //           else
  //             applyLeftRight(equality(right, left))(premise)(true, toLeft, toRight) match {
  //               case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${left} to replace.")
  //               case v: proof.ValidProofTactic => return v
  //             }

  //         val leftForm = AppliedConnector(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
  //         val rightForm = AppliedConnector(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
  //         val newleft = if (toLeft) isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.applyUnsafe(Seq(right))) else originSequent.left
  //         val newright = if (toRight) isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.applyUnsafe(Seq(right))) else originSequent.right
  //         val result1: Sequent = (AppliedConnector(And, newleft.toSeq), phi) |- rightOrigin
  //         val result2: Sequent = result1.left |- AppliedConnector(Or, newright.toSeq)
  //         var scproof: Seq[K.SCProofStep] = Seq(K.Restate((leftOrigin |- rightOrigin).underlying, -1))
  //         if (toLeft)
  //           scproof = scproof :+ K.LeftSubstEq(
  //             result1.underlying,
  //             scproof.length - 1,
  //             List(K.LambdaTermTerm(Seq(), left.underlying) -> (K.LambdaTermTerm(Seq(), right.underlying))),
  //             (Seq(v.underlyingLabel), leftForm.underlying)
  //           )
  //         if (toRight)
  //           scproof = scproof :+ K.RightSubstEq(
  //             result2.underlying,
  //             scproof.length - 1,
  //             List(K.LambdaTermTerm(Seq(), left.underlying) -> (K.LambdaTermTerm(Seq(), right.underlying))),
  //             (Seq(v.underlyingLabel), rightForm.underlying)
  //           )
  //         val bot = newleft + phi |- newright
  //         scproof = scproof :+ K.Restate(bot.underlying, scproof.length - 1)

  //         proof.ValidProofTactic(
  //           bot,
  //           scproof,
  //           Seq(premise)
  //         )

  //       case AppliedConnector(label, args) if label == Iff =>
  //         val left = args(0)
  //         val right = args(1)
  //         val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.allSchematicLabels).map(_.id)
  //         val H = VariableFormula(nFreshId(fv_in_phi, 1).head)
  //         lazy val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
  //         lazy val isolatedRight = originSequent.right.map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
  //         if ((!toLeft || isolatedLeft.forall(_._2.isEmpty)) && (!toRight || isolatedRight.forall(_._2.isEmpty)))
  //           if (rightLeft)
  //             return proof.InvalidProofTactic(s"There is no instance of ${right} to replace.")
  //           else
  //             applyLeftRight(Iff(right, left))(premise)(true, toLeft, toRight) match {
  //               case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${left} to replace.")
  //               case v: proof.ValidProofTactic => return v
  //             }

  //         val leftForm = AppliedConnector(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
  //         val rightForm = AppliedConnector(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
  //         val newleft = if (toLeft) isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.applyUnsafe(Seq(right))) else originSequent.left
  //         val newright = if (toRight) isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.applyUnsafe(Seq(right))) else originSequent.right
  //         val result1: Sequent = (AppliedConnector(And, newleft.toSeq), phi) |- rightOrigin
  //         val result2: Sequent = result1.left |- AppliedConnector(Or, newright.toSeq)

  //         var scproof: Seq[K.SCProofStep] = Seq(K.Restate((leftOrigin |- rightOrigin).underlying, -1))
  //         if (toLeft)
  //           scproof = scproof :+ K.LeftSubstIff(
  //             result1.underlying,
  //             scproof.length - 1,
  //             List(K.LambdaTermFormula(Seq(), left.underlying) -> (K.LambdaTermFormula(Seq(), right.underlying))),
  //             (Seq(H.underlyingLabel), leftForm.underlying)
  //           )
  //         if (toRight)
  //           scproof = scproof :+ K.RightSubstIff(
  //             result2.underlying,
  //             scproof.length - 1,
  //             List(K.LambdaTermFormula(Seq(), left.underlying) -> (K.LambdaTermFormula(Seq(), right.underlying))),
  //             (Seq(H.underlyingLabel), rightForm.underlying)
  //           )

  //         val bot = newleft + phi |- newright
  //         scproof = scproof :+ K.Restate(bot.underlying, scproof.length - 1)

  //         proof.ValidProofTactic(
  //           bot,
  //           scproof,
  //           Seq(premise)
  //         )
  //       case _ => proof.InvalidProofTactic(s"Formula in applySingleSimp need to be of the form a=b or q<=>p and not ${phi}")
  //     }
  //   }

  //   @nowarn("msg=.*the type test for proof.Fact cannot be checked at runtime*")
  //   def apply(using
  //       lib: lisa.prooflib.Library,
  //       proof: lib.Proof,
  //       line: sourcecode.Line,
  //       file: sourcecode.File
  //   )(f: proof.Fact | Formula, rightLeft: Boolean = false, toLeft: Boolean = true, toRight: Boolean = true)(
  //       premise: proof.Fact
  //   ): proof.ProofTacticJudgement = {
  //     f match {
  //       case phi: Formula => applyLeftRight(phi)(premise)(rightLeft, toLeft, toRight)
  //       case f: proof.Fact =>
  //         val seq = proof.getSequent(f)
  //         val phi = seq.right.head
  //         val sp = TacticSubproof {
  //           val x = applyLeftRight(phi)(premise)(rightLeft, toLeft, toRight)
  //           proof.library.have(x)
  //           proof.library.andThen(SimpleDeducedSteps.Discharge(f))
  //         }

  //         BasicStepTactic.unwrapTactic(sp)("Subproof substitution fail.")
  //     }

  //   }

  //   def toLeft(using lib: lisa.prooflib.Library, proof: lib.Proof, line: sourcecode.Line, file: sourcecode.File)(f: proof.Fact | Formula, rightLeft: Boolean = false)(
  //       premise: proof.Fact
  //   ): proof.ProofTacticJudgement = apply(f, rightLeft, toLeft = true, toRight = false)(premise)

  //   def toRight(using lib: lisa.prooflib.Library, proof: lib.Proof, line: sourcecode.Line, file: sourcecode.File)(f: proof.Fact | Formula, rightLeft: Boolean = false)(
  //       premise: proof.Fact
  //   ): proof.ProofTacticJudgement = apply(f, rightLeft, toLeft = false, toRight = true)(premise)

  // }

end Substitution
