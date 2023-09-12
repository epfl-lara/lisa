package lisa.prooflib

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps
import lisa.utils.FOLPrinter
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.unification.UnificationUtils
import lisa.utils.unification.UnificationUtils.getContextFormulaSet

import scala.annotation.nowarn
import scala.collection.mutable.{Map as MMap}

object Substitution {
  def validRule(using lib: lisa.prooflib.Library, proof: lib.Proof)(r: (proof.Fact | Formula | RunningTheory#Justification)): Boolean =
    r match {
      case PredicateFormula(`equality`, _) => true
      case ConnectorFormula(Iff, _) => true
      case f: proof.Fact @unchecked => proof.sequentOfFact(f).right.size == 1 && validRule(proof.sequentOfFact(f).right.head)
      case j: RunningTheory#Justification =>
        proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.size == 1 && validRule(proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.head)
      case _ => false
    }

  object ApplyRules extends ProofTactic {
    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(
        premise: proof.Fact
    )(bot: Sequent): proof.ProofTacticJudgement = {
      // figure out instantiations for rules
      // takes a premise
      val premiseSequent: Sequent = proof.getSequent(premise)

      // make sure substitutions are all valid
      val violatingSubstitutions = substitutions.collect {
        case f: proof.Fact if !validRule(f) => proof.sequentOfFact(f)
        case j: RunningTheory#Justification if !validRule(j) => proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification])
      }

      val violatingFormulas = substitutions.collect {
        case f: Formula if !validRule(f) => f
      }

      if (!violatingSubstitutions.isEmpty)
        // return error
        proof.InvalidProofTactic("Substitution rules must have a single equality or equivalence on the right-hand side. Violating sequents passed:\n" + violatingSubstitutions.zipWithIndex.map {
          (s, i) =>
            s"${i + 1}. ${FOLPrinter.prettySequent(s)}"
        })
      else if (!violatingFormulas.isEmpty)
        proof.InvalidProofTactic("Substitution rules must be equalities or equivalences. Violating formulas passed:\n" + violatingFormulas.zipWithIndex.map { (s, i) =>
          s"${i + 1}. ${FOLPrinter.prettyFormula(s)}"
        })
      else {
        // proceed as usual

        // maintain a list of where subtitutions come from
        val sourceOf: MMap[(Formula, Formula) | (Term, Term), proof.Fact] = MMap()
        val takenTermVars = premiseSequent.left.flatMap(_.freeVariables).toSet union substitutions.collect { case f: Formula => f.freeVariables.toSet }.foldLeft(Set.empty)(_.union(_))
        val takenFormulaVars = premiseSequent.left.flatMap(_.freeVariableFormulaLabels).toSet union substitutions
          .collect { case f: Formula => f.freeVariableFormulaLabels.toSet }
          .foldLeft(Set.empty)(_.union(_)) // TODO: should this just be the LHS of the premise sequent instead?

        var freeEqualitiesPre = List[(Term, Term)]()
        var confinedEqualitiesPre = List[(Term, Term)]()
        var freeIffsPre = List[(Formula, Formula)]()
        var confinedIffsPre = List[(Formula, Formula)]()

        def updateSource(t: (Formula, Formula) | (Term, Term), f: proof.Fact) = {
          sourceOf.update(t, f)
          sourceOf.update(t.swap.asInstanceOf[(Formula, Formula) | (Term, Term)], f)
        }

        // collect substitutions into the right buckets
        substitutions.foreach {
          case f: Formula =>
            f match {
              case PredicateFormula(`equality`, Seq(l, r)) =>
                confinedEqualitiesPre = (l, r) :: confinedEqualitiesPre
              case ConnectorFormula(Iff, Seq(l, r)) =>
                confinedIffsPre = (l, r) :: confinedIffsPre
              case _ => ()
            }
          case j: RunningTheory#Justification =>
            proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.head match {
              case PredicateFormula(`equality`, Seq(l, r)) =>
                updateSource((l, r), j.asInstanceOf[lib.theory.Justification])
                freeEqualitiesPre = (l, r) :: freeEqualitiesPre
              case ConnectorFormula(Iff, Seq(l, r)) =>
                updateSource((l, r), j.asInstanceOf[lib.theory.Justification])
                freeIffsPre = (l, r) :: freeIffsPre
              case _ => ()
            }
          case f: proof.Fact @unchecked =>
            proof.sequentOfFact(f).right.head match {
              case PredicateFormula(`equality`, Seq(l, r)) =>
                updateSource((l, r), f)
                confinedEqualitiesPre = (l, r) :: confinedEqualitiesPre
              case ConnectorFormula(Iff, Seq(l, r)) =>
                updateSource((l, r), f)
                confinedIffsPre = (l, r) :: confinedIffsPre
              case _ => ()
            }
        }

        // get the original and swapped versions
        val freeEqualities = freeEqualitiesPre ++ freeEqualitiesPre.map(_.swap)
        val confinedEqualities = confinedEqualitiesPre ++ confinedEqualitiesPre.map(_.swap)
        val freeIffs = freeIffsPre ++ freeIffsPre.map(_.swap)
        val confinedIffs = confinedIffsPre ++ confinedIffsPre.map(_.swap)

        val filteredPrem = (premiseSequent.left filter {
          case PredicateFormula(`equality`, Seq(l, r)) if freeEqualities.contains((l, r)) || confinedEqualities.contains((l, r)) => false
          case ConnectorFormula(Iff, Seq(l, r)) if freeIffs.contains((l, r)) || confinedIffs.contains((l, r)) => false
          case _ => true
        }).toSeq

        val filteredBot = (bot.left filter {
          case PredicateFormula(`equality`, Seq(l, r)) if freeEqualities.contains((l, r)) || confinedEqualities.contains((l, r)) => false
          case ConnectorFormula(Iff, Seq(l, r)) if freeIffs.contains((l, r)) || confinedIffs.contains((l, r)) => false
          case _ => true
        }).toSeq

        // construct the right instantiations
        lazy val leftContextsOpt = getContextFormulaSet(filteredPrem, filteredBot, freeEqualities, freeIffs, confinedEqualities, takenTermVars, confinedIffs, takenFormulaVars)
        lazy val rightContextsOpt = getContextFormulaSet(premiseSequent.right.toSeq, bot.right.toSeq, freeEqualities, freeIffs, confinedEqualities, takenTermVars, confinedIffs, takenFormulaVars)

        lazy val violatingFormulaLeft: Option[Formula] = Some(top())
        lazy val violatingFormulaRight: Option[Formula] = Some(top())

        if (leftContextsOpt.isEmpty)
          proof.InvalidProofTactic(s"Could not rewrite LHS of premise into conclusion with given substitutions.\nViolating Formula: ${FOLPrinter.prettyFormula(violatingFormulaLeft.get)}")
        else if (rightContextsOpt.isEmpty)
          proof.InvalidProofTactic(s"Could not rewrite RHS of premise into conclusion with given substitutions.\nViolating Formula: ${FOLPrinter.prettyFormula(violatingFormulaRight.get)}")
        else {
          // actually construct proof

          TacticSubproof {

            def eq(rule: (Term, Term)) = PredicateFormula(equality, Seq(rule._1, rule._2))
            def iff(rule: (Formula, Formula)) = ConnectorFormula(Iff, Seq(rule._1, rule._2))

            def eqSource(rule: (Term, Term)) = lib.have(eq(rule) |- eq(rule)) by SimpleDeducedSteps.Restate
            def iffSource(rule: (Formula, Formula)) = lib.have(iff(rule) |- iff(rule)) by SimpleDeducedSteps.Restate

            val leftContexts = leftContextsOpt.get // remove the options
            val rightContexts = rightContextsOpt.get // remove the options

            val leftBody = ConnectorFormula(And, leftContexts.map(_.body))

            val defaultLeft = UnificationUtils.FormulaRewriteLambda(body = leftBody)

            val leftContextReduced = leftContexts.foldLeft(defaultLeft) { (f, s) =>
              UnificationUtils.FormulaRewriteLambda(
                termRules = f.termRules ++ s.termRules,
                formulaRules = f.formulaRules ++ s.formulaRules,
                leftBody
              )
            }

            val rightBody = ConnectorFormula(Or, rightContexts.map(_.body))

            val defaultRight = UnificationUtils.FormulaRewriteLambda(body = rightBody)

            val rightContextReduced = rightContexts.foldLeft(defaultRight) { (f, s) =>
              UnificationUtils.FormulaRewriteLambda(
                termRules = f.termRules ++ s.termRules,
                formulaRules = f.formulaRules ++ s.formulaRules,
                rightBody
              )
            }

            // find the justifications for each rule, or generate them, as required
            val leftDischarges =
              leftContextReduced.termRules.map { case (_, (rule, subst)) =>
                sourceOf.get(rule) match {
                  case Some(f: proof.Fact) =>
                    f.of(subst.toSeq.map((l, r) => (l, lambda(Seq(), r))): _*)
                  // case Some(j: lib.theory.Justification) =>
                  //   j.of(subst.toSeq.map((l, r) => (l, lambda(Seq(), r))): _*)
                  case _ =>
                    eqSource(rule).of()
                }
              } ++
                leftContextReduced.formulaRules.map { case (_, (rule, subst)) =>
                  sourceOf.get(rule) match {
                    case Some(f: proof.Fact) =>
                      f.of(subst._1.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))) ++ subst._2.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))): _*)
                    // case Some(j: lib.theory.Justification) =>
                    //   j.of(subst._1.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))) ++ subst._2.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))): _*)
                    case _ =>
                      iffSource(rule).of()
                  }
                }
            val rightDischarges =
              rightContextReduced.termRules.map { case (_, (rule, subst)) =>
                sourceOf.get(rule) match {
                  case Some(f: proof.Fact) =>
                    f.of(subst.toSeq.map((l, r) => (l, lambda(Seq(), r))): _*)
                  // case Some(j: lib.theory.Justification) =>
                  //   j.of(subst.toSeq.map((l, r) => (l, lambda(Seq(), r))): _*)
                  case None =>
                    eqSource(rule).of()
                }
              } ++
                rightContextReduced.formulaRules.map { case (_, (rule, subst)) =>
                  sourceOf.get(rule) match {
                    case Some(f: proof.Fact) =>
                      f.of(subst._1.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))) ++ subst._2.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))): _*)
                    // case Some(j: lib.theory.Justification) =>
                    //   j.of(subst._1.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))) ++ subst._2.toSeq.map((l, r) => (l, lambda(Seq[VariableLabel](), r))): _*)
                    case None =>
                      iffSource(rule).of()
                  }
                }

            val discharges = leftDischarges ++ rightDischarges

            // -------------------
            // LEFT SUBSTITUTIONS
            // -------------------
            val nextSequent = {
              // we have a lambda like λx. Λp. body
              // where the p are formula variables, and the x are term variables
              val ctx = leftContextReduced

              val termVars = ctx.termRules.map(_._1)

              val termInputs = ctx.termRules.map { case (_, (rule, subst)) =>
                (
                  substituteVariables(rule._1, subst),
                  substituteVariables(rule._2, subst)
                )
              }

              lazy val (termInputsL, termInputsR) = (termInputs.map(_._1), termInputs.map(_._2))

              val formulaVars = ctx.formulaRules.map(_._1)

              val formulaInputs = ctx.formulaRules.map { case (_, (rule, subst)) =>
                (
                  substituteFormulaVariables(substituteVariables(rule._1, subst._2), subst._1),
                  substituteFormulaVariables(substituteVariables(rule._2, subst._2), subst._1)
                )
              }

              val (formulaInputsL, formulaInputsR) = (formulaInputs.map(_._1), formulaInputs.map(_._2))

              // get premise into the right form
              val prem = ConnectorFormula(And, filteredPrem.toSeq) |- ConnectorFormula(Or, premiseSequent.right.toSeq)
              val eqs = termInputs.map(eq(_))
              val iffs = formulaInputs.map(iff(_))
              val premiseWithSubst = prem ++<< (eqs |- ()) ++<< (iffs |- ())
              lib.have(premiseWithSubst) by BasicStepTactic.Weakening(premise)

              // left ===
              val eqSubst = (termVars zip termInputsR).toMap
              val formSubstL = (formulaVars zip formulaInputsL).toMap
              val lhsAfterEq = substituteFormulaVariables(substituteVariables(ctx.body, eqSubst), formSubstL)
              val sequentAfterEqPre = lhsAfterEq |- premiseWithSubst.right
              val sequentAfterEq = sequentAfterEqPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (p = left formulas)
              lib.thenHave(sequentAfterEq) by BasicStepTactic.LeftSubstEq(termInputs.toList, lambda(termVars, substituteFormulaVariables(ctx.body, formSubstL)))

              // left <=>
              val formSubstR = (formulaVars zip formulaInputsR).toMap
              val lhsAfterIff = substituteFormulaVariables(substituteVariables(ctx.body, eqSubst), formSubstR)
              val sequentAfterIffPre = lhsAfterIff |- sequentAfterEq.right
              val sequentAfterIff = sequentAfterIffPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (x = right terms)
              lib.thenHave(sequentAfterIff) by BasicStepTactic.LeftSubstIff(formulaInputs.toList, lambda(formulaVars, substituteVariables(ctx.body, eqSubst)))
              sequentAfterIff
            }

            // -------------------
            // RIGHT SUBSTITUTIONS
            // -------------------
            val finalSequent = {
              // we have a lambda like λx. Λp. body
              // where the p are formula variables, and the x are term variables
              val ctx = rightContextReduced

              val termVars = ctx.termRules.map(_._1)

              val termInputs = ctx.termRules.map { case (_, (rule, subst)) =>
                (
                  substituteVariables(rule._1, subst),
                  substituteVariables(rule._2, subst)
                )
              }

              lazy val (termInputsL, termInputsR) = (termInputs.map(_._1), termInputs.map(_._2))

              val formulaVars = ctx.formulaRules.map(_._1)

              val formulaInputs = ctx.formulaRules.map { case (_, (rule, subst)) =>
                (
                  substituteFormulaVariables(substituteVariables(rule._1, subst._2), subst._1),
                  substituteFormulaVariables(substituteVariables(rule._2, subst._2), subst._1)
                )
              }

              val (formulaInputsL, formulaInputsR) = (formulaInputs.map(_._1), formulaInputs.map(_._2))

              // get premise into the right form
              val prem = nextSequent
              val eqs = termInputs.map(eq(_))
              val iffs = formulaInputs.map(iff(_))
              val premiseWithSubst = prem ++<< (eqs |- ()) ++<< (iffs |- ())
              lib.thenHave(premiseWithSubst) by BasicStepTactic.Weakening

              // right ===
              val eqSubst = (termVars zip termInputsR).toMap
              val formSubstL = (formulaVars zip formulaInputsL).toMap
              val rhsAfterEq = substituteFormulaVariables(substituteVariables(ctx.body, eqSubst), formSubstL)
              val sequentAfterEqPre = premiseWithSubst.left |- rhsAfterEq
              val sequentAfterEq = sequentAfterEqPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (p = left formulas)
              lib.thenHave(sequentAfterEq) by BasicStepTactic.RightSubstEq(termInputs.toList, lambda(termVars, substituteFormulaVariables(ctx.body, formSubstL)))

              // right <=>
              val formSubstR = (formulaVars zip formulaInputsR).toMap
              val rhsAfterIff = substituteFormulaVariables(substituteVariables(ctx.body, eqSubst), formSubstR)
              val sequentAfterIffPre = sequentAfterEq.left |- rhsAfterIff
              val sequentAfterIff = sequentAfterIffPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (x = right terms)
              lib.thenHave(sequentAfterIff) by BasicStepTactic.RightSubstIff(formulaInputs.toList, lambda(formulaVars, substituteVariables(ctx.body, eqSubst)))
            }

            // discharge any assumptions

            // custom discharge
            // invariant: all facts are known to have only one formula in their RHS
            discharges.foreach { f =>
              lib.thenHave(lib.lastStep.bot +<< f.result.right.head) by BasicStepTactic.Weakening // in case of double discharges, add the formula back in
              lib.have(lib.lastStep.bot -<? f.result.right.head ++ (f.result.left |- ())) by BasicStepTactic.Cut.withParameters(f.result.right.head)(f, lib.lastStep)
            }

            // finally, make sure our substitutions and discharges led us to the required conclusion
            lib.thenHave(bot) by BasicStepTactic.Weakening
          }
        }
      }
    }
  }

  object applySubst extends ProofTactic {

    private def condflat[T](s: Seq[(T, Boolean)]): (Seq[T], Boolean) = (s.map(_._1), s.exists(_._2))

    private def findSubterm2(t: Term, subs: Seq[(VariableLabel, Term)]): (Term, Boolean) = {
      val eq = subs.find(s => isSameTerm(t, s._2))
      if (eq.nonEmpty) (eq.get._1(), true)
      else {
        val induct = condflat(t.args.map(te => findSubterm2(te, subs)))
        if (!induct._2) (t, false)
        else (Term(t.label, induct._1), true)

      }

    }

    private def findSubterm2(f: Formula, subs: Seq[(VariableLabel, Term)]): (Formula, Boolean) = {
      f match {
        case PredicateFormula(label, args) =>
          val induct = condflat(args.map(findSubterm2(_, subs)))
          if (!induct._2) (f, false)
          else (PredicateFormula(label, induct._1), true)
        case ConnectorFormula(label, args) =>
          val induct = condflat(args.map(findSubterm2(_, subs)))
          if (!induct._2) (f, false)
          else (ConnectorFormula(label, induct._1), true)
        case BinderFormula(label, bound, inner) =>
          val fv_in_f = subs.flatMap(e => e._2.freeVariables + e._1)
          if (!fv_in_f.contains(bound)) {
            val induct = findSubterm2(inner, subs)
            if (!induct._2) (f, false)
            else (BinderFormula(label, bound, induct._1), true)
          } else {
            val newv = VariableLabel(freshId((f.freeVariables ++ fv_in_f).map(_.id), bound.id))
            val newInner = substituteVariables(inner, Map(bound -> newv()))
            val induct = findSubterm2(newInner, subs)
            if (!induct._2) (f, false)
            else (BinderFormula(label, newv, induct._1), true)
          }
      }
    }

    private def findSubformula2(f: Formula, subs: Seq[(VariableFormulaLabel, Formula)]): (Formula, Boolean) = {
      val eq = subs.find(s => isSame(f, s._2))
      if (eq.nonEmpty) (eq.get._1(), true)
      else
        f match {
          case PredicateFormula(label, args) =>
            (f, false)
          case ConnectorFormula(label, args) =>
            val induct = condflat(args.map(findSubformula2(_, subs)))
            if (!induct._2) (f, false)
            else (ConnectorFormula(label, induct._1), true)
          case BinderFormula(label, bound, inner) =>
            val fv_in_f = subs.flatMap(_._2.freeVariables)
            if (!fv_in_f.contains(bound)) {
              val induct = findSubformula2(inner, subs)
              if (!induct._2) (f, false)
              else (BinderFormula(label, bound, induct._1), true)
            } else {
              val newv = VariableLabel(freshId((f.freeVariables ++ fv_in_f).map(_.id), bound.id))
              val newInner = substituteVariables(inner, Map(bound -> newv()))
              val induct = findSubformula2(newInner, subs)
              if (!induct._2) (f, false)
              else (BinderFormula(label, newv, induct._1), true)
            }
        }
    }
    def findSubterm(t: Term, subs: Seq[(VariableLabel, Term)]): Option[LambdaTermTerm] = {
      val vars = subs.map(_._1)
      val r = findSubterm2(t, subs)
      if (r._2) Some(LambdaTermTerm(vars, r._1))
      else None
    }

    def findSubterm(f: Formula, subs: Seq[(VariableLabel, Term)]): Option[LambdaTermFormula] = {
      val vars = subs.map(_._1)
      val r = findSubterm2(f, subs)
      if (r._2) Some(LambdaTermFormula(vars, r._1))
      else None
    }

    def findSubformula(f: Formula, subs: Seq[(VariableFormulaLabel, Formula)]): Option[LambdaFormulaFormula] = {
      val vars = subs.map(_._1)
      val r = findSubformula2(f, subs)
      if (r._2) Some(LambdaFormulaFormula(vars, r._1))
      else None
    }

    def applyLeftRight(using lib: lisa.prooflib.Library, proof: lib.Proof)(
        phi: Formula
    )(premise: proof.Fact)(rightLeft: Boolean = false, toLeft: Boolean = true, toRight: Boolean = true): proof.ProofTacticJudgement = {
      val originSequent = proof.getSequent(premise)
      val leftOrigin = ConnectorFormula(And, originSequent.left.toSeq)
      val rightOrigin = ConnectorFormula(Or, originSequent.right.toSeq)

      if (!toLeft && !toRight) return proof.InvalidProofTactic("applyLeftRight called with no substitution selected (toLeft or toRight).")

      phi match {
        case PredicateFormula(label, args) if label == equality =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.freeVariables).map(_.id)
          val v = VariableLabel(nFreshId(fv_in_phi, 1).head)
          lazy val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
          lazy val isolatedRight = originSequent.right.map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
          if ((!toLeft || isolatedLeft.forall(_._2.isEmpty)) && (!toRight || isolatedRight.forall(_._2.isEmpty)))
            if (rightLeft)
              return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyTerm(right)} to replace.")
            else
              applyLeftRight(equality(right, left))(premise)(true, toLeft, toRight) match {
                case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyTerm(left)} to replace.")
                case v: proof.ValidProofTactic => return v
              }

          val leftForm = ConnectorFormula(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val rightForm = ConnectorFormula(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val newleft = if (toLeft) isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.left
          val newright = if (toRight) isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.right
          val result1: Sequent = (ConnectorFormula(And, newleft.toSeq), phi) |- rightOrigin
          val result2: Sequent = result1.left |- ConnectorFormula(Or, newright.toSeq)

          var scproof: Seq[SC.SCProofStep] = Seq(SC.Restate(leftOrigin |- rightOrigin, -1))
          if (toLeft) scproof = scproof :+ SC.LeftSubstEq(result1, scproof.length - 1, List(left -> right), LambdaTermFormula(Seq(v), leftForm))
          if (toRight) scproof = scproof :+ SC.RightSubstEq(result2, scproof.length - 1, List(left -> right), LambdaTermFormula(Seq(v), rightForm))
          scproof = scproof :+ SC.Restate(newleft + phi |- newright, scproof.length - 1)

          proof.ValidProofTactic(
            scproof,
            Seq(premise)
          )
        case ConnectorFormula(label, args) if label == Iff =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.schematicFormulaLabels).map(_.id)
          val H = VariableFormulaLabel(nFreshId(fv_in_phi, 1).head)
          lazy val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
          lazy val isolatedRight = originSequent.right.map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
          if ((!toLeft || isolatedLeft.forall(_._2.isEmpty)) && (!toRight || isolatedRight.forall(_._2.isEmpty)))
            if (rightLeft)
              return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyFormula(right)} to replace.")
            else
              applyLeftRight(Iff(right, left))(premise)(true, toLeft, toRight) match {
                case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyFormula(left)} to replace.")
                case v: proof.ValidProofTactic => return v
              }

          val leftForm = ConnectorFormula(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val rightForm = ConnectorFormula(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val newleft = if (toLeft) isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.left
          val newright = if (toRight) isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.right
          val result1: Sequent = (ConnectorFormula(And, newleft.toSeq), phi) |- rightOrigin
          val result2: Sequent = result1.left |- ConnectorFormula(Or, newright.toSeq)

          var scproof: Seq[SC.SCProofStep] = Seq(SC.Restate(leftOrigin |- rightOrigin, -1))
          if (toLeft) scproof = scproof :+ SC.LeftSubstIff(result1, scproof.length - 1, List(left -> right), LambdaFormulaFormula(Seq(H), leftForm))
          if (toRight) scproof = scproof :+ SC.RightSubstIff(result2, scproof.length - 1, List(left -> right), LambdaFormulaFormula(Seq(H), rightForm))
          scproof = scproof :+ SC.Restate(newleft + phi |- newright, scproof.length - 1)

          proof.ValidProofTactic(
            scproof,
            Seq(premise)
          )
        case _ => proof.InvalidProofTactic(s"Formula in applySingleSimp need to be of the form a=b or q<=>p and not ${phi.label}")
      }

    }

    @nowarn("msg=.*the type test for proof.Fact cannot be checked at runtime*")
    def apply(using
        lib: lisa.prooflib.Library,
        proof: lib.Proof,
        line: sourcecode.Line,
        file: sourcecode.File
    )(f: proof.Fact | Formula, rightLeft: Boolean = false, toLeft: Boolean = true, toRight: Boolean = true)(
        premise: proof.Fact
    ): proof.ProofTacticJudgement = {
      f match {
        case phi: Formula => applyLeftRight(phi)(premise)(rightLeft, toLeft, toRight)
        case f: proof.Fact =>
          val seq = proof.getSequent(f)
          val phi = seq.right.head
          val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
            val x = applyLeftRight(phi)(premise)(rightLeft, toLeft, toRight)
            proof.library.have(x)
            proof.library.andThen(SimpleDeducedSteps.Discharge(f))
          })

          BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof substitution fail.")
      }

    }

    def toLeft(using lib: lisa.prooflib.Library, proof: lib.Proof, line: sourcecode.Line, file: sourcecode.File)(f: proof.Fact | Formula, rightLeft: Boolean = false)(
        premise: proof.Fact
    ): proof.ProofTacticJudgement = apply(f, rightLeft, toLeft = true, toRight = false)(premise)

    def toRight(using lib: lisa.prooflib.Library, proof: lib.Proof, line: sourcecode.Line, file: sourcecode.File)(f: proof.Fact | Formula, rightLeft: Boolean = false)(
        premise: proof.Fact
    ): proof.ProofTacticJudgement = apply(f, rightLeft, toLeft = false, toRight = true)(premise)
  }
}
