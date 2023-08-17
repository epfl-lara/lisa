package lisa.prooflib

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps
import lisa.utils.FOLPrinter
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.unification.UnificationUtils
import lisa.utils.unification.UnificationUtils2
import lisa.utils.unification.UnificationUtils2.getContextFormulaSet

import scala.collection.mutable.{Map as MMap}

object EqualityReasoning {
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
        val takenTermVars = proof.getAssumptions.flatMap(_.freeVariables).toSet
        val takenFormulaVars = proof.getAssumptions.flatMap(_.freeVariableFormulaLabels).toSet // TODO: should this just be the LHS of the premise sequent instead?

        var freeEqualitiesPre = List[(Term, Term)]()
        var confinedEqualitiesPre = List[(Term, Term)]()
        var freeIffsPre = List[(Formula, Formula)]()
        var confinedIffsPre = List[(Formula, Formula)]()

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
          case f: proof.Fact @unchecked =>
            proof.sequentOfFact(f).right.head match {
              case PredicateFormula(`equality`, Seq(l, r)) =>
                sourceOf.update((l, r), f)
                confinedEqualitiesPre = (l, r) :: confinedEqualitiesPre
              case ConnectorFormula(Iff, Seq(l, r)) =>
                sourceOf.update((l, r), f)
                confinedIffsPre = (l, r) :: confinedIffsPre
              case _ => ()
            }
          case j: RunningTheory#Justification =>
            proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.head match {
              case PredicateFormula(`equality`, Seq(l, r)) =>
                sourceOf.update((l, r), j.asInstanceOf[lib.theory.Justification])
                freeEqualitiesPre = (l, r) :: freeEqualitiesPre
              case ConnectorFormula(Iff, Seq(l, r)) =>
                sourceOf.update((l, r), j.asInstanceOf[lib.theory.Justification])
                freeIffsPre = (l, r) :: freeIffsPre
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

        lazy val violatingFormulaLeft: Option[Formula] = ???
        lazy val violatingFormulaRight: Option[Formula] = ???

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

            val leftContextReduced = leftContexts.reduce { (f, s) =>
              UnificationUtils2.FormulaRewriteLambda(
                termRules = f.termRules ++ s.termRules,
                formulaRules = f.formulaRules ++ s.formulaRules,
                leftBody
              )
            }

            val rightBody = ConnectorFormula(Or, rightContexts.map(_.body))

            val rightContextReduced = leftContexts.reduce { (f, s) =>
              UnificationUtils2.FormulaRewriteLambda(
                termRules = f.termRules ++ s.termRules,
                formulaRules = f.formulaRules ++ s.formulaRules,
                leftBody
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
              val prem = ConnectorFormula(And, premiseSequent.left.toSeq) |- ConnectorFormula(Or, premiseSequent.right.toSeq)
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
              val sequentAfterIffPre = lhsAfterIff |- premiseWithSubst.right
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
              val sequentAfterIffPre = premiseWithSubst.left |- rhsAfterIff
              val sequentAfterIff = sequentAfterIffPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (x = right terms)
              lib.thenHave(sequentAfterEq) by BasicStepTactic.RightSubstIff(formulaInputs.toList, lambda(formulaVars, substituteVariables(ctx.body, eqSubst)))
            }

            // discharge any assumptions
            discharges.foreach { f => proof.library.andThen(SimpleDeducedSteps.Discharge(f)) }

            // finally, make sure our substitutions and discharges led us to the required conclusion
            lib.thenHave(bot) by BasicStepTactic.Weakening
          }
        }
      }
    }
  }
}
