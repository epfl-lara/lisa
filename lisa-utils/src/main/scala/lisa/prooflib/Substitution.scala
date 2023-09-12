package lisa.prooflib

import lisa.fol.FOL as F
import lisa.fol.FOLHelpers.*
import lisa.utils.K
//import lisa.utils.KernelHelpers.{_, given}

import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.*
import lisa.prooflib.BasicStepTactic.*
import lisa.utils.FOLPrinter

import lisa.utils.KernelHelpers.{|- => `K|-`, *}
import lisa.utils.UserLisaException
import lisa.utils.parsing.FOLPrinter
import lisa.utils.unification.FirstOrderUnifier
import lisa.utils.unification.UnificationUtils
import lisa.utils.unification.UnificationUtils.getContextFormulaSet
import lisa.utils.unification.UnificationUtils2

import scala.collection.mutable.{Map as MMap}

object Substitution {
  /*
  def validRule(using lib: lisa.prooflib.Library, proof: lib.Proof)(r: (proof.Fact | F.Formula | lib.JUSTIFICATION)): Boolean =
    r match {
      case F.PredicateFormula(F.equality, _) => true
      case F.ConnectorFormula(F.Iff, _) => true
      case f: proof.Fact @unchecked => proof.sequentOfFact(f).right.size == 1 && validRule(proof.sequentOfFact(f).right.head)
      case j: lib.JUSTIFICATION => j.statement.right.size == 1 && validRule(j.statement.right.head)
      //case j: K.RunningTheory#Justification =>
      //  proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.size == 1 && validRule(proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.head)
      case _ => false
    }

  object ApplyRules extends ProofTactic {
    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | F.Formula | lib.JUSTIFICATION)*)(
        premise: proof.Fact
    )(bot: F.Sequent): proof.ProofTacticJudgement = {
      //lazy val substitutionsK = substitutions.map()


      // figure out instantiations for rules
      // takes a premise
      val premiseSequent: F.Sequent = proof.getSequent(premise)

      // make sure substitutions are all valid
      val violatingSubstitutions = substitutions.collect {
        case f: proof.Fact if !validRule(f) => proof.sequentOfFact(f)
        case j: lib.JUSTIFICATION if !validRule(j) => j.statement
      }

      val violatingFormulas = substitutions.collect {
        case f: F.Formula if !validRule(f) => f
      }

      if (!violatingSubstitutions.isEmpty)
        // return error
        proof.InvalidProofTactic("Substitution rules must have a single equality or equivalence on the right-hand side. Violating sequents passed:\n" + violatingSubstitutions.zipWithIndex.map {
          (s, i) =>
            s"${i + 1}. ${s.toString}"
        })
      else if (!violatingFormulas.isEmpty)
        proof.InvalidProofTactic("Substitution rules must be equalities or equivalences. Violating formulas passed:\n" + violatingFormulas.zipWithIndex.map { (s, i) =>
          s"${i + 1}. ${s.toString}"
        })
      else {
        // proceed as usual

        
        // maintain a list of where subtitutions come from
        val sourceOf: MMap[(F.Formula, F.Formula) | (F.Term, F.Term), proof.Fact] = MMap()
        val takenTermVars: Set[lisa.fol.FOL.Variable] = premiseSequent.left.flatMap(_.freeVariables).toSet union substitutions.collect { case f: F.Formula => f.freeVariables.toSet}.foldLeft(Set.empty)(_.union(_))
        val takenFormulaVars: Set[lisa.fol.FOL.VariableFormula] = premiseSequent.left.flatMap(_.freeVariableFormulas).toSet union substitutions
          .collect { case f: F.Formula => f.freeVariableFormulas.toSet }
          .foldLeft(Set.empty)(_.union(_)) // TODO: should this just be the LHS of the premise sequent instead?

        var freeEqualitiesPre = List[(F.Term, F.Term)]()
        var confinedEqualitiesPre = List[(F.Term, F.Term)]()
        var freeIffsPre = List[(F.Formula, F.Formula)]()
        var confinedIffsPre = List[(F.Formula, F.Formula)]()

        def updateSource(t: (F.Formula, F.Formula) | (F.Term, F.Term), f: proof.Fact) = {
          sourceOf.update(t, f)
          sourceOf.update(t.swap.asInstanceOf[(F.Formula, F.Formula) | (F.Term, F.Term)], f)
        }

        // collect substitutions into the right buckets
        substitutions.foreach {
          case f: F.Formula =>
            f match {
              case F.PredicateFormula(F.equality, Seq(l, r)) =>
                confinedEqualitiesPre = (l, r) :: confinedEqualitiesPre
              case F.ConnectorFormula(F.Iff, Seq(l, r)) =>
                confinedIffsPre = (l, r) :: confinedIffsPre
              case _ => ()
            }
          case j: lib.JUSTIFICATION =>
            j.statement.right.head match {
              case F.PredicateFormula(F.equality, Seq(l, r)) =>
                updateSource((l, r), j)
                freeEqualitiesPre = (l, r) :: freeEqualitiesPre
              case F.ConnectorFormula(F.Iff, Seq(l, r)) =>
                updateSource((l, r), j)
                freeIffsPre = (l, r) :: freeIffsPre
              case _ => ()
            }
          case f: proof.Fact @unchecked =>
            proof.sequentOfFact(f).right.head match {
              case F.PredicateFormula(F.equality, Seq(l, r)) =>
                updateSource((l, r), f)
                confinedEqualitiesPre = (l, r) :: confinedEqualitiesPre
              case F.ConnectorFormula(F.Iff, Seq(l, r)) =>
                updateSource((l, r), f)
                confinedIffsPre = (l, r) :: confinedIffsPre
              case _ => ()
            }
        }

        // get the original and swapped versions
        val freeEqualities: List[(F.Term, F.Term)] = freeEqualitiesPre ++ freeEqualitiesPre.map(_.swap)
        val confinedEqualities: List[(F.Term, F.Term)] = confinedEqualitiesPre ++ confinedEqualitiesPre.map(_.swap)
        val freeIffs: List[(F.Formula, F.Formula)] = freeIffsPre ++ freeIffsPre.map(_.swap)
        val confinedIffs: List[(F.Formula, F.Formula)] = confinedIffsPre ++ confinedIffsPre.map(_.swap)

        val filteredPrem: Seq[F.Formula] = (premiseSequent.left filter {
          case F.PredicateFormula(F.equality, Seq(l, r)) if freeEqualities.contains((l, r)) || confinedEqualities.contains((l, r)) => false
          case F.ConnectorFormula(F.Iff, Seq(l, r)) if freeIffs.contains((l, r)) || confinedIffs.contains((l, r)) => false
          case _ => true
        }).toSeq

        val filteredBot: Seq[F.Formula] = (bot.left filter {
          case F.PredicateFormula(F.equality, Seq(l, r)) if freeEqualities.contains((l, r)) || confinedEqualities.contains((l, r)) => false
          case F.ConnectorFormula(F.Iff, Seq(l, r)) if freeIffs.contains((l, r)) || confinedIffs.contains((l, r)) => false
          case _ => true
        }).toSeq

        // construct the right instantiations
        lazy val leftContextsOpt = getContextFormulaSet(  // Option[Seq[lisa.utils.unification.UnificationUtils.FormulaRewriteLambda]]
          filteredPrem.map(_.underlying),
          filteredBot.map(_.underlying),
          freeEqualities.map(p => (p._1.underlying, p._2.underlying)),
          freeIffs.map(p => (p._1.underlying, p._2.underlying)),
          confinedEqualities.map(p => (p._1.underlying, p._2.underlying)),
          takenTermVars.map(_.underlyingLabel),
          confinedIffs.map(p => (p._1.underlying, p._2.underlying)),
          takenFormulaVars.map(_.underlyingLabel)
        )
        lazy val rightContextsOpt = getContextFormulaSet(  // Option[Seq[lisa.utils.unification.UnificationUtils.FormulaRewriteLambda]]
          premiseSequent.right.toSeq.map(_.underlying),
          bot.right.toSeq.map(_.underlying),
          freeEqualities.map(p => (p._1.underlying, p._2.underlying)),
          freeIffs.map(p => (p._1.underlying, p._2.underlying)),
          confinedEqualities.map(p => (p._1.underlying, p._2.underlying)),
          takenTermVars.map(_.underlyingLabel),
          confinedIffs.map(p => (p._1.underlying, p._2.underlying)),
          takenFormulaVars.map(_.underlyingLabel)
        )

        lazy val violatingFormulaLeft: Option[K.Formula] = Some(K.top()) //TODO
        lazy val violatingFormulaRight: Option[K.Formula] = Some(K.top())  //TODO

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
                  K.substituteVariablesInTerm(rule._1, subst),
                  K.substituteVariablesInTerm(rule._2, subst)
                )
              }

              lazy val (termInputsL, termInputsR) = (termInputs.map(_._1), termInputs.map(_._2))

              val formulaVars = ctx.formulaRules.map(_._1)

              val formulaInputs = ctx.formulaRules.map { case (_, (rule, subst)) =>
                (
                  substituteFormulaVariables(K.substituteVariablesInTerm(rule._1, subst._2), subst._1),
                  substituteFormulaVariables(K.substituteVariablesInTerm(rule._2, subst._2), subst._1)
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
              val lhsAfterEq = substituteFormulaVariables(K.substituteVariablesInTerm(ctx.body, eqSubst), formSubstL)
              val sequentAfterEqPre = lhsAfterEq |- premiseWithSubst.right
              val sequentAfterEq = sequentAfterEqPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (p = left formulas)
              lib.thenHave(sequentAfterEq) by BasicStepTactic.LeftSubstEq(termInputs.toList, lambda(termVars, substituteFormulaVariables(ctx.body, formSubstL)))

              // left <=>
              val formSubstR = (formulaVars zip formulaInputsR).toMap
              val lhsAfterIff = substituteFormulaVariables(K.substituteVariablesInTerm(ctx.body, eqSubst), formSubstR)
              val sequentAfterIffPre = lhsAfterIff |- sequentAfterEq.right
              val sequentAfterIff = sequentAfterIffPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (x = right terms)
              lib.thenHave(sequentAfterIff) by BasicStepTactic.LeftSubstIff(formulaInputs.toList, lambda(formulaVars, K.substituteVariablesInTerm(ctx.body, eqSubst)))
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
                  K.substituteVariablesInTerm(rule._1, subst),
                  K.substituteVariablesInTerm(rule._2, subst)
                )
              }

              lazy val (termInputsL, termInputsR) = (termInputs.map(_._1), termInputs.map(_._2))

              val formulaVars = ctx.formulaRules.map(_._1)

              val formulaInputs = ctx.formulaRules.map { case (_, (rule, subst)) =>
                (
                  substituteFormulaVariables(K.substituteVariablesInTerm(rule._1, subst._2), subst._1),
                  substituteFormulaVariables(K.substituteVariablesInTerm(rule._2, subst._2), subst._1)
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
              val rhsAfterEq = substituteFormulaVariables(K.substituteVariablesInTerm(ctx.body, eqSubst), formSubstL)
              val sequentAfterEqPre = premiseWithSubst.left |- rhsAfterEq
              val sequentAfterEq = sequentAfterEqPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (p = left formulas)
              lib.thenHave(sequentAfterEq) by BasicStepTactic.RightSubstEq(termInputs.toList, lambda(termVars, substituteFormulaVariables(ctx.body, formSubstL)))

              // right <=>
              val formSubstR = (formulaVars zip formulaInputsR).toMap
              val rhsAfterIff = substituteFormulaVariables(K.substituteVariablesInTerm(ctx.body, eqSubst), formSubstR)
              val sequentAfterIffPre = sequentAfterEq.left |- rhsAfterIff
              val sequentAfterIff = sequentAfterIffPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (x = right terms)
              lib.thenHave(sequentAfterIff) by BasicStepTactic.RightSubstIff(formulaInputs.toList, lambda(formulaVars, K.substituteVariablesInTerm(ctx.body, eqSubst)))
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
  */
}
