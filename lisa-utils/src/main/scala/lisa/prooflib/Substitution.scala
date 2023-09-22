package lisa.prooflib
import lisa.fol.FOL as F
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.utils.FOLPrinter
import lisa.utils.K
import lisa.utils.UserLisaException
import lisa.utils.parsing.FOLPrinter
import lisa.utils.unification.UnificationUtils
import lisa.utils.unification.UnificationUtils.getContextFormulaSet

import scala.annotation.nowarn
import scala.collection.mutable.{Map as MMap}

import F.{*, given}
import F.|-

object Substitution {
  def validRule(using lib: lisa.prooflib.Library, proof: lib.Proof)(r: (proof.Fact | F.Formula | lib.JUSTIFICATION)): Boolean =
    r match {
      case F.equality(_) => true
      case F.Iff(_) => true
      case j: lib.JUSTIFICATION => j.statement.right.size == 1 && validRule(j.statement.right.head)
      case f: proof.Fact @unchecked => proof.sequentOfFact(f).right.size == 1 && validRule(proof.sequentOfFact(f).right.head)
      // case j: RunningTheory#Justification =>
      //  proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.size == 1 && validRule(proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.head)
      case _ => false
    }

  object ApplyRules extends ProofTactic {

    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | F.Formula | lib.JUSTIFICATION)*)(
        premise: proof.Fact
    )(bot: F.Sequent): proof.ProofTacticJudgement = {
      // lazy val substitutionsK = substitutions.map()

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
        val takenTermVars: Set[lisa.fol.FOL.Variable] =
          premiseSequent.left.flatMap(_.freeVariables).toSet union substitutions.collect { case f: F.Formula => f.freeVariables.toSet }.foldLeft(Set.empty)(_.union(_))
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
        lazy val leftContextsOpt: Option[Seq[UnificationUtils.FormulaRewriteLambda]] = getContextFormulaSet(
          filteredPrem,
          filteredBot,
          freeEqualities,
          freeIffs,
          confinedEqualities,
          takenTermVars,
          confinedIffs,
          takenFormulaVars
        )

        lazy val rightContextsOpt: Option[Seq[UnificationUtils.FormulaRewriteLambda]] = getContextFormulaSet(
          premiseSequent.right.toSeq,
          bot.right.toSeq,
          freeEqualities,
          freeIffs,
          confinedEqualities,
          takenTermVars,
          confinedIffs,
          takenFormulaVars
        )

        lazy val violatingFormulaLeft: Option[Formula] = Some(top) // TODO
        lazy val violatingFormulaRight: Option[Formula] = Some(top) // TODO

        if (leftContextsOpt.isEmpty)
          proof.InvalidProofTactic(s"Could not rewrite LHS of premise into conclusion with given substitutions.\nViolating Formula: ${violatingFormulaLeft.get}")
        else if (rightContextsOpt.isEmpty)
          proof.InvalidProofTactic(s"Could not rewrite RHS of premise into conclusion with given substitutions.\nViolating Formula: ${violatingFormulaRight.get}")
        else {
          // actually construct proof
          TacticSubproof {

            def eq(rule: (Term, Term)) = PredicateFormula(equality, Seq(rule._1, rule._2))
            def iff(rule: (Formula, Formula)) = ConnectorFormula(Iff, Seq(rule._1, rule._2))

            def eqSource(rule: (Term, Term)) = lib.have(eq(rule) |- eq(rule)) by SimpleDeducedSteps.Restate
            def iffSource(rule: (Formula, Formula)) = lib.have(iff(rule) |- iff(rule)) by SimpleDeducedSteps.Restate
            val leftContexts: Seq[UnificationUtils.FormulaRewriteLambda] = leftContextsOpt.get // remove the options
            val rightContexts: Seq[UnificationUtils.FormulaRewriteLambda] = rightContextsOpt.get // remove the options

            val leftBody = ConnectorFormula(And, leftContexts.map(f => f.body))

            val defaultLeft = UnificationUtils.FormulaRewriteLambda(body = leftBody)

            val leftContextReduced = leftContexts.foldLeft(defaultLeft) { (f, s) =>
              UnificationUtils.FormulaRewriteLambda(
                termRules = f.termRules ++ s.termRules,
                formulaRules = f.formulaRules ++ s.formulaRules,
                leftBody
              )
            }

            val rightBody = ConnectorFormula(Or, rightContexts.map(f => f.body))

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
                    f.of(subst.toSeq.map((l, r) => (l := r)): _*)
                  // case Some(j: lib.theory.Justification) =>
                  //   j.of(subst.toSeq.map((l, r) => (l, lambda(Seq(), r))): _*)
                  case _ =>
                    eqSource(rule).of()
                }
              } ++
                leftContextReduced.formulaRules.map { case (_, (rule, subst)) =>
                  sourceOf.get(rule) match {
                    case Some(f: proof.Fact) =>
                      f.of(subst._1.toSeq.map((l, r) => (l := r)) ++ subst._2.toSeq.map((l, r) => (l := r)): _*)
                    // case Some(j: lib.theory.Justification) =>
                    //   j.of(subst._1.toSeq.map((l, r) => (l, lambda(Seq[Variable](), r))) ++ subst._2.toSeq.map((l, r) => (l, lambda(Seq[Variable](), r))): _*)
                    case _ =>
                      iffSource(rule).of()
                  }
                }
            val rightDischarges =
              rightContextReduced.termRules.map { case (_, (rule, subst)) =>
                sourceOf.get(rule) match {
                  case Some(f: proof.Fact) =>
                    f.of(subst.toSeq.map((l, r) => (l := r)): _*)
                  // case Some(j: lib.theory.Justification) =>
                  //   j.of(subst.toSeq.map((l, r) => (l, lambda(Seq(), r))): _*)
                  case None =>
                    eqSource(rule).of()
                }
              } ++
                rightContextReduced.formulaRules.map { case (_, (rule, subst)) =>
                  sourceOf.get(rule) match {
                    case Some(f: proof.Fact) =>
                      f.of(subst._1.toSeq.map((l, r) => (l := r)) ++ subst._2.toSeq.map((l, r) => (l := r)): _*)
                    // case Some(j: lib.theory.Justification) =>
                    //   j.of(subst._1.toSeq.map((l, r) => (l, lambda(Seq[Variable](), r))) ++ subst._2.toSeq.map((l, r) => (l, lambda(Seq[Variable](), r))): _*)
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

              val termInputs = ctx.termRules.map { case (_, (rule: (Term, Term), subst: UnificationUtils.TermSubstitution)) =>
                (
                  rule._1.substituteUnsafe2(subst),
                  rule._2.substituteUnsafe2(subst)
                )
              }

              lazy val (termInputsL, termInputsR) = (termInputs.map(_._1), termInputs.map(_._2))

              val formulaVars = ctx.formulaRules.map(_._1)

              val formulaInputs = ctx.formulaRules.map { case (_, (rule, subst)) =>
                (
                  rule._1.substituteUnsafe2(subst._2).substituteUnsafe2(subst._1),
                  rule._2.substituteUnsafe2(subst._2).substituteUnsafe2(subst._1)
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
              val eqSubst = Map((termVars zip termInputsR)*)
              val formSubstL = Map((formulaVars zip formulaInputsL)*)
              val lhsAfterEq = ctx.body.substituteUnsafe2(eqSubst).substituteUnsafe2(formSubstL)
              val sequentAfterEqPre = lhsAfterEq |- premiseWithSubst.right
              val sequentAfterEq = sequentAfterEqPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (p = left formulas)
              lib.thenHave(sequentAfterEq) by BasicStepTactic.LeftSubstEq.withParameters(termInputs.toList, lambda(termVars, ctx.body.substituteUnsafe2(formSubstL)))

              // left <=>
              val formSubstR = Map((formulaVars zip formulaInputsR)*)
              val lhsAfterIff = ctx.body.substituteUnsafe2(eqSubst).substituteUnsafe2(formSubstR)
              val sequentAfterIffPre = lhsAfterIff |- sequentAfterEq.right
              val sequentAfterIff = sequentAfterIffPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (x = right terms)
              lib.thenHave(sequentAfterIff) by BasicStepTactic.LeftSubstIff(formulaInputs.toList, lambda(formulaVars, ctx.body.substituteUnsafe2(eqSubst)))
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
                  rule._1.substituteUnsafe2(subst),
                  rule._2.substituteUnsafe2(subst)
                )
              }

              lazy val (termInputsL, termInputsR) = (termInputs.map(_._1), termInputs.map(_._2))

              val formulaVars = ctx.formulaRules.map(_._1)

              val formulaInputs = ctx.formulaRules.map { case (_, (rule, subst)) =>
                (
                  rule._1.substituteUnsafe2(subst._2).substituteUnsafe2(subst._1),
                  rule._2.substituteUnsafe2(subst._2).substituteUnsafe2(subst._1)
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
              val eqSubst = Map((termVars zip termInputsR)*)
              val formSubstL = Map((formulaVars zip formulaInputsL)*)
              val rhsAfterEq = ctx.body.substituteUnsafe2(eqSubst).substituteUnsafe2(formSubstL)
              val sequentAfterEqPre = premiseWithSubst.left |- rhsAfterEq
              val sequentAfterEq = sequentAfterEqPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (p = left formulas)
              lib.thenHave(sequentAfterEq) by BasicStepTactic.RightSubstEq.withParameters(termInputs.toList, lambda(termVars, ctx.body.substituteUnsafe2(formSubstL)))

              // right <=>
              val formSubstR = Map((formulaVars zip formulaInputsR)*)
              val rhsAfterIff = ctx.body.substituteUnsafe2(eqSubst).substituteUnsafe2(formSubstR)
              val sequentAfterIffPre = sequentAfterEq.left |- rhsAfterIff
              val sequentAfterIff = sequentAfterIffPre ++<< (eqs |- ()) ++<< (iffs |- ())

              // this uses the "lambda" (λx. Λp. body) (x = right terms)
              lib.thenHave(sequentAfterIff) by BasicStepTactic.RightSubstIff(formulaInputs.toList, lambda(formulaVars, ctx.body.substituteUnsafe2(eqSubst)))

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

    private def findSubterm2(t: Term, subs: Seq[(Variable, Term)]): (Term, Boolean) = {
      val eq = subs.find(s => isSameTerm(t, s._2))
      if (eq.nonEmpty) (eq.get._1, true)
      else {
        val induct = condflat(t.args.map(te => findSubterm2(te, subs)))
        if (!induct._2) (t, false)
        else (t.label(induct._1), true)

      }

    }
    private def findSubterm2(f: Formula, subs: Seq[(Variable, Term)]): (Formula, Boolean) = {
      f match {
        case f: VariableFormula => (f, false)
        case f: ConstantFormula => (f, false)
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
            val newv = Variable(freshId((f.freeVariables ++ fv_in_f).map(_.id), bound.id))
            val newInner = inner.substitute(bound := newv)
            val induct = findSubterm2(newInner, subs)
            if (!induct._2) (f, false)
            else (BinderFormula(label, newv, induct._1), true)
          }
      }
    }

    private def findSubformula2(f: Formula, subs: Seq[(VariableFormula, Formula)]): (Formula, Boolean) = {
      val eq = subs.find(s => isSame(f, s._2))
      if (eq.nonEmpty) (eq.get._1, true)
      else
        f match {
          case f: AtomicFormula => (f, false)
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
              val newv = Variable(freshId((f.freeVariables ++ fv_in_f).map(_.id), bound.id))
              val newInner = inner.substitute(bound := newv)
              val induct = findSubformula2(newInner, subs)
              if (!induct._2) (f, false)
              else (BinderFormula(label, newv, induct._1), true)
            }
        }
    }

    def findSubterm(t: Term, subs: Seq[(Variable, Term)]): Option[LambdaExpression[Term, Term, ?]] = {
      val vars = subs.map(_._1)
      val r = findSubterm2(t, subs)
      if (r._2) Some(LambdaExpression(vars, r._1, vars.size))
      else None
    }

    def findSubterm(f: Formula, subs: Seq[(Variable, Term)]): Option[LambdaExpression[Term, Formula, ?]] = {
      val vars = subs.map(_._1)
      val r = findSubterm2(f, subs)
      if (r._2) Some(LambdaExpression(vars, r._1, vars.size))
      else None
    }

    def findSubformula(f: Formula, subs: Seq[(VariableFormula, Formula)]): Option[LambdaExpression[Formula, Formula, ?]] = {
      val vars = subs.map(_._1)
      val r = findSubformula2(f, subs)
      if (r._2) Some(LambdaExpression(vars, r._1, vars.size))
      else None
    }

    def applyLeftRight(using lib: lisa.prooflib.Library, proof: lib.Proof)(
        phi: Formula
    )(premise: proof.Fact)(rightLeft: Boolean = false, toLeft: Boolean = true, toRight: Boolean = true): proof.ProofTacticJudgement = {
      import lisa.utils.K
      val originSequent = proof.getSequent(premise)
      val leftOrigin = ConnectorFormula(And, originSequent.left.toSeq)
      val rightOrigin = ConnectorFormula(Or, originSequent.right.toSeq)

      if (!toLeft && !toRight) return proof.InvalidProofTactic("applyLeftRight called with no substitution selected (toLeft or toRight).")

      phi match {
        case PredicateFormula(label, args) if label == equality =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.allSchematicLabels).map(_.id)
          val v = Variable(nFreshId(fv_in_phi, 1).head)
          lazy val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
          lazy val isolatedRight = originSequent.right.map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
          if ((!toLeft || isolatedLeft.forall(_._2.isEmpty)) && (!toRight || isolatedRight.forall(_._2.isEmpty)))
            if (rightLeft)
              return proof.InvalidProofTactic(s"There is no instance of ${right} to replace.")
            else
              applyLeftRight(equality(right, left))(premise)(true, toLeft, toRight) match {
                case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${left} to replace.")
                case v: proof.ValidProofTactic => return v
              }

          val leftForm = ConnectorFormula(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val rightForm = ConnectorFormula(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val newleft = if (toLeft) isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.left
          val newright = if (toRight) isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.right
          val result1: Sequent = (ConnectorFormula(And, newleft.toSeq), phi) |- rightOrigin
          val result2: Sequent = result1.left |- ConnectorFormula(Or, newright.toSeq)
          var scproof: Seq[K.SCProofStep] = Seq(K.Restate((leftOrigin |- rightOrigin).underlying, -1))
          if (toLeft)
            scproof = scproof :+ K.LeftSubstEq(result1.underlying, scproof.length - 1, List(left.underlying -> right.underlying), K.LambdaTermFormula(Seq(v.underlyingLabel), leftForm.underlying))
          if (toRight)
            scproof = scproof :+ K.RightSubstEq(result2.underlying, scproof.length - 1, List(left.underlying -> right.underlying), K.LambdaTermFormula(Seq(v.underlyingLabel), rightForm.underlying))
          val bot = newleft + phi |- newright
          scproof = scproof :+ K.Restate(bot.underlying, scproof.length - 1)

          proof.ValidProofTactic(
            bot,
            scproof,
            Seq(premise)
          )

        case ConnectorFormula(label, args) if label == Iff =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.allSchematicLabels).map(_.id)
          val H = VariableFormula(nFreshId(fv_in_phi, 1).head)
          lazy val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
          lazy val isolatedRight = originSequent.right.map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
          if ((!toLeft || isolatedLeft.forall(_._2.isEmpty)) && (!toRight || isolatedRight.forall(_._2.isEmpty)))
            if (rightLeft)
              return proof.InvalidProofTactic(s"There is no instance of ${right} to replace.")
            else
              applyLeftRight(Iff(right, left))(premise)(true, toLeft, toRight) match {
                case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${left} to replace.")
                case v: proof.ValidProofTactic => return v
              }

          val leftForm = ConnectorFormula(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val rightForm = ConnectorFormula(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val newleft = if (toLeft) isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.left
          val newright = if (toRight) isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right))) else originSequent.right
          val result1: Sequent = (ConnectorFormula(And, newleft.toSeq), phi) |- rightOrigin
          val result2: Sequent = result1.left |- ConnectorFormula(Or, newright.toSeq)

          var scproof: Seq[K.SCProofStep] = Seq(K.Restate((leftOrigin |- rightOrigin).underlying, -1))
          if (toLeft)
            scproof = scproof :+ K.LeftSubstIff(result1.underlying, scproof.length - 1, List(left.underlying -> right.underlying), K.LambdaFormulaFormula(Seq(H.underlyingLabel), leftForm.underlying))
          if (toRight)
            scproof =
              scproof :+ K.RightSubstIff(result2.underlying, scproof.length - 1, List(left.underlying -> right.underlying), K.LambdaFormulaFormula(Seq(H.underlyingLabel), rightForm.underlying))

          val bot = newleft + phi |- newright
          scproof = scproof :+ K.Restate(bot.underlying, scproof.length - 1)

          proof.ValidProofTactic(
            bot,
            scproof,
            Seq(premise)
          )
        case _ => proof.InvalidProofTactic(s"Formula in applySingleSimp need to be of the form a=b or q<=>p and not ${phi}")
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
