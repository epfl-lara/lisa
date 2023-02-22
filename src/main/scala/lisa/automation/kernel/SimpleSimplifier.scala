package lisa.automation.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.prooflib.BasicStepTactic
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps
import lisa.utils.FOLPrinter
import lisa.utils.KernelHelpers.*
import lisa.utils.unification.UnificationUtils

import scala.annotation.nowarn
import scala.collection
import scala.collection.immutable.Seq

object SimpleSimplifier {

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

  object applySubst extends ProofTactic {
    def applyLeftRight(using lib: lisa.prooflib.Library, proof: lib.Proof)(phi: Formula)(premise: proof.Fact)(rightLeft: Boolean = false): proof.ProofTacticJudgement = {
      val originSequent = proof.getSequent(premise)
      val leftOrigin = ConnectorFormula(And, originSequent.left.toSeq)
      val rightOrigin = ConnectorFormula(Or, originSequent.right.toSeq)

      phi match {
        case PredicateFormula(label, args) if label == equality =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.freeVariables).map(_.id)
          val v = VariableLabel(nFreshId(fv_in_phi, 1).head)
          val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
          val isolatedRight = originSequent.right.map(f => (f, findSubterm(f, IndexedSeq(v -> left))))
          if (isolatedLeft.forall(_._2.isEmpty) && isolatedRight.forall(_._2.isEmpty)) {
            if (rightLeft)
              return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyTerm(left)} to replace.")
            else
              applyLeftRight(equality(right, left))(premise)(true) match {
                case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyTerm(left)} to replace.")
                case v: proof.ValidProofTactic => return v
              }
          }

          val leftForm = ConnectorFormula(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val rightForm = ConnectorFormula(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val newleft = isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right)))
          val newright = isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right)))
          val result1: Sequent = (ConnectorFormula(And, newleft.toSeq), phi) |- rightOrigin
          val result2: Sequent = result1.left |- ConnectorFormula(Or, newright.toSeq)

          val scproof = Seq(
            Restate(leftOrigin |- rightOrigin, -1),
            LeftSubstEq(result1, 0, List(left -> right), LambdaTermFormula(Seq(v), leftForm)),
            RightSubstEq(result2, 1, List(left -> right), LambdaTermFormula(Seq(v), rightForm)),
            Restate(newleft + phi |- newright, 2)
          )
          proof.ValidProofTactic(
            scproof,
            Seq(premise)
          )
        case ConnectorFormula(label, args) if label == Iff =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.schematicFormulaLabels).map(_.id)
          val H = VariableFormulaLabel(nFreshId(fv_in_phi, 1).head)
          val isolatedLeft = originSequent.left.filterNot(f => isSame(f, phi)).map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
          val isolatedRight = originSequent.right.map(f => (f, findSubformula(f, IndexedSeq(H -> left))))
          if (isolatedLeft.forall(_._2.isEmpty) && isolatedRight.forall(_._2.isEmpty))
            if (rightLeft)
              return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyFormula(right)} to replace.")
            else
              applyLeftRight(Iff(right, left))(premise)(true) match {
                case proof.InvalidProofTactic(m) => return proof.InvalidProofTactic(s"There is no instance of ${FOLPrinter.prettyFormula(left)} to replace.")
                case v: proof.ValidProofTactic => return v
              }

          val leftForm = ConnectorFormula(And, isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val rightForm = ConnectorFormula(Or, isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get.body).toSeq)
          val newleft = isolatedLeft.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right)))
          val newright = isolatedRight.map((f, ltf) => if (ltf.isEmpty) f else ltf.get(Seq(right)))
          val result1: Sequent = (ConnectorFormula(And, newleft.toSeq), phi) |- rightOrigin
          val result2: Sequent = result1.left |- ConnectorFormula(Or, newright.toSeq)

          val scproof = Seq(
            Restate(leftOrigin |- rightOrigin, -1),
            LeftSubstIff(result1, 0, List(left -> right), LambdaFormulaFormula(Seq(H), leftForm)),
            RightSubstIff(result2, 1, List(left -> right), LambdaFormulaFormula(Seq(H), rightForm)),
            Restate(newleft + phi |- newright, 2)
          )
          proof.ValidProofTactic(
            scproof,
            Seq(premise)
          )
        case _ => proof.InvalidProofTactic(s"Formula in applySingleSimp need to be of the form a=b or q<=>p and not ${phi.label}")
      }

    }

    @nowarn("msg=.*the type test for proof.Fact cannot be checked at runtime*")
    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof, line: sourcecode.Line, file: sourcecode.File)(f: proof.Fact | Formula, rightLeft: Boolean = false)(
        premise: proof.Fact
    ): proof.ProofTacticJudgement = {
      f match {
        case phi: Formula => applyLeftRight(phi)(premise)(rightLeft)
        case f: proof.Fact =>
          val seq = proof.getSequent(f)
          val phi = seq.right.head
          val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
            val x = applyLeftRight(phi)(premise)(rightLeft)
            proof.library.have(x)
            proof.library.andThen(SimpleDeducedSteps.Discharge(f))
          })

          BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof substitution fail.")
      }

    }

  }

  def simplifySeq(seq: Sequent, ruleseq: IndexedSeq[PredicateFormula], rulesiff: IndexedSeq[ConnectorFormula]): SCProof = {
    /*
        val takenVarsIff = (seq.left.flatMap(_.schematicPredicateLabels) ++ seq.right.flatMap(_.schematicPredicateLabels) ++ ruleseq.flatMap(_.schematicPredicateLabels) ++ rulesiff.flatMap(_.schematicPredicateLabels)).map(_.id)
        val varsIff = nFreshId(takenVarsIff, rulesiff.length).map(VariableFormulaLabel)
        val subsIff = varsIff.zip(rulesiff.map(_.args(0)))

        val substs: Set[(Formula, LambdaFormulaFormula)] = seq.left.map(f => (f, findSubformula(f, subsIff)) )
        val newseq = substs.map(_._2(rulesiff.map(_.args(1)))) |- seq.right
        val step1 = ??? // LeftSubstIff(newseq, prev.length-1, )
     */
    ???
  }

  def simplifySequent(seq: Sequent): SCProof = {
    val (ruleseq, rulesiff, rem): (List[PredicateFormula], List[ConnectorFormula], List[Formula]) =
      seq.left.foldLeft((List[PredicateFormula](), List[ConnectorFormula](), List[Formula]()))((prev, f) => {
        f match {
          case f @ PredicateFormula(label, _) if label == equality => (f :: prev._1, prev._2, prev._3)
          case f @ ConnectorFormula(label, _) if label == iff => (prev._1, f :: prev._2, prev._3)
          case _ => prev
        }
      })

    ???
  }

  object Substitution extends ProofTactic with ProofFactSequentTactic {
    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof, line: sourcecode.Line, file: sourcecode.File)(rightLeft: Boolean = false, f: lisa.prooflib.Library#Proof#InstantiatedFact | Formula)(
        premise: proof.Fact
    ): proof.ProofTacticJudgement = {
      f match {
        case phi: Formula => applySubst.applyLeftRight(phi)(premise)(rightLeft)
        case f: proof.Fact @unchecked =>
          val seq = proof.getSequent(f)
          val phi = seq.right.head
          val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
            val x = applySubst.applyLeftRight(phi)(premise)(rightLeft)
            proof.library.have(x)
            proof.library.andThen(SimpleDeducedSteps.Discharge(f))
          })
          BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof substitution fail.")
        case _ =>
          proof.InvalidProofTactic("the given fact is not valid in the current proof. (This should not compile, but a specific case of overload resolution needs to be fixed.")
      }

    }
    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      val premRight = ConnectorFormula(Or, premiseSequent.right.toSeq)
      val botRight = ConnectorFormula(Or, bot.right.toSeq)

      val equalities = bot.left.collect { case PredicateFormula(`equality`, Seq(l, r)) =>
        (l, r)
      }
      val canReach = UnificationUtils.canReachOneStepTermFormula(premRight, botRight, equalities.toList)

      if (canReach.isEmpty) {
        proof.InvalidProofTactic("Could not find a set of equalities to rewrite premise into conclusion successfully.")
      } else {
        BasicStepTactic.RightSubstEq(equalities.toList, canReach.get)(premise)(bot)
      }
    }

    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitution: proof.Fact | Formula | RunningTheory#Justification)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      val premRight = ConnectorFormula(Or, premiseSequent.right.toSeq)
      val botRight = ConnectorFormula(Or, bot.right.toSeq)

      val equalities = substitution match {
        case f: Formula =>
          bot.left.collect { case PredicateFormula(`equality`, Seq(l, r)) =>
            (l, r)
          }
        case j: RunningTheory#Justification =>
          proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.collect { case PredicateFormula(`equality`, Seq(l, r)) =>
            (l, r)
          }
        case f: proof.Fact @unchecked =>
          proof.sequentOfFact(f).right.collect { case PredicateFormula(`equality`, Seq(l, r)) =>
            (l, r)
          }
      }
      val iffs = substitution match {
        case f: Formula =>
          f match {
            case ConnectorFormula(Iff, Seq(l, r)) =>
              List((l, r))
            case _ => List()
          }
        case j: RunningTheory#Justification =>
          proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.collect { case ConnectorFormula(Iff, Seq(l, r)) =>
            (l, r)
          }
        case f: proof.Fact @unchecked =>
          proof.sequentOfFact(f).right.collect { case ConnectorFormula(Iff, Seq(l, r)) =>
            (l, r)
          }
      }

      val canReach = UnificationUtils.canReachOneStepTermFormula(premRight, botRight, equalities.toList)

      if (canReach.isEmpty || equalities.isEmpty) {
        val canReach2 = UnificationUtils.canReachOneStepOLFormula(premRight, botRight, iffs.toList)
        if (canReach2.isEmpty) {
          proof.InvalidProofTactic("Iffs and Equalities failed")
        } else {
          val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
            val actIffs = iffs.map((a, b) => Iff(a, b))
            val newBot = bot.copy(right = Set(ConnectorFormula(Or, bot.right.toSeq))) ++< (actIffs |- ())
            val s1 = proof.library.have(premiseSequent.left |- ConnectorFormula(Or, premiseSequent.right.toSeq)) by SimpleDeducedSteps.Restate.from(premise)
            val x = BasicStepTactic.RightSubstIff(iffs.toList, canReach2.get)(s1)(newBot)
            proof.library.have(x)
            proof.library.thenHave(bot) by SimpleDeducedSteps.Restate.from
            substitution match {
              case f: Formula => ()
              case j: RunningTheory#Justification => proof.library.andThen(SimpleDeducedSteps.Discharge(j.asInstanceOf[lib.theory.Justification]))
              case f: proof.Fact @unchecked => proof.library.andThen(SimpleDeducedSteps.Discharge(f))
            }
          })
          BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof substitution fail.")
        }
      } else {
        val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
          val x = BasicStepTactic.RightSubstEq(equalities.toList, canReach.get)(premise)(bot)
          proof.library.have(x)
          substitution match {
            case f: Formula => ()
            case j: RunningTheory#Justification => proof.library.andThen(SimpleDeducedSteps.Discharge(j.asInstanceOf[lib.theory.Justification]))
            case f: proof.Fact @unchecked => proof.library.andThen(SimpleDeducedSteps.Discharge(f))
          }
        })
        BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof substitution fail.")
      }
    }

    def apply2(using lib: lisa.prooflib.Library, proof: lib.Proof)(rightLeft: Boolean = false, substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(
        premise: proof.Fact
    )(bot: Sequent): proof.ProofTacticJudgement = {
      // takes a bot
      val premiseSequent = proof.getSequent(premise)

      val eqspre: List[(Term, Term)] = substitutions.flatMap {
        case f: Formula =>
          f match {
            case PredicateFormula(`equality`, Seq(l, r)) => List((l, r))
            case _ => List()
          }
        case f: proof.Fact @unchecked =>
          proof.sequentOfFact(f).right.collect { case PredicateFormula(`equality`, Seq(l, r)) =>
            (l, r)
          }
        case j: RunningTheory#Justification =>
          proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.collect { case PredicateFormula(`equality`, Seq(l, r)) =>
            (l, r)
          }
      }.toList

      val iffspre: List[(Formula, Formula)] = substitutions.flatMap {
        case f: Formula =>
          f match {
            case ConnectorFormula(Iff, Seq(l, r)) => List((l, r))
            case _ => List()
          }
        case f: proof.Fact @unchecked =>
          proof.sequentOfFact(f).right.collect { case ConnectorFormula(Iff, Seq(l, r)) =>
            (l, r)
          }
        case j: RunningTheory#Justification =>
          proof.sequentOfFact(j.asInstanceOf[lib.theory.Justification]).right.collect { case ConnectorFormula(Iff, Seq(l, r)) =>
            (l, r)
          }
      }.toList

      val eqs = if (rightLeft) eqspre.map(e => (e._2, e._1)) else eqspre
      val iffs = if (rightLeft) iffspre.map(i => (i._2, i._1)) else iffspre

      val filteredPrem = premiseSequent.left filter {
        case PredicateFormula(`equality`, Seq(l, r)) if eqs.contains((l, r)) => false
        case ConnectorFormula(Iff, Seq(l, r)) if iffs.contains((l, r)) => false
        case _ => true
      }

      val filteredBot = bot.left filter {
        case PredicateFormula(`equality`, Seq(l, r)) if eqs.contains((l, r)) => false
        case ConnectorFormula(Iff, Seq(l, r)) if iffs.contains((l, r)) => false
        case _ => true
      }

      lazy val rightPairs = premiseSequent.right zip premiseSequent.right.map(x => bot.right.find(y => UnificationUtils.canReachOneStep(x, y, iffs, eqs).isDefined))
      lazy val leftPairs = filteredPrem zip filteredPrem.map(x => filteredBot.find(y => UnificationUtils.canReachOneStep(x, y, iffs, eqs).isDefined))

      if (leftPairs.exists(_._2.isEmpty))
        proof.InvalidProofTactic("Could not rewrite LHS of premise into conclusion with given substitutions.")
      else if (rightPairs.exists(_._2.isEmpty))
        proof.InvalidProofTactic("Could not rewrite RHS of premise into conclusion with given substitutions.")
      else {
        // actually construct proof
        try {
          val leftLambdas = leftPairs.collect { case (l, Some(r)) => UnificationUtils.canReachOneStep(l, r, iffs, eqs).get }
          val rightLambdas = rightPairs.collect { case (l, Some(r)) => UnificationUtils.canReachOneStep(l, r, iffs, eqs).get }

          val eqsForm = eqs.map { case (l, r) => PredicateFormula(`equality`, Seq(l, r)) }.toSet
          val iffsForm = iffs.map { case (l, r) => ConnectorFormula(Iff, Seq(l, r)) }.toSet

          val leftEqs = eqs.map(_._1).toSeq
          val rightEqs = eqs.map(_._2).toSeq
          val leftIffs = iffs.map(_._1).toSeq
          val rightIffs = iffs.map(_._2).toSeq

          val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
            var premiseWithSubst = premiseSequent ++< (eqsForm |- ()) ++< (iffsForm |- ())
            proof.library.have(premiseWithSubst) by BasicStepTactic.Weakening(premise)

            if (!leftLambdas.isEmpty) {
              val leftEqLambdas = leftLambdas.map(f => lambda(f._2.toSeq, substituteFormulaVariables(f._3, ((f._1: Seq[VariableFormulaLabel]) zip iffs.map(_._1)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = leftEqLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda) => {
                  val newSequent = prevSequent -< nextLambda(leftEqs) +< nextLambda(rightEqs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.LeftSubstEq(eqs, nextLambda)

                  newSequent
                }
              }
            }
            if (!rightLambdas.isEmpty) {
              val rightEqLambdas = rightLambdas.map(f => lambda(f._2.toSeq, substituteFormulaVariables(f._3, ((f._1: Seq[VariableFormulaLabel]) zip iffs.map(_._1)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = rightEqLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda: LambdaTermFormula) => {
                  val newSequent = prevSequent ->> nextLambda(leftEqs) +> nextLambda(rightEqs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.RightSubstEq(eqs, nextLambda)

                  newSequent
                }
              }
            }

            if (!leftLambdas.isEmpty) {
              val leftIffLambdas = leftLambdas.map(f => lambda(f._1.toSeq, substituteVariables(f._3, ((f._2: Seq[VariableLabel]) zip eqs.map(_._2)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = leftIffLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda) => {
                  val newSequent = prevSequent -< nextLambda(leftIffs) +< nextLambda(rightIffs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.LeftSubstIff(iffs, nextLambda)

                  newSequent
                }
              }
            }
            if (!rightLambdas.isEmpty) {
              val rightIffLambdas = rightLambdas.map(f => lambda(f._1.toSeq, substituteVariables(f._3, ((f._2: Seq[VariableLabel]) zip eqs.map(_._2)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = rightIffLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda) => {
                  val newSequent = prevSequent ->> nextLambda(leftIffs) +> nextLambda(rightIffs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.RightSubstIff(iffs, nextLambda)

                  newSequent
                }
              }
            }

            substitutions.foreach {
              case f: Formula => ()
              case f: proof.Fact @unchecked => (proof.library.andThen(SimpleDeducedSteps.Discharge(f)))
              case j: RunningTheory#Justification => proof.library.andThen(SimpleDeducedSteps.Discharge(j.asInstanceOf[lib.theory.Justification]))
            }

            proof.library.thenHave(bot) by SimpleDeducedSteps.Restate

          })

          BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof for Substitution failed.")
        } catch case _ => proof.InvalidProofTactic("Could not rewrite given conlusion sequent into substituted premise. You may have a typo.")

      }

    }

    // def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = apply(lib, proof)(false, substitutions)(premise)(bot)

    // def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(rightLeft: Boolean = false, substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact): proof.ProofTacticJudgement = {
    //   // takes no bot
    //   ???
    // }

    // def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = apply(lib, proof)(false, substitutions)(premise)

  }

}
