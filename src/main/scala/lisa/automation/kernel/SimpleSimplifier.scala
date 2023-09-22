package lisa.automation.kernel

import lisa.fol.FOL.*
import lisa.prooflib.BasicStepTactic
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps
import lisa.utils.FOLPrinter
import lisa.utils.K
import lisa.utils.unification.UnificationUtils

import scala.annotation.nowarn
import scala.annotation.tailrec
import scala.collection
import scala.collection.immutable.Seq

object SimpleSimplifier {
  /*
  private def condflat[T](s: Seq[(T, Boolean)]): (Seq[T], Boolean) = (s.map(_._1), s.exists(_._2))

  private def findSubterm2(t: Term, subs: Seq[(Variable, Term)]): (Term, Boolean) = {
    val eq = subs.find(s => (t == s._2))
    if (eq.nonEmpty) (eq.get._1, true)
    else {
      t match {
        case Variable(id) => (t, false)
        case Constant(id) => (t, false)
        case AppliedTerm(f, args) =>
          val induct = condflat(args.map(te => findSubterm2(te, subs)))
          if (!induct._2) (t, false)
          else (AppliedTerm(f, induct._1), true)
      }

    }

  }

  private def findSubterm2(f: Formula, subs: Seq[(Variable, Term)]): (Formula, Boolean) = {
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
        val fv_in_f = subs.flatMap(e => e._2.freeSchematicLabels + e._1)
        if (!fv_in_f.contains(bound)) {
          val induct = findSubterm2(inner, subs)
          if (!induct._2) (f, false)
          else (BinderFormula(label, bound, induct._1), true)
        } else {
          val newv = Variable(freshId((f.freeSchematicLabels ++ fv_in_f).map(_.id), bound.id))
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
        case PredicateFormula(label, args) =>
          (f, false)
        case ConnectorFormula(label, args) =>
          val induct = condflat(args.map(findSubformula2(_, subs)))
          if (!induct._2) (f, false)
          else (ConnectorFormula(label, induct._1), true)
        case BinderFormula(label, bound, inner) =>
          val fv_in_f = subs.flatMap(_._2.freeSchematicLabels)
          if (!fv_in_f.contains(bound)) {
            val induct = findSubformula2(inner, subs)
            if (!induct._2) (f, false)
            else (BinderFormula(label, bound, induct._1), true)
          } else {
            val newv = Variable(freshId((f.freeSchematicLabels ++ fv_in_f).map(_.id), bound.id))
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
    if (r._2) Some(lambda(vars, r._1))
    else None
  }

  def findSubterm(f: Formula, subs: Seq[(Variable, Term)]): Option[LambdaExpression[Term, Formula, ?]] = {
    val vars = subs.map(_._1)
    val r = findSubterm2(f, subs)
    if (r._2) Some(lambda(vars, r._1))
    else None
  }

  def findSubformula(f: Formula, subs: Seq[(VariableFormula, Formula)]): Option[LambdaExpression[Formula, Formula, ?]] = {
    val vars = subs.map(_._1)
    val r = findSubformula2(f, subs)
    if (r._2) Some(lambda(vars, r._1))
    else None
  }

  /*
  object applySubst extends ProofTactic {
    def applyLeftRight(using lib: lisa.prooflib.Library, proof: lib.Proof)
    (phi: Formula)
    (premise: proof.Fact)
    (rightLeft: Boolean = false, toLeft: Boolean = true, toRight: Boolean = true): proof.ProofTacticJudgement = {
      val originSequent = proof.getSequent(premise)
      val leftOrigin = ConnectorFormula(And, originSequent.left.toSeq)
      val rightOrigin = ConnectorFormula(Or, originSequent.right.toSeq)

      if (!toLeft && !toRight) return proof.InvalidProofTactic("applyLeftRight called with no substitution selected (toLeft or toRight).")

      phi match {
        case PredicateFormula(label, args) if label == equality =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.freeSchematicLabels).map(_.id)
          val v = Variable(nFreshId(fv_in_phi, 1).head)
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

          var scproof: Seq[SCProofStep] = Seq(Restate(leftOrigin |- rightOrigin, -1))
          if (toLeft) scproof = scproof :+ LeftSubstEq(result1, scproof.length - 1, List(left -> right), LambdaTermFormula(Seq(v), leftForm))
          if (toRight) scproof = scproof :+ RightSubstEq(result2, scproof.length - 1, List(left -> right), LambdaTermFormula(Seq(v), rightForm))
          scproof = scproof :+ Restate(newleft + phi |- newright, scproof.length - 1)

          proof.ValidProofTactic(
            ???,
            scproof,
            Seq(premise)
          )
        case ConnectorFormula(label, args) if label == Iff =>
          val left = args(0)
          val right = args(1)
          val fv_in_phi = (originSequent.left ++ originSequent.right).flatMap(_.schematicFormulaLabels).map(_.id)
          val H = VariableFormula(nFreshId(fv_in_phi, 1).head)
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

          var scproof: Seq[SCProofStep] = Seq(Restate(leftOrigin |- rightOrigin, -1))
          if (toLeft) scproof = scproof :+ LeftSubstIff(result1, scproof.length - 1, List(left -> right), LambdaFormulaFormula(Seq(H), leftForm))
          if (toRight) scproof = scproof :+ RightSubstIff(result2, scproof.length - 1, List(left -> right), LambdaFormulaFormula(Seq(H), rightForm))
          scproof = scproof :+ Restate(newleft + phi |- newright, scproof.length - 1)

          proof.ValidProofTactic(
            ???,
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

  def simplifySeq(seq: Sequent, ruleseq: IndexedSeq[PredicateFormula], rulesiff: IndexedSeq[ConnectorFormula]): SCProof = {
    /*
        val takenVarsIff = (seq.left.flatMap(_.schematicPredicateLabels) ++ seq.right.flatMap(_.schematicPredicateLabels) ++ ruleseq.flatMap(_.schematicPredicateLabels) ++ rulesiff.flatMap(_.schematicPredicateLabels)).map(_.id)
        val varsIff = nFreshId(takenVarsIff, rulesiff.length).map(VariableFormula)
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
<<<<<<< HEAD
   */
  object Substitution2 extends ProofTactic with ProofFactSequentTactic {
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
      val canReach = UnificationUtils2.canReachOneStepTermFormula(premRight, botRight, equalities.toList)

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

      val canReach = UnificationUtils2.canReachOneStepTermFormula(premRight, botRight, equalities.toList)

      if (canReach.isEmpty || equalities.isEmpty) {
        val canReach2 = UnificationUtils2.canReachOneStepOLFormula(premRight, botRight, iffs.toList)
        if (canReach2.isEmpty) {
          proof.InvalidProofTactic("Iffs and Equalities failed")
        } else {
          val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
            val actIffs = iffs.map((a, b) => Iff(a, b))
            val newBot = bot.copy(right = Set(ConnectorFormula(Or, bot.right.toSeq))) ++<< (actIffs |- ())
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

    def withExplicitRules(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(
        premise: proof.Fact
    )(bot: Sequent): proof.ProofTacticJudgement = {
      // takes a bot
      val premiseSequent: Sequent = proof.getSequent(premise)

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

      // get the original and swapped versions
      val eqs = eqspre ++ eqspre.map(_.swap)
      val iffs = iffspre ++ iffspre.map(_.swap)

      val filteredPrem = (premiseSequent.left filter {
        case PredicateFormula(`equality`, Seq(l, r)) if eqs.contains((l, r)) => false
        case ConnectorFormula(Iff, Seq(l, r)) if iffs.contains((l, r)) => false
        case _ => true
      }).toSeq

      val filteredBot = (bot.left filter {
        case PredicateFormula(`equality`, Seq(l, r)) if eqs.contains((l, r)) => false
        case ConnectorFormula(Iff, Seq(l, r)) if iffs.contains((l, r)) => false
        case _ => true
      }).toSeq

      lazy val rightPairs = premiseSequent.right zip premiseSequent.right.map(x => bot.right.find(y => UnificationUtils2.canReachOneStep(x, y, iffs, eqs).isDefined))
      lazy val leftPairs = filteredPrem zip filteredPrem.map(x => filteredBot.find(y => UnificationUtils2.canReachOneStep(x, y, iffs, eqs).isDefined))

      lazy val violatingFormulaLeft = leftPairs.find(_._2.isEmpty)
      lazy val violatingFormulaRight = rightPairs.find(_._2.isEmpty)

      if (violatingFormulaLeft.isDefined)
        proof.InvalidProofTactic(s"Could not rewrite LHS of premise into conclusion with given substitutions.\nViolating Formula: ${FOLPrinter.prettyFormula(violatingFormulaLeft.get._1)}")
      else if (violatingFormulaRight.isDefined)
        proof.InvalidProofTactic(s"Could not rewrite RHS of premise into conclusion with given substitutions.\nViolating Formula: ${FOLPrinter.prettyFormula(violatingFormulaRight.get._1)}")
      else {
        // actually construct proof
        try {
          val leftLambdas = leftPairs.collect { case (l, Some(r)) => UnificationUtils2.canReachOneStep(l, r, iffs, eqs).get }
          val rightLambdas = rightPairs.collect { case (l, Some(r)) => UnificationUtils2.canReachOneStep(l, r, iffs, eqs).get }

          val eqsForm = eqs.map { case (l, r) => PredicateFormula(`equality`, Seq(l, r)) }.toSet
          val iffsForm = iffs.map { case (l, r) => ConnectorFormula(Iff, Seq(l, r)) }.toSet

          val leftEqs = eqs.map(_._1).toSeq
          val rightEqs = eqs.map(_._2).toSeq
          val leftIffs = iffs.map(_._1).toSeq
          val rightIffs = iffs.map(_._2).toSeq

          val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
            var premiseWithSubst = premiseSequent ++<< (eqsForm |- ()) ++<< (iffsForm |- ())
            proof.library.have(premiseWithSubst) by BasicStepTactic.Weakening(premise)

            if (!leftLambdas.isEmpty) {
              val leftEqLambdas = leftLambdas.map(f => lambda(f._2.toSeq, substituteFormulaVariables(f._3, ((f._1: Seq[VariableFormula]) zip iffs.map(_._1)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = leftEqLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda) => {
                  val newSequent = prevSequent -<? nextLambda(leftEqs) +<< nextLambda(rightEqs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.LeftSubstEq(eqs, nextLambda)

                  newSequent
                }
              }
            }
            if (!rightLambdas.isEmpty) {
              val rightEqLambdas = rightLambdas.map(f => lambda(f._2.toSeq, substituteFormulaVariables(f._3, ((f._1: Seq[VariableFormula]) zip iffs.map(_._1)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = rightEqLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda: LambdaTermFormula) => {
                  val newSequent = prevSequent ->? nextLambda(leftEqs) +>> nextLambda(rightEqs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.RightSubstEq(eqs, nextLambda)

                  newSequent
                }
              }
            }

            if (!leftLambdas.isEmpty) {
              val leftIffLambdas = leftLambdas.map(f => lambda(f._1.toSeq, substituteVariablesInFormula(f._3, ((f._2: Seq[Variable]) zip eqs.map(_._2)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = leftIffLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda) => {
                  val newSequent = prevSequent -<? nextLambda(leftIffs) +<< nextLambda(rightIffs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.LeftSubstIff(iffs, nextLambda)

                  newSequent
                }
              }
            }
            if (!rightLambdas.isEmpty) {
              val rightIffLambdas = rightLambdas.map(f => lambda(f._1.toSeq, substituteVariablesInFormula(f._3, ((f._2: Seq[Variable]) zip eqs.map(_._2)).toMap)))

              // substitute and set a new premise for next step
              premiseWithSubst = rightIffLambdas.foldLeft(premiseWithSubst) {
                case (prevSequent, nextLambda) => {
                  val newSequent = prevSequent ->? nextLambda(leftIffs) +>> nextLambda(rightIffs)
                  proof.library.thenHave(newSequent) by BasicStepTactic.RightSubstIff(iffs, nextLambda)

                  newSequent
                }
              }
            }

            substitutions.foreach {
              case f: Formula =>
              case f: proof.Fact @unchecked =>
                (proof.library.andThen(SimpleDeducedSteps.Discharge(f)))
              case j: RunningTheory#Justification =>
                proof.library.andThen(SimpleDeducedSteps.Discharge(j.asInstanceOf[lib.theory.Justification]))
            }

            proof.library.thenHave(bot) by SimpleDeducedSteps.Restate

          })

          BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof for Substitution failed.")
        } catch case e: UnapplicableProofTactic => proof.InvalidProofTactic(s"Could not rewrite given conlusion sequent into substituted premise. You may have a typo.\n\t${e.errorMessage}")

      }

    }

    // def apply2(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact)(
    //     bot: Sequent
    // ): proof.ProofTacticJudgement = apply2(using lib, proof)(false, substitutions: _*)(premise)(bot)

  }

  object Simplify extends ProofTactic {

    def once(using lib: lisa.prooflib.Library, proof: lib.Proof)(rightLeft: Boolean = false, substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(
        premise: proof.Fact
    ): proof.ProofTacticJudgement = {
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

      lazy val rightLambdas = premiseSequent.right.map(UnificationUtils2.getContextOneStepFormula(_, iffs, eqs))
      lazy val leftLambdas = filteredPrem.map(UnificationUtils2.getContextOneStepFormula(_, iffs, eqs))

      // actually construct proof
      val eqsForm = eqs.map { case (l, r) => PredicateFormula(`equality`, Seq(l, r)) }.toSet
      val iffsForm = iffs.map { case (l, r) => ConnectorFormula(Iff, Seq(l, r)) }.toSet

      val leftEqs = eqs.map(_._1).toSeq
      val rightEqs = eqs.map(_._2).toSeq
      val leftIffs = iffs.map(_._1).toSeq
      val rightIffs = iffs.map(_._2).toSeq

      val sp = new BasicStepTactic.SUBPROOF(using proof)(None)({
        var premiseWithSubst = premiseSequent ++<< (eqsForm |- ()) ++<< (iffsForm |- ())
        proof.library.have(premiseWithSubst) by BasicStepTactic.Weakening(premise)

        if (!leftLambdas.isEmpty) {
          val leftEqLambdas = leftLambdas.map(f => lambda(f._2.toSeq, substituteFormulaVariables(f._3, ((f._1: Seq[VariableFormula]) zip iffs.map(_._1)).toMap)))

          // substitute and set a new premise for next step
          premiseWithSubst = leftEqLambdas.foldLeft(premiseWithSubst) {
            case (prevSequent, nextLambda) => {
              val newSequent = prevSequent -<< nextLambda(leftEqs) +<< nextLambda(rightEqs)
              proof.library.thenHave(newSequent) by BasicStepTactic.LeftSubstEq(eqs, nextLambda)

              newSequent
            }
          }
        }
        if (!rightLambdas.isEmpty) {
          val rightEqLambdas = rightLambdas.map(f => lambda(f._2.toSeq, substituteFormulaVariables(f._3, ((f._1: Seq[VariableFormula]) zip iffs.map(_._1)).toMap)))

          // substitute and set a new premise for next step
          premiseWithSubst = rightEqLambdas.foldLeft(premiseWithSubst) {
            case (prevSequent, nextLambda: LambdaTermFormula) => {
              val newSequent = prevSequent ->> nextLambda(leftEqs) +>> nextLambda(rightEqs)
              proof.library.thenHave(newSequent) by BasicStepTactic.RightSubstEq(eqs, nextLambda)

              newSequent
            }
          }
        }

        if (!leftLambdas.isEmpty) {
          val leftIffLambdas = leftLambdas.map(f => lambda(f._1.toSeq, substituteVariablesInTerm(f._3, ((f._2: Seq[Variable]) zip eqs.map(_._2)).toMap)))

          // substitute and set a new premise for next step
          premiseWithSubst = leftIffLambdas.foldLeft(premiseWithSubst) {
            case (prevSequent, nextLambda) => {
              val newSequent = prevSequent -<< nextLambda(leftIffs) +<< nextLambda(rightIffs)
              proof.library.thenHave(newSequent) by BasicStepTactic.LeftSubstIff(iffs, nextLambda)

              newSequent
            }
          }
        }
        if (!rightLambdas.isEmpty) {
          val rightIffLambdas = rightLambdas.map(f => lambda(f._1.toSeq, substituteVariablesInTerm(f._3, ((f._2: Seq[Variable]) zip eqs.map(_._2)).toMap)))

          // substitute and set a new premise for next step
          premiseWithSubst = rightIffLambdas.foldLeft(premiseWithSubst) {
            case (prevSequent, nextLambda) => {
              val newSequent = prevSequent ->> nextLambda(leftIffs) +>> nextLambda(rightIffs)
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

      })

      if (isSameSequent(premiseSequent, sp.scproof.conclusion)) proof.InvalidProofTactic("Could not perform a substitution.")
      else BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof for Substitution failed.")

    }

    // def once(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact): proof.ProofTacticJudgement =
    //   once(using lib, proof)(false, substitutions: _*)(premise)

    // def exhaustive(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact): proof.ProofTacticJudgement = star(once(using lib, proof)(substitutions))(premise)

    def exhaustive(using lib: lisa.prooflib.Library, proof: lib.Proof, line: sourcecode.Line, file: sourcecode.File)(
        substitutions: (proof.Fact | Formula | RunningTheory#Justification)*
    )(premise: proof.Fact): proof.ProofTacticJudgement = {
      @tailrec
      def f(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact): Unit = {
        once(using lib, proof)(false, substitutions: _*)(premise) match {
          case v: proof.ValidProofTactic => {
            val ps = v.validate(line, file)
            f(using lib, proof)(substitutions: _*)(ps)
          }
          case _ => ()
        }
      }
      try
        BasicStepTactic.TacticSubproof {
          f(substitutions: _*)(premise)
        }
      catch case _ => proof.InvalidProofTactic("Could not perform a substitution.")
    }

    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(substitutions: (proof.Fact | Formula | RunningTheory#Justification)*)(premise: proof.Fact): proof.ProofTacticJudgement =
      exhaustive(using lib, proof)(substitutions: _*)(premise)
  }
   */
}
