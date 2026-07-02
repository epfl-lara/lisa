package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.ProofHelpers.*
import sourcecode.File
import sourcecode.Line

trait DerivedFromPremises:
  protected def prove(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
    prove(conclusion, Seq.empty)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: Thm): ProofJudgement =
    prove(conclusion, Seq(premise))

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
    prove(conclusion, Seq(Thm(premise)))

  def from(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*): Sequent => ProofJudgement =
    conclusion => prove(conclusion, premises)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*): (Sequent, Thm) => ProofJudgement =
    (conclusion, lastStep) => prove(conclusion, lastStep +: premises)

object Substitute extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  protected def prove(using File, Line)(using Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement = ???

object Congruence extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  protected def prove(using File, Line)(using Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement = ???

object Tableau extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  protected def prove(using File, Line)(using Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement = ???

object Generalize extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement = ???
  override def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
    BasicStep.RightForall(using file, line)(using library)(conclusion, premise)

object InstantiateForall extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement = ???

  final class WithTerms(terms: Seq[Expr[?]])(using file: sourcecode.File, line: sourcecode.Line, library: Library) extends ((Sequent, Thm) => ProofJudgement):
    def apply(premise: Thm): Sequent => ProofJudgement =
      conclusion => InstantiateForall.prove(conclusion, Seq(premise))

    def apply(premises: Thm*): Sequent => ProofJudgement =
      conclusion => InstantiateForall.prove(conclusion, premises)

    def apply(conclusion: Sequent, premise: Thm): ProofJudgement =
      InstantiateForall.prove(conclusion, Seq(premise))

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(terms: Expr[?]*): WithTerms =
    WithTerms(terms)
