package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*

trait DerivedFromPremises:
  protected def prove(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement

  final class WithPremises(premises: Seq[Thm])(using file: sourcecode.File, line: sourcecode.Line, library: Library) extends ((Sequent, Thm) => ProofJudgement):
    def apply(conclusion: Sequent, lastStep: Thm): ProofJudgement =
      prove(conclusion, lastStep +: premises)

    def apply(premise: Thm): Sequent => ProofJudgement =
      conclusion => prove(conclusion, premise +: premises)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
    prove(conclusion, Seq.empty)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: Thm): ProofJudgement =
    prove(conclusion, Seq(premise))

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
    prove(conclusion, Seq(Thm(premise)))

  def from(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*): Sequent => ProofJudgement =
    conclusion => prove(conclusion, premises)

  def fromLastStep(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*): (Sequent, Thm) => ProofJudgement =
    (conclusion, lastStep) => prove(conclusion, lastStep +: premises)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*): WithPremises =
    WithPremises(premises)
