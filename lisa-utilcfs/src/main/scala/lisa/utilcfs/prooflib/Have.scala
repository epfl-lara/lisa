package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*

trait SequentTactic:
  def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent): ProofJudgement
trait PremiseSequentTactic:
  def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement

trait SequentTacticM[+T]:
  def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent): ProofCarrier[T]
trait PremiseSequentTacticM[+T]:
  def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent, premise: K.Thm): ProofCarrier[T]

private def noPreviousStep(using file: sourcecode.File, line: sourcecode.Line): ProofError =
  SoftError("thenHave requires a previous theorem in the local proof context.", file, line)

private def failedPreviousStep(using lib: Library, proof: Proof)(file: sourcecode.File, line: sourcecode.Line)(statement: Sequent): K.Thm =
  val error = noPreviousStep
  proof.absorbDestruct(ProofCarrier(Set(error), statement.underlying, None, ()))._1

private inline def record[T](using proof: Proof)(judgement: ProofCarrier[T]): (K.Thm, T) =
  proof.absorbDestruct(judgement)

class HaveSequent(val statement: Sequent):
  infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTactic): K.Thm =
    by(using lib, proof, file, line)
      ((conclusion: Sequent) => tactic.apply(using file, line)(using lib)(conclusion))

  infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofJudgement): K.Thm =
    record(tactic(statement))._1

class ThenHaveSequent(val statement: Sequent):
  infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTactic): K.Thm =
    by(using lib, proof, file, line)
      ((conclusion: Sequent, premise: K.Thm) => tactic.apply(using file, line)(using lib)(conclusion, premise))

  infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, K.Thm) => ProofJudgement): K.Thm =
    proof.last match
      case Some(j) => record(tactic(statement, j))._1
      case None => failedPreviousStep(file, line)(statement)

class HaveMSequent(val statement: Sequent):
  infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTacticM[T]): (K.Thm, T) =
    by(using lib, proof, file, line)
      ((conclusion: Sequent) => tactic.apply(using file, line)(using lib)(conclusion))

  infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofCarrier[T]): (K.Thm, T) =
    record(tactic(statement))

class ThenHaveMSequent(val statement: Sequent):
  infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTacticM[T]): (K.Thm, T) =
    by(using lib, proof, file, line)
      ((conclusion: Sequent, premise: K.Thm) => tactic.apply(using file, line)(using lib)(conclusion, premise))

  infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, K.Thm) => ProofCarrier[T]): (K.Thm, T) =
    proof.last match
      case Some(j) => record(tactic(statement, j))
      case None => throw new NoSuchElementException("thenHaveM requires a previous theorem in the local proof context. Cannot synthesize a return value.")

def have(statement: Sequent): HaveSequent =
  HaveSequent(statement)

def thenHave(statement: Sequent): ThenHaveSequent =
  ThenHaveSequent(statement)

def haveM(statement: Sequent): HaveMSequent =
  HaveMSequent(statement)

def thenHaveM(statement: Sequent): ThenHaveMSequent =
  ThenHaveMSequent(statement)

inline def have(using lib: Library, proof: Proof)(thm: K.Thm): K.Thm =
  have(ProofJudgement(thm))

def have(using proof: Proof)(judgement: ProofJudgement): K.Thm =
  proof.absorbDestruct(judgement)._1

def lastStep(using proof: Proof): K.Thm =
  proof.last.getOrElse:
    throw new NoSuchElementException("lastStep called on empty proof.")
