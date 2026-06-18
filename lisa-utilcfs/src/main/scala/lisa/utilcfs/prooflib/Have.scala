package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.* 

trait SequentTactic:
  def apply(using sourcecode.File, sourcecode.Line)(using Library, Proof)(conclusion: Sequent): ProofJudgement
trait PremiseSequentTactic:
  def apply(using sourcecode.File, sourcecode.Line)(using Library, Proof)(conclusion: Sequent, premise: K.Thm): ProofJudgement

trait SequentTacticM[+T]:
  def apply(using sourcecode.File, sourcecode.Line)(using Library, Proof)(conclusion: Sequent): ProofCarrier[T]
trait PremiseSequentTacticM[+T]:
  def apply(using sourcecode.File, sourcecode.Line)(using Library, Proof)(conclusion: Sequent, premise: K.Thm): ProofCarrier[T]

private def noPreviousStep(using file: sourcecode.File, line: sourcecode.Line): ProofError =
  SoftError("thenHave requires a previous theorem in the local proof context.", file, line)

private def failedPreviousStep(using lib: Library, proof: Proof)(file: sourcecode.File, line: sourcecode.Line)(statement: Sequent): ProofJudgement =
  val error = noPreviousStep
  K.Sorry(using lib.theory)(statement.underlying) match
    case Left(err) => ProofCarrier(Set(error, SoftError(err.toString, file, line)), statement.underlying, None, ())
    case Right(thm) => proof.absorb(ProofCarrier(Set(error), statement.underlying, Some(thm), ()))

private inline def record[T](judgement: ProofCarrier[T])(using proof: Proof): ProofCarrier[T] =
  proof.absorb(judgement)

class HaveSequent(val statement: Sequent):
  infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTactic): ProofJudgement =
    record(tactic.apply(using file, line)(using lib, proof)(statement))

  infix def by(using lib: Library, proof: Proof)(tactic: Sequent => ProofJudgement): ProofJudgement =
    record(tactic(statement))

class ThenHaveSequent(val statement: Sequent):
  infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTactic): ProofJudgement =
    proof.last match
      case Some(j) => 
        record(tactic.apply(using file, line)(using lib, proof)(statement, j))
      case None => failedPreviousStep(file, line)(statement)

  infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, K.Thm) => ProofJudgement): ProofJudgement =
    proof.last match
      case Some(j) => record(tactic(statement, j))
      case None => failedPreviousStep(file, line)(statement)

class HaveMSequent(val statement: Sequent):
  infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTacticM[T]): ProofCarrier[T] =
    record(tactic.apply(using file, line)(using lib, proof)(statement))

  infix def by[T](using lib: Library, proof: Proof)(tactic: Sequent => ProofCarrier[T]): ProofCarrier[T] =
    record(tactic(statement))

class ThenHaveMSequent(val statement: Sequent):
  infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTacticM[T]): ProofCarrier[T] =
    proof.last match
      case Some(j) => record(tactic.apply(using file, line)(using lib, proof)(statement, j))
      case None => throw new NoSuchElementException("thenHaveM requires a previous theorem in the local proof context. Cannot synthesize a return value.")

  infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, K.Thm) => ProofCarrier[T]): ProofCarrier[T] =
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

def have(using proof: Proof)(judgement: ProofJudgement): ProofJudgement =
  proof.absorb(judgement)

def have(using lib: Library, proof: Proof)(thm: K.Thm): ProofJudgement =
  proof.absorb(ProofCarrier(Set.empty, thm.statement, Some(thm), ()))

def lastStep(using proof: Proof): K.Thm =
  proof.last.getOrElse:
    throw new NoSuchElementException("lastStep called on empty proof.")
