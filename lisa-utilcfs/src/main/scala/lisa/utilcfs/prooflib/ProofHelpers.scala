package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*

object ProofHelpers:

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
    val error = noPreviousStep(using file, line)
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

  object Theorems:
    /** Returns a theorem by full name, or by short name when unambiguous. */
    def get(using library: Library)(name: String): Option[Theorem] =
      library.theorems.get(name)

    /** Returns a theorem by exact full name. */
    def full(using library: Library)(name: String): Option[Theorem] =
      library.theorems.getFull(name)

    /** Returns a theorem by short name only when that short name is unambiguous. */
    def short(using library: Library)(name: String): Option[Theorem] =
      library.theorems.getShort(name)

    /** Returns all registered theorems in registration order. */
    def all(using library: Library): collection.View[Theorem] =
      library.theorems.all

  /** Converts a kernel formula to the front expression type. */
  inline def asFrontFormula(expression: K.Expression): Expr[Prop] =
    asFrontExpression(expression).asInstanceOf[Expr[Prop]]

  /** Converts a kernel sequent to the front sequent type. */
  def asFrontSequent(statement: K.Sequent): Sequent =
    Sequent(statement.left.map(asFrontFormula), statement.right.map(asFrontFormula))

  /** The current local proof context. */
  inline def currentProof(using proof: Proof): Proof =
    proof

  /** The goal of the current proof, if one was declared. */
  def thesis(using proof: Proof): Sequent =
    proof.goal.map(asFrontSequent).getOrElse:
      throw new NoSuchElementException("thesis called outside a proof with a declared goal.")

  /** Alias for [[thesis]]. */
  inline def goal(using proof: Proof): Sequent =
    thesis

  /** Concludes the current goal with a sorry step and records it in the proof. */
  inline def sorry(using library: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line): K.Thm =
    have(thesis) by BasicStep.Sorry

  /** A tactic consuming only a previously proved theorem. */
  trait ThmTactic:
    def apply(using sourcecode.File, sourcecode.Line)(using Library)(premise: K.Thm): ProofJudgement

  /** Helper for `andThen tactic`, where the tactic consumes the previous theorem. */
  final class AndThen private[prooflib] (using library: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line):
    private def missingPreviousStep: K.Thm =
      val statement = proof.goal.getOrElse(K.Sequent(Set.empty, Set(K.top)))
      proof.absorbDestruct(ProofCarrier(Set(SoftError("andThen requires a previous theorem in the local proof context.", file, line)), statement, None, ()))._1

    /** Applies a function tactic to the previous theorem and records the result. */
    infix def apply(tactic: K.Thm => ProofJudgement): K.Thm =
      proof.last match
        case Some(premise) => proof.absorbDestruct(tactic(premise))._1
        case None => missingPreviousStep

    /** Applies an object tactic to the previous theorem and records the result. */
    infix def apply(tactic: ThmTactic): K.Thm =
      apply((premise: K.Thm) => tactic.apply(using file, line)(using library)(premise))

  /** Starts an `andThen` proof step from the previous theorem. */
  def andThen(using library: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line): AndThen =
    AndThen()

  extension (thm: K.Thm)
    /** The theorem statement as a front sequent. */
    def frontStatement: Sequent =
      asFrontSequent(thm.statement)

    /** Instantiates a theorem schema and returns the resulting theorem. */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: SubstPair*): K.Thm =
      val conclusion = thm.frontStatement.substitute(insts*)
      BasicStep.InstSchema(using file, line)(using library)(insts*)(thm)(conclusion).destruct._1

  extension (theorem: Theorem)
    /** Instantiates a theorem schema and returns the resulting theorem. */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: SubstPair*): K.Thm =
      theorem.thm.of(using file, line)(using library)(insts*)
