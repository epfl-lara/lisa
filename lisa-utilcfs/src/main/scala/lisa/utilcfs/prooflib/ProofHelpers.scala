package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.Helpers.withParams

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

  private def failedPreviousStep(using lib: Library, proof: Proof)(file: sourcecode.File, line: sourcecode.Line)(statement: Sequent): Thm =
    val error = noPreviousStep(using file, line)
    proof.absorbDestruct(ProofCarrier(Set(error), target(statement), None, ()))._1

  private def target(using proof: Proof)(statement: Sequent): Sequent =
    proof.withAssumptions(statement)

  private inline def record[T](using proof: Proof)(judgement: ProofCarrier[T]): (Thm, T) =
    proof.absorbDestruct(judgement)

  private def liftSubproofResult(using lib: Library)(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, carrier: ProofCarrier[?]): ProofJudgement =
    val intended = conclusion.underlying
    if carrier.statement.underlying == intended then carrier.judgement
    else
      carrier.justification match
        case Some(thm) =>
          K.Restate(using lib.theory)(intended, thm.kernel)
            .orElse(K.Weakening(using lib.theory)(intended, thm.kernel))
            .fold(
              error =>
                carrier.judgement
                  .withError(SoftError(withParams("Subproof does not prove the requested conclusion.", "Proven" -> carrier.statement, "Conclusion" -> conclusion, "Reason" -> error), file, line))
                  .copy(statement = conclusion),
              thm => carrier.judgement.withJustification(Thm(conclusion, thm))
            )
        case None =>
          carrier.judgement
            .withError(SoftError(withParams("Subproof produced no theorem.", "Conclusion" -> conclusion), file, line))
            .copy(statement = conclusion)

  private def runSubproof(using lib: Library, proof: Proof)(file: sourcecode.File, line: sourcecode.Line)(statement: Sequent)(inner: Proof ?=> Any): ProofJudgement =
    val conclusion = target(statement)
    def carrier(using subproof: Proof): ProofCarrier[?] =
      inner(using subproof) match
        case result: ProofCarrier[?] => result
        case _ => subproof.pure(())
    liftSubproofResult(file, line)(conclusion, proof.withSubcontext(Some(conclusion.underlying))(carrier))

  class HaveSequent(val statement: Sequent):
    infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTactic): Thm =
      by(using lib, proof, file, line)
        ((conclusion: Sequent) => tactic.apply(using file, line)(using lib)(conclusion))

    infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofJudgement): Thm =
      record(tactic(target(statement)))._1

    infix def subproof(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(inner: Proof ?=> Any): Thm =
      record(runSubproof(file, line)(statement)(inner))._1

  class ThenHaveSequent(val statement: Sequent):
    infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTactic): Thm =
      by(using lib, proof, file, line)
        ((conclusion: Sequent, premise: Thm) => tactic.apply(using file, line)(using lib)(conclusion, premise.kernel))

    infix def by(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, Thm) => ProofJudgement): Thm =
      proof.last match
        case Some(j) => record(tactic(target(statement), j))._1
        case None => failedPreviousStep(file, line)(statement)

    infix def subproof(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(inner: Proof ?=> Any): Thm =
      record(runSubproof(file, line)(statement)(inner))._1

  class HaveMSequent(val statement: Sequent):
    infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTacticM[T]): (Thm, T) =
      by(using lib, proof, file, line)
        ((conclusion: Sequent) => tactic.apply(using file, line)(using lib)(conclusion))

    infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofCarrier[T]): (Thm, T) =
      record(tactic(target(statement)))

  class ThenHaveMSequent(val statement: Sequent):
    infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTacticM[T]): (Thm, T) =
      by(using lib, proof, file, line)
        ((conclusion: Sequent, premise: Thm) => tactic.apply(using file, line)(using lib)(conclusion, premise.kernel))

    infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, Thm) => ProofCarrier[T]): (Thm, T) =
      proof.last match
        case Some(j) => record(tactic(target(statement), j))
        case None => throw new NoSuchElementException("thenHaveM requires a previous theorem in the local proof context. Cannot synthesize a return value.")

  def have(statement: Sequent): HaveSequent =
    HaveSequent(statement)

  def have(statement: K.Sequent): HaveSequent =
    HaveSequent(asFrontSequent(statement))

  def thenHave(statement: Sequent): ThenHaveSequent =
    ThenHaveSequent(statement)

  def haveM(statement: Sequent): HaveMSequent =
    HaveMSequent(statement)

  def thenHaveM(statement: Sequent): ThenHaveMSequent =
    ThenHaveMSequent(statement)

  inline def have(using lib: Library, proof: Proof)(thm: K.Thm): Thm =
    have(ProofJudgement(thm))

  inline def have(using lib: Library, proof: Proof)(thm: Thm): Thm =
    have(ProofJudgement(thm))

  def have(using proof: Proof)(judgement: ProofJudgement): Thm =
    proof.absorbDestruct(judgement)._1

  def lastStep(using proof: Proof): Thm =
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
    Thm.liftFormula(expression)

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

  private def splitConjunctions(formula: Expr[Prop]): Set[Expr[Prop]] =
    formula match
      case /\(left, right) => splitConjunctions(left) ++ splitConjunctions(right)
      case _ => Set(formula)

  /** Adds formulas to the local assumption context and proves them by hypothesis. */
  def assume(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(formulas: Expr[Prop]*): Thm =
    proof.assume(formulas)
    if formulas.isEmpty then have(Sequent(Set.empty, Set(top))) by BasicStep.RestateTrue
    else have(Sequent(Set.empty, formulas.toSet)) by BasicStep.Hypothesis

  /** Assumes every formula on the left of the current goal. */
  def assumeAll(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line): Thm =
    assume(thesis.left.toSeq*)

  /** Assumes every formula on the left of the current goal, splitting conjunctions recursively. */
  def assumeAllSplit(using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line): Thm =
    assume(thesis.left.flatMap(splitConjunctions).toSeq*)

  /** Concludes the current goal with a sorry step and records it in the proof. */
  inline def sorry(using library: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line): Thm =
    have(thesis) by BasicStep.Sorry

  /** A tactic consuming only a previously proved theorem. */
  trait ThmTactic:
    def apply(using sourcecode.File, sourcecode.Line)(using Library)(premise: Thm): ProofJudgement

  /** Helper for `andThen tactic`, where the tactic consumes the previous theorem. */
  final class AndThen private[prooflib] (using library: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line):
    private def missingPreviousStep: Thm =
      val statement = proof.goal.getOrElse(K.Sequent(Set.empty, Set(K.top)))
      proof.absorbDestruct(ProofCarrier(Set(SoftError("andThen requires a previous theorem in the local proof context.", file, line)), asFrontSequent(statement), None, ()))._1

    /** Applies a function tactic to the previous theorem and records the result. */
    infix def apply(tactic: Thm => ProofJudgement): Thm =
      proof.last match
        case Some(premise) => proof.absorbDestruct(tactic(premise))._1
        case None => missingPreviousStep

    /** Applies an object tactic to the previous theorem and records the result. */
    infix def apply(tactic: ThmTactic): Thm =
      apply((premise: Thm) => tactic.apply(using file, line)(using library)(premise))

  /** Starts an `andThen` proof step from the previous theorem. */
  def andThen(using library: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line): AndThen =
    AndThen()

  extension (thm: K.Thm)
    /** The theorem statement as a front sequent. */
    def frontStatement: Sequent =
      asFrontSequent(thm.statement)

    /** Instantiates a theorem schema and returns the resulting theorem. */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: SubstPair*): Thm =
      val conclusion = thm.frontStatement.substitute(insts*)
      BasicStep.InstSchema(using file, line)(using library)(insts*)(thm)(conclusion).destruct._1

  extension (thm: Thm)
    /** Instantiates a theorem schema and returns the resulting theorem. */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: SubstPair*): Thm =
      thm.kernel.of(using file, line)(using library)(insts*)

  extension (theorem: Theorem)
    /** Instantiates a theorem schema and returns the resulting theorem. */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: SubstPair*): Thm =
      theorem.thm.of(using file, line)(using library)(insts*)
