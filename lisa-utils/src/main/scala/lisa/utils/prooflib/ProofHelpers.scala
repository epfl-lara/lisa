package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.UserLisaException.InvalidProofOperationException
import lisa.utils.automation.InstantiateForall
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.Helpers.withParams

object ProofHelpers:

  type SequentTactic = SequentTacticM[Unit]
  type PremiseSequentTactic = PremiseSequentTacticM[Unit]

  trait SequentTacticM[+T]:
    def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent): ProofCarrier[T]

  trait PremiseSequentTacticM[+T]:
    def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent, premise: K.Thm): ProofCarrier[T]
    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premise: K.Thm): Sequent => ProofCarrier[T] =
      conclusion => apply(using file, line)(using library)(conclusion, premise)
    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premise: Thm): Sequent => ProofCarrier[T] =
      conclusion => apply(using file, line)(using library)(conclusion, premise.kernel)
    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(theorem: Theorem): Sequent => ProofCarrier[T] =
      conclusion => apply(using file, line)(using library)(conclusion, theorem.kernel)

  private def prove(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(statement: Sequent)(tactic: Sequent => ProofJudgement): Thm =
    val conclusion = proof.withAssumptions(statement)
    proof.absorbDestruct(proof.recover(conclusion)(tactic(conclusion)))._1

  private def liftSubproofResult(using lib: Library)(conclusion: Sequent, carrier: ProofCarrier[?]): ProofJudgement =
    carrier.flatMap { (_, theorem) =>
      if theorem.statement.underlying == conclusion.underlying then ProofJudgement(Thm(conclusion, theorem.kernel))
      else
        K.Restate(using lib.theory)(conclusion.underlying, theorem.kernel)
          .orElse(K.Weakening(using lib.theory)(conclusion.underlying, theorem.kernel))
          .fold(
            error => ProofCarrier.Failure(withParams("Subproof does not prove the requested conclusion.", "Proven" -> theorem.statement, "Conclusion" -> conclusion, "Reason" -> error)),
            kernel => ProofJudgement(Thm(conclusion, kernel))
          )
    }

  private def runSubproof(using lib: Library, proof: ProofBuilder)(conclusion: Sequent)(inner: ProofBuilder ?=> Any): ProofJudgement =
    def carrier(using subproof: ProofBuilder): ProofCarrier[?] =
      inner(using subproof) match
        case result: ProofCarrier[?] => result
        case theorem: Thm => ProofJudgement(theorem)
        case _ => subproof.pure(())

    liftSubproofResult(conclusion, proof.withSubcontext(Some(conclusion))(carrier))

  /**
   * Adds context to an expected tactic failure without throwing or recording it.
   */
  def unwrapTactic(judgement: ProofJudgement)(message: String): ProofJudgement =
    judgement match
      case failure: ProofCarrier.Failure => ProofCarrier.Failure(s"$message\n${failure.message}")
      case success => success

  class HaveSequent(val statement: Sequent):
    infix def by(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTactic): Thm =
      by(using lib, proof, file, line)((conclusion: Sequent) => tactic.apply(using file, line)(using lib)(conclusion))

    infix def by(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofJudgement): Thm =
      prove(statement)(tactic)

    infix def subproof(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(inner: ProofBuilder ?=> Any): Thm =
      prove(statement)(conclusion => runSubproof(conclusion)(inner))

  class ThenHaveSequent(val statement: Sequent):
    infix def by(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofJudgement): Thm =
      prove(statement)(tactic)

    infix def by(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTactic): Thm =
      by(using lib, proof, file, line)((conclusion: Sequent, premise: Thm) => tactic.apply(using file, line)(using lib)(conclusion, premise.kernel))

    infix def by(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, Thm) => ProofJudgement): Thm =
      prove(statement): conclusion =>
        proof.last match
          case Some(j) => tactic(conclusion, j)
          case None => throw new InvalidProofOperationException("thenHave requires a previous theorem in the local proof context.")

    @scala.annotation.targetName("byThmCurried")
    infix def by(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: Thm => Sequent => ProofJudgement): Thm =
      by(using lib, proof, file, line)((conclusion: Sequent, premise: Thm) => tactic(premise)(conclusion))

    @scala.annotation.targetName("byKernelCurried")
    infix def by(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: K.Thm => Sequent => ProofJudgement): Thm =
      by(using lib, proof, file, line)((conclusion: Sequent, premise: Thm) => tactic(premise.kernel)(conclusion))

    infix def subproof(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(inner: ProofBuilder ?=> Any): Thm =
      prove(statement)(conclusion => runSubproof(conclusion)(inner))

  class HaveMSequent(val statement: Sequent):
    infix def by[T](using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTacticM[T]): (Thm, T) =
      by(using lib, proof, file, line)((conclusion: Sequent) => tactic.apply(using file, line)(using lib)(conclusion))

    infix def by[T](using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofCarrier[T]): (Thm, T) =
      proof.absorbDestruct(tactic(proof.withAssumptions(statement)))

  class ThenHaveMSequent(val statement: Sequent):
    infix def by[T](using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: PremiseSequentTacticM[T]): (Thm, T) =
      by(using lib, proof, file, line)((conclusion: Sequent, premise: Thm) => tactic.apply(using file, line)(using lib)(conclusion, premise.kernel))

    infix def by[T](using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: (Sequent, Thm) => ProofCarrier[T]): (Thm, T) =
      proof.last match
        case Some(j) => proof.absorbDestruct(tactic(proof.withAssumptions(statement), j))
        case None => throw new InvalidProofOperationException("thenHaveM requires a previous theorem in the local proof context.")

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

  inline def have(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(thm: K.Thm): Thm =
    have(Thm(thm))

  inline def have(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(thm: Thm): Thm =
    if proof.assumptions.isEmpty then have(ProofJudgement(thm))
    else prove(thm.statement)(BasicStep.Weakening(thm.kernel))

  def have(using proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(judgement: ProofJudgement): Thm =
    proof.absorbDestruct(judgement)._1

  def lastStep(using proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line): Thm =
    proof.last.getOrElse:
      throw new InvalidProofOperationException("lastStep called on empty proof.")

  object Theorems:
    /**
     * Returns a theorem by full name, or by short name when unambiguous.
     */
    def get(using library: Library)(name: String): Option[Theorem] =
      library.theorems.get(name)

    /**
     * Returns a theorem by exact full name.
     */
    def full(using library: Library)(name: String): Option[Theorem] =
      library.theorems.getFull(name)

    /**
     * Returns a theorem by short name only when that short name is unambiguous.
     */
    def short(using library: Library)(name: String): Option[Theorem] =
      library.theorems.getShort(name)

    /**
     * Returns all registered theorems in registration order.
     */
    def all(using library: Library): collection.View[Theorem] =
      library.theorems.all

  /**
   * Converts a kernel formula to the front expression type.
   */
  inline def asFrontFormula(expression: K.Expression): Expr[Prop] =
    Thm.liftFormula(expression)

  /**
   * Converts a kernel sequent to the front sequent type.
   */
  def asFrontSequent(statement: K.Sequent): Sequent =
    Thm.liftSequent(statement)

  /**
   * The current local proof context.
   */
  inline def currentProof(using proof: ProofBuilder): ProofBuilder =
    proof

  /**
   * The goal of the current proof, if one was declared.
   */
  def thesis(using proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line): Sequent =
    proof.goal.getOrElse:
      throw new InvalidProofOperationException("thesis called outside a proof with a declared goal.")

  /**
   * Alias for [[thesis]].
   */
  inline def goal(using proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line): Sequent =
    thesis

  private def splitConjunctions(formula: Expr[Prop]): Set[Expr[Prop]] =
    formula match
      case left /\ right => splitConjunctions(left) ++ splitConjunctions(right)
      case _ => Set(formula)

  /**
   * Adds formulas to the local assumption context and proves them by hypothesis.
   */
  def assume(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(formulas: Expr[Prop]*): Thm =
    proof.assume(formulas)
    if formulas.isEmpty then have(() |- ⊤) by BasicStep.RestateTrue
    else have(() |- formulas) by BasicStep.Hypothesis

  /**
   * Assumes every formula on the left of the current goal.
   */
  def assumeAll(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line): Thm =
    assume(thesis.left.toSeq*)

  /**
   * Assumes every formula on the left of the current goal, splitting conjunctions recursively.
   */
  def assumeAllSplit(using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line): Thm =
    assume(thesis.left.flatMap(splitConjunctions).toSeq*)

  /**
   * Concludes the current goal with a sorry step and records it in the proof.
   */
  inline def sorry(using library: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line): Thm =
    have(thesis) by BasicStep.Sorry

  /**
   * A tactic consuming only a previously proved theorem.
   */
  trait ThmTactic:
    def apply(using sourcecode.File, sourcecode.Line)(using Library)(premise: Thm): ProofJudgement

  /**
   * Helper for `andThen tactic`, where the tactic consumes the previous theorem.
   */
  final class AndThen private[prooflib] (using library: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line):
    private def missingPreviousStep: Thm =
      throw new InvalidProofOperationException("andThen requires a previous theorem in the local proof context.")

    /**
     * Applies a function tactic to the previous theorem and records the result.
     */
    infix def apply(tactic: Thm => ProofJudgement): Thm =
      proof.last match
        case Some(premise) => proof.absorbDestruct(tactic(premise))._1
        case None => missingPreviousStep

    /**
     * Applies an object tactic to the previous theorem and records the result.
     */
    infix def apply(tactic: ThmTactic): Thm =
      apply((premise: Thm) => tactic.apply(using file, line)(using library)(premise))

  /**
   * Starts an `andThen` proof step from the previous theorem.
   */
  def andThen(using library: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line): AndThen =
    AndThen()

  private def instantiate(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(thm: Thm, insts: Seq[SubstPair | Expr[Ind]]): Thm =
    val (terms, substitutions) = insts.partitionMap { argument =>
      if argument.isInstanceOf[Expr[?]] then Left(argument.asInstanceOf[Expr[Ind]])
      else Right(argument.asInstanceOf[SubstPair])
    }
    def checked(result: ProofJudgement): Thm =
      result match
        case ProofCarrier.Success(theorem, _) => theorem
        case ProofCarrier.Failure(message) => throw new InvalidProofOperationException(s"Cannot instantiate theorem:\n$message")

    val instance =
      if substitutions.isEmpty then thm
      else checked(BasicStep.InstSchema(substitutions*)(thm.kernel)(thm.statement.substitute(substitutions*)))

    if terms.isEmpty then instance
    else
      if instance.right.size != 1 then throw new InvalidProofOperationException("Quantified instantiation requires exactly one formula on the right.")
      val formula = terms.foldLeft(instance.right.head) {
        case (forall(variable, body), term) => body.substitute(variable := term)
        case (formula, _) => throw new InvalidProofOperationException(s"Cannot instantiate a non-universal formula: $formula")
      }
      checked(InstantiateForall(terms*)(instance.left |- formula, instance))

  extension (thm: K.Thm)
    /**
     * The theorem statement as a front sequent.
     */
    def frontStatement: Sequent =
      asFrontSequent(thm.statement)

    /**
     * Applies simultaneous schema substitutions, then instantiates leading universal quantifiers with the supplied terms.
     */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: (SubstPair | Expr[Ind])*): Thm =
      instantiate(Thm(thm), insts)

  extension (thm: Thm)
    /**
     * Applies simultaneous schema substitutions, then instantiates leading universal quantifiers with the supplied terms.
     */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: (SubstPair | Expr[Ind])*): Thm =
      instantiate(thm, insts)

  extension (theorem: Theorem)
    /**
     * Applies simultaneous schema substitutions, then instantiates leading universal quantifiers with the supplied terms.
     */
    infix def of(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(insts: (SubstPair | Expr[Ind])*): Thm =
      instantiate(theorem.thm, insts)

  extension (pj: ProofJudgement)
    /**
     * Take the first valid of two proof judgements. If both fail, the second is
     * returned.
     */
    infix def ||(other: => (ProofJudgement | Thm)): ProofJudgement =
      if pj.isValid then pj
      else
        other match
          case thm: Thm => ProofJudgement(thm)
          case judgement: ProofJudgement => judgement
