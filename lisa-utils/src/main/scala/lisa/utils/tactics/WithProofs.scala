package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.Library
import lisa.utils.OutputManager
import lisa.utils.tactics.ProofStepJudgement.EarlyProofStepException
import lisa.utils.tactics.ProofStepJudgement.InvalidProofStep
import lisa.utils.tactics.ProofStepJudgement.ValidProofStep
import lisa.utils.tactics.ProofStepLib.ProofStep

import scala.collection.mutable.Buffer as mBuf
import scala.collection.mutable.Map as mMap

trait WithProofs extends ProofsHelpers {
  library: Library =>

  class Proof(assumpts: List[Formula] = Nil) {
    type OutsideFact = (theory.Justification | Proof#DoubleStep)
    // Maintaining the current state of the proof if an imperative environment //
    private val that: Proof = this
    private var steps: List[DoubleStep] = Nil
    private var imports: List[ImportedFact] = Nil
    private var assumptions: List[Formula] = assumpts
    private var discharges: List[Fact] = Nil

    private val justMap: mMap[OutsideFact, ImportedFact] = mMap()

    private val parent: Option[Proof] = if (proofStack.isEmpty) None else Some(proofStack(0))

    /**
     * A step that has been added to a proof and its equivalent in pure sequent calculus.
     */
    case class DoubleStep private (ps: ProofStep, scps: SCProofStep, position: Int) {
      val bot: Sequent = scps.bot
    }

    /**
     * An import (theorem, axiom or definition) that has been added to the current proof.
     */
    case class ImportedFact private (of: OutsideFact, seq: Sequent, position: Int, reference: Int | theory.Justification) {}

    /**
     * The type of object which can be used as premises of proofsteps, similar to integers in pure sequent calculus.
     */
    type Fact = DoubleStep | OutsideFact | ImportedFact | Int

    private def addStep(ds: DoubleStep): Unit = steps = ds :: steps
    private def addImport(ji: ImportedFact): Unit = {
      justMap.update(ji.of, ji)
      imports = ji :: imports
    }

    //  Setters  //

    /**
     * @param f add the formula f as an assumption on the left handsides of all further (manually written) proofsteps in the proof.
     */
    def addAssumption(f: Formula): Unit = {
      if (!assumptions.contains(f)) assumptions = f :: assumptions
    }

    /**
     * @param ji Automatically discharge (by applying Cut rule) the given justification at the end of the proof.
     */
    def addDischarge(ji: Fact): Unit = {
      if (!discharges.contains(ji)) discharges = ji :: discharges
    }

    private object DoubleStep {
      def newDoubleStep(ps: ProofStep)(using om: OutputManager): DoubleStep = {
        val judgement = ps.asSCProof(that)
        judgement match {
          case ValidProofStep(scps) =>
            val ds = DoubleStep(ps, scps, steps.length)
            addStep(ds)
            ds
          case InvalidProofStep(ps, message) =>
            om.output(s"$message\n")
            om.finishOutput(EarlyProofStepException(message))
        }
      }
    }

    /**
     * Add a new proof step to the proof
     */
    def newDoubleStep(ps: ProofStep)(using om: OutputManager): DoubleStep =
      DoubleStep.newDoubleStep(ps: ProofStep)

    private object ImportedFact {
      def newImportedFact(outFact: OutsideFact): ImportedFact = {
        if (parent.isEmpty) {
          outFact match {
            case just: theory.Justification =>
              val imf: ImportedFact = ImportedFact(outFact, theory.sequentFromJustification(just), -(imports.length + 1), just)
              addImport(imf)
              imf
            case ds: Proof#DoubleStep => throw InvalidJustificationException(ds)
          }
        } else {
          val (seq, ref) = parent.get.getSequentAndInt(outFact)
          val imf: ImportedFact = ImportedFact(outFact, seq, -(imports.length + 1), ref)
          addImport(imf)
          imf
        }
      }
    }

    /**
     * Add a new import to the proof.
     */
    def newImportedFact(just: theory.Justification): ImportedFact = ImportedFact.newImportedFact(just)

    //  Getters  //

    /**
     * Favour using getSequent when applicable.
     * @return The list of ValidatedSteps (containing a high level ProofStep and the corresponding SCProofStep).
     */
    def getSteps: List[DoubleStep] = steps.reverse

    /**
     * Favour using getSequent when applicable.
     * @return The list of Imports validated in the formula, with their original justification.
     */
    def getImports: List[ImportedFact] = imports.reverse

    /**
     * @return The list of formulas that are assumed for the reminder of the proof.
     */
    def getAssumptions: List[Formula] = assumptions

    /**
     * @return The list of Formula, typically proved by outer theorems or axioms that will get discharged in the end of the proof.
     */
    def getDischarges: List[Fact] = discharges

    /**
     * Tell if a justification for a ProofStep (an Index, and ProofStep, a theory Justification) is usable in the current proof
     */
    def validInThisProof(ij: Library#Proof#Fact): Boolean = ij match {
      case ds: library.Proof#DoubleStep => ds.isInstanceOf[this.DoubleStep] || (parent.nonEmpty && parent.get.validInThisProof(ij))
      case ji: library.Proof#ImportedFact => ji.isInstanceOf[this.ImportedFact] || (parent.nonEmpty && parent.get.validInThisProof(ij))
      case _: Int => true
      case _: theory.Justification => true
      case _ => false
    }

    /**
     * Tell if a justification for a ProofStep (ad ProofStep, a theory Justification) is usable in the current proof
     */
    def validInThisProof(ji: Library#Proof#ImportedFact): Boolean = validInThisProof(ji.asInstanceOf[Library#Proof#Fact])

    /**
     * Tell if a justification for a ProofStep (ad ProofStep, a theory Justification) is usable in the current proof
     */
    def validInThisProof(ds: Library#Proof#DoubleStep): Boolean = validInThisProof(ds.asInstanceOf[Library#Proof#Fact])

    /**
     * Compute the final, Kernel-pure, SCProof.
     */
    def toSCProof(using om: OutputManager): lisa.kernel.proof.SCProof = {
      discharges.foreach(i => Discharge(getSequentAndInt(i)._2))
      SCProof(steps.reverse.map(_.scps).toIndexedSeq, imports.reverse.map(_.seq).toIndexedSeq)
    }

    /**
     * Return the Sequent that a given justification proves as well as it's integer position in the steps or imports lists.
     */
    def getSequentAndInt(ij: Fact): (Sequent, Int) = {
      ij match {
        case ds: DoubleStep =>
          (ds.bot, ds.position)
        case ds: Proof#DoubleStep if parent.nonEmpty && parent.get.validInThisProof(ds) =>
          val r = justMap.get(ds)
          r match {
            case Some(importedFact) => getSequentAndInt(importedFact)
            case None =>
              getSequentAndInt(ImportedFact.newImportedFact(ds))
          }
        case ds: Proof#DoubleStep => throw InvalidJustificationException(ds)
        case just: theory.Justification =>
          val r = justMap.get(just)
          r match {
            case Some(ji) => getSequentAndInt(ji)
            case None =>
              if (parent.isEmpty) getSequentAndInt(ImportedFact.newImportedFact(just))
              else {
                val i = parent.get.getSequentAndInt(just)
                getSequentAndInt(ImportedFact.newImportedFact(just))
              }
          }
        case ji: ImportedFact =>
          (ji.seq, ji.position)
        case i: Int =>
          (
            if (i >= 0)
              if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
              else steps(steps.length - i - 1).bot
            else {
              val i2 = -(i + 1)
              if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
              else imports(imports.length + i).seq
            },
            i
          )
      }
    }

    /**
     * Create a new proof with this proof as parent, execute the given code and then close the created proof (i.e. remove it from the proofstack).
     */
    def subproof(proofAction: => Unit): Proof = {
      assert(proofStack.head == this, "Can only create a subproof in the latest opened Proof.")
      val p = new Proof(getAssumptions)
      proofStack.push(p)
      proofAction
      proofStack.pop
    }

    /**
     * Return the Sequent that a given justification proves in the proof.
     */
    def getSequent(ij: Fact): Sequent = getSequentAndInt(ij)._1

    /**
     * @return the most recently added proofstep.
     */
    def mostRecentStep: (DoubleStep, Int) = (steps.head, steps.length - 1)

    /**
     * @return Current number of steps in the proof.
     */
    def length: Int = steps.length

    /**
     * @return a Set of symbols free in the assumption and which shouldn't be bound or instantiated.
     */
    def lockedSymbols: Set[SchematicLabel] = assumptions.toSet.flatMap(f => f.schematicFormulaLabels.toSet[SchematicLabel] ++ f.schematicTermLabels.toSet[SchematicLabel])

    /**
     * @return The sequent and integer position of a justification in the proof. Alias for [[getSequentAndInt]]
     */
    def references(ij: Fact): (Sequent, Int) = getSequentAndInt(ij)

  }

  /**
   * An error indicating that a given proof step was used in a proof while it does not belong to it or its parents.
   */
  case class InvalidJustificationException(ds: Proof#DoubleStep) extends Exception("Reference to a step that does not belong to the current proof or on of its parents.")

}
