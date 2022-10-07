package lisa.utils.tactics

import lisa.kernel.proof.{RunningTheory, SCProof}
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.fol.FOL.*
import lisa.utils.Library
import lisa.utils.tactics.ProofStepJudgement.{EarlyProofStepException, InvalidProofStep, ValidProofStep}
import lisa.utils.tactics.ProofStepLib.{Prev, ProofStep, SecondPrev, Index}

import scala.collection.mutable.Buffer as mBuf
import scala.collection.mutable.Map as mMap

trait WithProofs extends ProofsHelpers {
  library: Library =>


  class Proof(assumpts:List[Formula] = Nil) {

    // Maintaining the current state of the proof if an imperatice environment //
    private val that: Proof = this
    private var steps: List[DoubleStep] = Nil
    private var imports: List[JustifiedImport] = Nil
    private var assumptions: List[Formula] = assumpts
    private var discharges: List[Int] = Nil

    private val justMap: mMap[theory.Justification, JustifiedImport] = mMap()

    case class DoubleStep private(ps:ProofStep, scps:SCProofStep){
      def _1: ProofStep = ps
      def _2: SCProofStep = scps
    }

    case class JustifiedImport(just:theory.Justification, seq:Sequent) {
      def _1: Sequent = seq
      def _2: theory.Justification = just
    }

    type InnerJustification = DoubleStep | theory.Justification | JustifiedImport | Index

    private def addStep(ds:DoubleStep):Unit = steps = ds::steps
    private def addImport(ji:JustifiedImport):Unit = {
      justMap.update(ji.just, ji)
      imports= ji::imports
    }





    //  Setters  //

    def addAssumption(f:Formula):Unit = {
      if (!assumptions.contains(f)) assumptions = f::assumptions
    }
    def addDischarge(i:Int):Unit = {
      if (!discharges.contains(i)) discharges = i::discharges
    }
    def addDischarge(ji:InnerJustification):Unit = {
      val i = getSequentAndInt(ji)._2
      addDischarge(i)
    }

    object DoubleStep {
      def newDoubleStep(ps:ProofStep)(using output: String => Unit)(using finishOutput: Throwable => Nothing): DoubleStep = {
        val judgement = ps.asSCProofStep(that)
        judgement match {
          case ValidProofStep(scps) =>
            val ds = DoubleStep(ps, scps)
            addStep(ds)
            ds
          case InvalidProofStep(ps, message) =>
            output(s"$message\n")
            finishOutput(EarlyProofStepException(message))
        }
      }
    }

    object JustifiedImport {
      def newJustifiedImport(just:theory.Justification): JustifiedImport = {
        val ji : JustifiedImport = JustifiedImport(just, theory.sequentFromJustification(just))
        addImport(ji)
        ji
      }
    }


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
    def getImports: List[JustifiedImport] = imports
    /**
     * @return The list of formulas that are assumed for the reminder of the proof.
     */
    def getAssumptions: List[Formula] = assumptions
    /**
     * @return The list of Formula, typically proved by outer theorems or axioms that will get discharged in the end of the proof.
     */
    def getDischarges: List[Int] = discharges

    /**
     * Tell if a justification for a ProofStep (an Index, and ProofStep, a theory Justification) is usable in the current proof
     */
    def validInThisProof(ij:Library#Proof#InnerJustification): Boolean = ij match {
      case ds: library.Proof#DoubleStep => ds.isInstanceOf[this.DoubleStep]
      case ji: library.Proof#JustifiedImport => ji.isInstanceOf[this.JustifiedImport]
      case _: Int => true
      case _: Index => true
      case _: theory.Justification => true
      case _ => false
    }
    /**
     * Tell if a justification for a ProofStep (an Index, and ProofStep, a theory Justification) is usable in the current proof
     */
    def validInThisProof(ji:Library#Proof#JustifiedImport): Boolean = ji.isInstanceOf[this.JustifiedImport]
    /**
     * Tell if a justification for a ProofStep (an Index, and ProofStep, a theory Justification) is usable in the current proof
     */
    def validInThisProof(ds:Library#Proof#DoubleStep): Boolean = ds.isInstanceOf[this.DoubleStep]


    /**
     * Compute the final, Kernel-pure, SCProof.
     */
    def toSCProof(using String => Unit)(using finishOutput: Throwable => Nothing): (lisa.kernel.proof.SCProof) = {
      discharges.foreach(i => Discharge(i))
      SCProof(steps.map(_._2).reverse.toIndexedSeq, imports.map(_._1).toIndexedSeq)
    }

    /**
     * Return the Sequent that a given justification proves as well as it's integer position in the steps or imports lists.
     */
    def getSequentAndInt(ij: InnerJustification): (Sequent, Int) = {
      ij match {
        case ds: DoubleStep =>
          val (sq, i) = (ds.scps.bot, steps.indexOf(ds))
          (sq, steps.length-i-1)
        case just: theory.Justification =>
          val r = justMap.get(just)
          r match {
            case Some(ji) => getSequentAndInt(ji)
            case None =>
              getSequentAndInt(JustifiedImport.newJustifiedImport(just))
          }
        case ji: JustifiedImport =>
          val (sq, i) = (ji.seq, imports.indexOf(ji))
          (sq, -i-1)
        case Prev => getSequentAndInt(steps.length-1)
        case SecondPrev => getSequentAndInt(steps.length-2)
        case i:Int =>
          (if (i >= 0)
            if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
            else steps(steps.length-i-1)._2.bot
          else{
            val i2 = -(i + 1)
            if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
            else imports(imports.length+i)._1
          }
            , i)
      }
    }
    /**
     * Return the Sequent that a given justification proves in the proof.
     */
    def getSequent(ij: InnerJustification):  Sequent = {
      ij match {
        case ds: DoubleStep => ds.scps.bot
        case just: theory.Justification =>
          val r = justMap.get(just)
          r match {
            case Some(ji) => getSequent(ji)
            case None =>
              getSequent(JustifiedImport.newJustifiedImport(just))
          }
        case ji: JustifiedImport => ji.seq
        case Prev => getSequent(steps.length-1)
        case SecondPrev => getSequent(steps.length-2)
        case i:Int =>
          if (i >= 0)
            if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
            else steps(steps.length-i-1)._2.bot
          else{
            val i2 = -(i + 1)
            if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
            else imports(i2)._1
          }
      }
    }

    /**
     * @return the most recently added proofstep.
     */
    def mostRecentStep: (DoubleStep, Int) = (steps.head, steps.length-1)
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
    def references(ij: InnerJustification): (Sequent, Int) = getSequentAndInt(ij)

  }


}
