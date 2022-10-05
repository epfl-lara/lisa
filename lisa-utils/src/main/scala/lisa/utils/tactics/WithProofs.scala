package lisa.utils.tactics

import lisa.kernel.proof.{RunningTheory, SCProof}
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.fol.FOL.*
import lisa.utils.Library
import lisa.utils.tactics.ProofStepJudgement.{EarlyProofStepException, InvalidProofStep, ValidProofStep}
import lisa.utils.tactics.ProofStepLib.ProofStep

import scala.collection.mutable.Buffer as mBuf
import scala.collection.mutable.Map as mMap

trait WithProofs extends ProofsHelpers {
  library: Library =>


  case class Proof(assumpts:List[Formula] = Nil) {

    val that: Proof = this
    var steps: List[DoubleStep] = Nil
    var imports: List[JustifiedImport] = Nil
    var assumptions:List[Formula] = assumpts

    private val justMap: mMap[theory.Justification, JustifiedImport] = mMap()

    case class DoubleStep private(ps:ProofStep, scps:SCProofStep){
      def _1: ProofStep = ps
      def _2: SCProofStep = scps
    }

    case class JustifiedImport(just:theory.Justification, seq:Sequent) {
      def _1: Sequent = seq
      def _2: theory.Justification = just
    }

    type InnerJustification = DoubleStep | theory.Justification | JustifiedImport | Int

    private def addStep(ds:DoubleStep):Unit = steps = ds::steps
    private def addImport(ji:JustifiedImport):Unit = {
      justMap.update(ji.just, ji)
      imports= ji::imports
    }





    //  Setters  //

    def addAssumption(f:Formula):Unit = {
      if (!assumptions.contains(f)) assumptions = f::assumptions
    }

    object DoubleStep {
      def newDoubleStep(ps:ProofStep)(using output: String => Unit)(using finishOutput: Throwable => Nothing): DoubleStep = {
        val references: Int => Sequent = getSequent
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

    def apply(i: Int): DoubleStep = {
      if (i >= 0)
        if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
        else steps(steps.length-i-1)
      else throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
    }

    def toSCProof: (lisa.kernel.proof.SCProof) = {
      SCProof(steps.map(_._2).reverse.toIndexedSeq, imports.map(_._1).toIndexedSeq)
    }

    def getSequent(ij: InnerJustification): Sequent = {
      ij match {
        case DoubleStep(ps, scps) => scps.bot
        case j: theory.Justification => justMap(j).seq //TODO what if not present? Can it be?
        case JustifiedImport(seq, just) => seq
        case i:Int =>
          if (i >= 0)
            if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
            else steps(steps.length-i-1)._2.bot
          else{
            val i2 = -(i + 1)
            if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
            else imports(imports.length+i)._1
          }
      }
    }

    def length: Int = steps.length
    def lockedSymbols: Set[SchematicLabel] = assumptions.toSet.flatMap(f => f.schematicFormulaLabels.toSet[SchematicLabel] ++ f.schematicTermLabels.toSet[SchematicLabel])
    def assumed: Set[Formula] = assumptions.toSet
    val references: InnerJustification => Sequent = getSequent

  }

  object Proof {

    def empty: Proof = Proof()

  }


}
