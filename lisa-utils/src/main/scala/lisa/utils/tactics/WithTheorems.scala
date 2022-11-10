package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.{RunningTheory, RunningTheoryJudgement, SCProof}
import lisa.kernel.proof.SequentCalculus.{Cut, Sequent}
import lisa.utils.{Library, OutputManager}
import lisa.utils.tactics.ProofTacticJudgement.EarlyProofTacticException
import lisa.utils.tactics.ProofTacticJudgement.InvalidProofTactic
import lisa.utils.tactics.ProofTacticJudgement.ValidProofTactic
import lisa.utils.tactics.ProofTacticLib.ProofTactic
import lisa.utils.LisaException

import scala.collection.mutable.Buffer as mBuf
import scala.collection.mutable.Map as mMap
import scala.collection.mutable.Stack as stack
import scala.annotation.nowarn

trait WithTheorems {
  library: Library =>

  sealed abstract class Proof(assump: List[Formula]) {
    val goal:Sequent
    type SelfType = this.type
    type OutsideFact

    private val that: this.type = this
    private var steps: List[ProofStep] = Nil
    private var imports: List[(OutsideFact, Sequent)] = Nil
    private var assumptions: List[Formula] = assump
    private var discharges: List[Fact] = Nil

    case class ProofStep private(ps: ProofTactic{val proof: SelfType}, scps: SCProofStep, position: Int) {
      val bot: Sequent = scps.bot
    }
    private object ProofStep {
      def newProofStep(ps: ProofTactic{val proof: SelfType})(using om:OutputManager): ProofStep = {
        val judgement = ps.asSCProof(sequentAndIntOfFact(_)._2)
        judgement match {
          case ValidProofTactic(scps) =>
            val ds = ProofStep(ps, scps, steps.length)
            addStep(ds)
            ds
          case InvalidProofTactic(ps, message) =>
            om.output(s"$message\n")
            om.finishOutput(EarlyProofTacticException(message))
        }
      }
    }
    def newProofStep(ps: ProofTactic{val proof: SelfType})(using om:OutputManager): ProofStep =
      ProofStep.newProofStep(ps)


    type Fact = ProofStep | OutsideFact | Int

    private def addStep(ds: ProofStep): Unit = steps = ds :: steps
    private def addImport(imp: OutsideFact, seq: Sequent): Unit = {
      imports = (imp, seq):: imports
    }

    def addAssumption(f: Formula): Unit = {
      if (!assumptions.contains(f)) assumptions = f :: assumptions
    }

    def addDischarge(ji: Fact): Unit = {
      if (!discharges.contains(ji)) discharges = ji :: discharges
    }


    //Getters

    /**
     * Favour using getSequent when applicable.
     * @return The list of ValidatedSteps (containing a high level ProofTactic and the corresponding SCProofStep).
     */
    def getSteps: List[ProofStep] = steps.reverse

    /**
     * Favour using getSequent when applicable.
     * @return The list of Imports validated in the formula, with their original justification.
     */
    def getImports: List[(OutsideFact, Sequent)] = imports.reverse

    /**
     * @return The list of formulas that are assumed for the reminder of the proof.
     */
    def getAssumptions: List[Formula] = assumptions

    /**
     * @return The list of Formula, typically proved by outer theorems or axioms that will get discharged in the end of the proof.
     */
    def getDischarges: List[Fact] = discharges

    def toSCProof(using om:OutputManager): lisa.kernel.proof.SCProof = {
      discharges.foreach(i => {
        val (s, t1) = sequentAndIntOfFact(i)
        val (lastStep, t2) = mostRecentStep
        SC.Cut((lastStep.bot -< s.right.head) ++ (s -> s.right.head), t1, t2, s.right.head)
      })
      val finalSteps = discharges.foldLeft(steps.map(_.scps))((cumul, next) => {
        val (s, t1) = sequentAndIntOfFact(next)
        val lastStep = cumul.head
        val t2 = cumul.length-1
        SC.Cut((lastStep.bot -< s.right.head) ++ (s -> s.right.head), t1, t2, s.right.head)::cumul
      })


      SCProof(finalSteps.reverse.toIndexedSeq, getImports.map(of => of._2).toIndexedSeq)
    }

    def sequentAndIntOfFact(fact:Fact): (Sequent, Int) = fact match {
      case i:Int => (
          if (i >= 0)
            if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
            else steps(steps.length - i - 1).bot
          else {
            val i2 = -(i + 1)
            if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
            else imports(imports.length + i)._2
          },
          i
      )
      case ds:ProofStep => (ds.bot, ds.position)
      case of: OutsideFact @unchecked =>
        val r = imports.indexWhere(of == _._1)
        if (r != -1){
          (imports(r)._2, r-imports.length)
        }
        else {
          val r2 = sequentOfOutsideFact(of)
          addImport(of, r2)
          (r2, -imports.length)
        }
    }

    def sequentOfFact(fact: Fact): Sequent = fact match {
      case i:Int =>
          if (i >= 0)
            if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
            else steps(steps.length - i - 1).bot
          else {
            val i2 = -(i + 1)
            if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
            else imports(imports.length + i)._2
          }
      case ds:ProofStep => ds.bot
      case of:OutsideFact @unchecked =>
        val r = imports.find(of == _._1)
        if (r.nonEmpty){
          r.get._2
        }
        else {
          sequentOfOutsideFact(of)
        }
    }

    def sequentOfOutsideFact(of:OutsideFact): Sequent


    def getSequent(f:Fact):Sequent = sequentOfFact(f)
    def mostRecentStep: (ProofStep, Int) = (steps.head, steps.length - 1)

    def length:Int = steps.length

    def lockedSymbols: Set[SchematicLabel] = assumptions.toSet.flatMap(f => f.schematicFormulaLabels.toSet[SchematicLabel] ++ f.schematicTermLabels.toSet[SchematicLabel])

    def asOutsideFact(j:theory.Justification) : OutsideFact


    final class InnerProof (val goal:Sequent) extends Proof(this.getAssumptions) {
      val parent: Proof.this.type = Proof.this
      type OutsideFact = parent.Fact
      override def asOutsideFact(j:theory.Justification): OutsideFact = parent.asOutsideFact(j)

      override def sequentOfOutsideFact(of: parent.Fact): Sequent = of match {
        case j: theory.Justification => theory.sequentFromJustification(j)
        case ds:Proof#ProofStep => ds.bot
        case _ => parent.sequentOfFact(of)
      }
    }
  }

  sealed class BaseProof(val goal:Sequent) extends Proof(Nil) {

    type OutsideFact = theory.Justification
    override def asOutsideFact(j:theory.Justification): OutsideFact = j



    override def sequentOfOutsideFact(of: theory.Justification): Sequent = theory.sequentFromJustification(of)
  }



  class THM (using om:OutputManager)(statement: Sequent | String, val fullName:String, val line:Int, val file:String)(computeProof: Proof ?=> Unit){

    val goal:Sequent = statement match {
      case s: Sequent => s
      case s: String => lisa.utils.Parser.parseSequent(s)
    }
    val name:String = fullName


    val proof:BaseProof = new BaseProof(goal)
    val innerThm: theory.Theorem = show(computeProof)

    def show(computeProof: Proof ?=> Unit): theory.Theorem = {
      try {
        given Proof = proof
        computeProof
      } catch {
        case e: NotImplementedError => om.lisaThrow(new LisaException.EmptyProofException("Closed empty proof."))
        case e: LisaException.ParsingException => om.lisaThrow(e)
        case e: LisaException.FaultyProofTacticException => om.lisaThrow(e)
        case e: LisaException => om.lisaThrow(e)
      }

      if (proof.length == 0)
        om.lisaThrow(new LisaException.EmptyProofException("Closed empty proof."))

      val r = TheoremNameWithProof(name, goal, proof.toSCProof)
      val r2 = theory.theorem(r.name, r.statement, r.proof, proof.getImports.map(_._1)) match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          library.last = Some(just)
          just
        case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
          om.finishOutput(LisaException.InvalidKernelJustificationComputation("The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or lack of verification by a proof tactic.", wrongJudgement))
      }
      library.last = Some(r2)
      r2
    }
  }

  def makeVar(using name: sourcecode.FullName) : VariableLabel = VariableLabel(name.value)

  def makeTHM(using om:OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(statement: Sequent | String)(computeProof: Proof ?=> Unit): THM = new THM(statement, name.value, line.value, file.value)(computeProof) {}

}
