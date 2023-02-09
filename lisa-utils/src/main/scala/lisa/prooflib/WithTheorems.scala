package lisa.prooflib

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Cut
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.ProofTacticLib.UnimplementedProof
import lisa.prooflib.*
import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.parsing.UnreachableException

import scala.annotation.nowarn
import scala.collection.mutable.Buffer as mBuf
import scala.collection.mutable.Map as mMap
import scala.collection.mutable.Stack as stack

trait WithTheorems {
  library: Library =>
  /*
  sealed trait InstantiatedFact {
    val baseFormula: Sequent
    val instsConn: Map[SchematicConnectorLabel, LambdaFormulaFormula]
    val instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula]
    val instsTerm: Map[SchematicTermLabel, LambdaTermTerm]
    lazy val result: Sequent = instantiateSchemaInSequent(baseFormula, instsConn, instsPred, instsTerm)
  }

  case class InstantiatedJustification(
                                        just: theory.Justification,
                                        instsConn: Map[SchematicConnectorLabel, LambdaFormulaFormula],
                                        instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula],
                                        instsTerm: Map[SchematicTermLabel, LambdaTermTerm]) extends InstantiatedFact {
    val baseFormula: Sequent = theory.sequentFromJustification(just)
  }*/

  sealed abstract class Proof(assump: List[Formula]) {
    val possibleGoal: Option[Sequent]
    type SelfType = this.type
    type OutsideFact >: theory.Justification
    type Fact = ProofStep | InstantiatedFact | OutsideFact | Int

    case class InstantiatedFact(
        fact: Fact,
        instsConn: Map[SchematicConnectorLabel, LambdaFormulaFormula],
        instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula],
        instsTerm: Map[SchematicTermLabel, LambdaTermTerm]
    ) {
      val baseFormula: Sequent = sequentOfFact(fact)
      val result: Sequent = instantiateSchemaInSequent(baseFormula, instsConn, instsPred, instsTerm)
    }

    val library: WithTheorems.this.type = WithTheorems.this

    private var steps: List[ProofStep] = Nil
    private var imports: List[(OutsideFact, Sequent)] = Nil
    private var instantiatedFacts: List[(InstantiatedFact, Int)] = Nil
    private var assumptions: List[Formula] = assump
    private var discharges: List[Fact] = Nil

    def owningTheorem: THM

    case class ProofStep private (judgement: ValidProofTactic, scps: SCProofStep, position: Int) {
      def bot: Sequent = scps.bot
      val host: Proof.this.type = Proof.this

      def tactic: ProofTactic = judgement.tactic

    }
    private object ProofStep {
      def newProofStep(judgement: ValidProofTactic): ProofStep = {
        val ps = ProofStep(
          judgement,
          SC.SCSubproof(SCProof(judgement.scps.toIndexedSeq, judgement.imports.map(sequentOfFact).toIndexedSeq), judgement.imports.map(sequentAndIntOfFact(_)._2)),
          steps.length
        ) // TODO import the imports
        addStep(ps)
        ps

      }
    }
    def newProofStep(judgement: ValidProofTactic): ProofStep =
      ProofStep.newProofStep(judgement)

    private def addStep(ds: ProofStep): Unit = steps = ds :: steps
    private def addImport(imp: OutsideFact, seq: Sequent): Unit = {
      imports = (imp, seq) :: imports
    }

    private def addInstantiatedFact(instFact: InstantiatedFact): Unit = {
      val (_, i) = sequentAndIntOfFact(instFact.fact)
      newProofStep(BasicStepTactic.InstSchema(using library, this)(instFact.instsConn, instFact.instsPred, instFact.instsTerm)(i).asInstanceOf[ValidProofTactic])
      instantiatedFacts = (instFact, steps.length - 1) :: instantiatedFacts
    }

    def addAssumption(f: Formula): Unit = {
      if (!assumptions.contains(f)) assumptions = f :: assumptions
    }

    def addDischarge(ji: Fact): Unit = {
      if (!discharges.contains(ji)) discharges = ji :: discharges
    }

    // Getters

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

    def toSCProof: lisa.kernel.proof.SCProof = {
      discharges.foreach(i => { // TODO probably remove
        val (s, t1) = sequentAndIntOfFact(i)
        SC.Cut((mostRecentStep.bot -< s.right.head) ++ (s -> s.right.head), t1, steps.length - 1, s.right.head)
      })
      val finalSteps = discharges.foldLeft(steps.map(_.scps))((cumul, next) => {
        val (s, t1) = sequentAndIntOfFact(next)
        val lastStep = cumul.head
        val t2 = cumul.length - 1
        SC.Cut((lastStep.bot -< s.right.head) ++ (s -> s.right.head), t1, t2, s.right.head) :: cumul
      })

      SCProof(finalSteps.reverse.toIndexedSeq, getImports.map(of => of._2).toIndexedSeq)
    }

    def sequentAndIntOfFact(fact: Fact): (Sequent, Int) = fact match {
      case i: Int =>
        (
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
      case ds: ProofStep => (ds.bot, ds.position)
      case instFact: InstantiatedFact =>
        val r = instantiatedFacts.find(instFact == _._1)
        r match {
          case Some(value) => (instFact.result, value._2)
          case None =>
            addInstantiatedFact(instFact)
            (instFact.result, steps.length - 1)
        }
      case of: OutsideFact @unchecked =>
        val r = imports.indexWhere(of == _._1)
        if (r != -1) {
          (imports(r)._2, r - imports.length)
        } else {
          val r2 = sequentOfOutsideFact(of)
          addImport(of, r2)
          (r2, -imports.length)
        }
    }

    def sequentOfFact(fact: Fact): Sequent = fact match {
      case i: Int =>
        if (i >= 0)
          if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
          else steps(steps.length - i - 1).bot
        else {
          val i2 = -(i + 1)
          if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
          else imports(imports.length + i)._2
        }
      case ds: ProofStep => ds.bot
      case instfact: InstantiatedFact => instfact.result
      case of: OutsideFact @unchecked =>
        val r = imports.find(of == _._1)
        if (r.nonEmpty) {
          r.get._2
        } else {
          sequentOfOutsideFact(of)
        }
    }

    def sequentOfOutsideFact(of: OutsideFact): Sequent

    def getSequent(f: Fact): Sequent = sequentOfFact(f)
    def mostRecentStep: ProofStep = steps.head

    def length: Int = steps.length

    def lockedSymbols: Set[SchematicLabel] = assumptions.toSet.flatMap(f => f.schematicFormulaLabels.toSet[SchematicLabel] ++ f.schematicTermLabels.toSet[SchematicLabel])

    def asOutsideFact(j: theory.Justification): OutsideFact

    @nowarn("msg=.*It would fail on pattern case: _: InnerProof.*")
    def depth: Int = this match {
      case p: Proof#InnerProof => 1 + p.parent.depth
      case _: BaseProof => 0
    }

    final class InnerProof(val possibleGoal: Option[Sequent]) extends Proof(this.getAssumptions) {
      val parent: Proof.this.type = Proof.this
      val owningTheorem: THM = parent.owningTheorem
      type OutsideFact = parent.Fact
      override inline def asOutsideFact(j: theory.Justification): OutsideFact = parent.asOutsideFact(j)

      override def sequentOfOutsideFact(of: parent.Fact): Sequent = of match {
        case j: theory.Justification => theory.sequentFromJustification(j)
        case ds: Proof#ProofStep => ds.bot
        case _ => parent.sequentOfFact(of)
      }
    }

    /**
     * Contains the result of a tactic computing a SCProofTactic.
     * Can be successful or unsuccessful.
     */
    sealed abstract class ProofTacticJudgement {
      val tactic: ProofTactic
      val proof: Proof = Proof.this

      /**
       * Returns true if and only if the judgement is valid.
       */
      def isValid: Boolean = this match {
        case ValidProofTactic(_, _) => true
        case InvalidProofTactic(_) => false
      }

      def validate(line: sourcecode.Line, file: sourcecode.File): ProofStep = {
        this match {
          case vpt: ValidProofTactic => newProofStep(vpt)
          case ipt: InvalidProofTactic =>
            val e = lisa.prooflib.ProofTacticLib.UnapplicableProofTactic(ipt.tactic, ipt.proof, ipt.message)(using line, file)
            e.setStackTrace(ipt.stack)
            throw e
        }
      }
    }

    /**
     * A Sequent Calculus proof step that has been correctly produced.
     */
    case class ValidProofTactic(scps: Seq[SCProofStep], imports: Seq[Fact])(using val tactic: ProofTactic) extends ProofTacticJudgement {}

    /**
     * A proof step which led to an error when computing the corresponding Sequent Calculus proof step.
     */
    case class InvalidProofTactic(message: String)(using val tactic: ProofTactic) extends ProofTacticJudgement {
      private val nstack = Throwable()
      val stack: Array[StackTraceElement] = nstack.getStackTrace.drop(2)
    }
  }

  sealed class BaseProof(val owningTheorem: THM) extends Proof(Nil) {
    val possibleGoal: Option[Sequent] = Some(owningTheorem.goal)
    val goal: Sequent = owningTheorem.goal
    type OutsideFact = theory.Justification
    override inline def asOutsideFact(j: theory.Justification): OutsideFact = j

    override def sequentOfOutsideFact(of: theory.Justification): Sequent = theory.sequentFromJustification(of)
  }

  sealed abstract class DefOrThm(using om: OutputManager)(val line: Int, val file: String)
  class THM(using om: OutputManager)(statement: Sequent | String, val fullName: String, line: Int, file: String)(computeProof: Proof ?=> Unit) extends DefOrThm(using om)(line, file) {

    val goal: Sequent = statement match {
      case s: Sequent => s
      case s: String => lisa.utils.FOLParser.parseSequent(s)
    }
    val name: String = fullName

    val proof: BaseProof = new BaseProof(this)
    val innerThm: theory.Theorem = show(computeProof)

    def repr: String = (
      " Theorem " + name + " := " + (statement match {
        case s: Sequent => lisa.utils.FOLPrinter.prettySequent(s)
        case s: String => s
      })
    )

    def show(computeProof: Proof ?=> Unit): theory.Theorem = {
      try {
        computeProof(using proof)
      } catch {
        case e: NotImplementedError =>
          om.lisaThrow(new UnimplementedProof(this))
        case e: UserLisaException =>
          om.lisaThrow(e)
      }

      if (proof.length == 0)
        om.lisaThrow(new UnimplementedProof(this))

      val r = TheoremNameWithProof(name, goal, proof.toSCProof)
      theory.theorem(r.name, r.statement, r.proof, proof.getImports.map(_._1)) match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          library.last = Some(just)
          just
        case wrongJudgement: RunningTheoryJudgement.InvalidJustification[?] =>
          om.lisaThrow(
            LisaException.InvalidKernelJustificationComputation(
              "The final proof was rejected by LISA's logical kernel. This may be due to a faulty proof computation or lack of verification by a proof tactic.",
              wrongJudgement,
              Some(proof)
            )
          )
      }
    }
  }

  given thmConv: Conversion[library.THM, theory.Theorem] = _.innerThm

}
