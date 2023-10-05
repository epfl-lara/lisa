package lisa.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.ProofTacticLib.UnimplementedProof
import lisa.prooflib.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.UserLisaException.*
import lisa.utils.parsing.UnreachableException

import scala.annotation.nowarn
import scala.collection.mutable.Buffer as mBuf
import scala.collection.mutable.Map as mMap
import scala.collection.mutable.Stack as stack

trait WithTheorems {
  library: Library =>

  sealed abstract class Proof(assump: List[F.Formula]) {
    val possibleGoal: Option[F.Sequent]
    type SelfType = this.type
    type OutsideFact >: JUSTIFICATION
    type Fact = ProofStep | InstantiatedFact | OutsideFact | Int

    case class InstantiatedFact(
        fact: Fact,
        insts: Seq[F.SubstPair] /*,
        instsConn: Map[K.SchematicConnectorLabel, K.LambdaFormulaFormula],
        instsPred: Map[K.SchematicVarOrPredLabel, K.LambdaTermFormula],
        instsTerm: Map[K.SchematicTermLabel, K.LambdaTermTerm]*/
    ) {
      val baseFormula: F.Sequent = sequentOfFact(fact)
      val result: F.Sequent = baseFormula.substitute(insts*)

    }

    val library: WithTheorems.this.type = WithTheorems.this

    private var steps: List[ProofStep] = Nil
    private var imports: List[(OutsideFact, F.Sequent)] = Nil
    private var instantiatedFacts: List[(InstantiatedFact, Int)] = Nil
    private var assumptions: List[F.Formula] = assump
    private var discharges: List[Fact] = Nil

    def owningTheorem: THM

    case class ProofStep private (judgement: ValidProofTactic, scps: K.SCProofStep, position: Int) {
      val bot: F.Sequent = judgement.bot
      def innerBot: K.Sequent = scps.bot
      val host: Proof.this.type = Proof.this

      def tactic: ProofTactic = judgement.tactic

    }
    private object ProofStep { // TODO
      def newProofStep(judgement: ValidProofTactic): ProofStep = {
        val ps = ProofStep(
          judgement,
          SC.SCSubproof(
            K.SCProof(judgement.scps.toIndexedSeq, judgement.imports.map(f => sequentOfFact(f).underlying).toIndexedSeq),
            judgement.imports.map(sequentAndIntOfFact(_)._2)
          ),
          steps.length
        )
        addStep(ps)
        ps

      }
    }
    def newProofStep(judgement: ValidProofTactic): ProofStep =
      ProofStep.newProofStep(judgement)

    private def addStep(ds: ProofStep): Unit = steps = ds :: steps
    private def addImport(imp: OutsideFact, seq: F.Sequent): Unit = {
      imports = (imp, seq) :: imports
    }

    private def addInstantiatedFact(instFact: InstantiatedFact): Unit = {
      val (s, i) = sequentAndIntOfFact(instFact.fact)
      // newProofStep(BasicStepTactic.InstSchema(using library, this)(instFact.instsConn, instFact.instsPred, instFact.instsTerm)(i).asInstanceOf[ValidProofTactic])
      // newProofStep(BasicStepTactic.InstSchema(using library, this)(instFact.insts)(i).asInstanceOf[ValidProofTactic])
      val instMap = Map(instFact.insts.map(s => (s._1, (s._2.asInstanceOf: F.LisaObject[_])))*)
      val instStep = {
        val res = s.substituteWithProof(instMap)

        ValidProofTactic(res._1, res._2, Seq(instFact.fact))(using F.SequentInstantiationRule)
      }
      newProofStep(instStep)
      instantiatedFacts = (instFact, steps.length - 1) :: instantiatedFacts
    }

    def addAssumption(f: F.Formula): Unit = {
      if (!assumptions.contains(f)) assumptions = f :: assumptions
    }

    def addDischarge(ji: Fact): Unit = {
      if (!discharges.contains(ji)) discharges = ji :: discharges
    }

    // Getters

    /**
     * Favour using getSequent when applicable.
     * @return The list of ValidatedSteps (containing a high level ProofTactic and the corresponding K.SCProofStep).
     */
    def getSteps: List[ProofStep] = steps.reverse

    /**
     * Favour using getSequent when applicable.
     * @return The list of Imports validated in the formula, with their original justification.
     */
    def getImports: List[(OutsideFact, F.Sequent)] = imports.reverse

    /**
     * @return The list of formulas that are assumed for the reminder of the proof.
     */
    def getAssumptions: List[F.Formula] = assumptions

    /**
     * @return The list of Formula, typically proved by outer theorems or axioms that will get discharged in the end of the proof.
     */
    def getDischarges: List[Fact] = discharges

    def toSCProof: K.SCProof = {
      import lisa.utils.KernelHelpers.{-<<, ->>}
      val finalSteps = discharges.foldLeft(steps.map(_.scps))((cumul, next) => {
        val (s1, t1) = sequentAndIntOfFact(next)
        val s = s1.underlying
        val lastStep = cumul.head
        val t2 = cumul.length - 1
        SC.Cut((lastStep.bot -<< s.right.head) ++ (s ->> s.right.head), t1, t2, s.right.head) :: cumul
      })

      K.SCProof(finalSteps.reverse.toIndexedSeq, getImports.map(of => of._2.underlying).toIndexedSeq)
    }

    def sequentAndIntOfFact(fact: Fact): (F.Sequent, Int) = fact match {
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

    def sequentOfFact(fact: Fact): F.Sequent = fact match {
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

    def sequentOfOutsideFact(of: OutsideFact): F.Sequent

    def getSequent(f: Fact): F.Sequent = sequentOfFact(f)
    def mostRecentStep: ProofStep = steps.head

    def length: Int = steps.length

    def lockedSymbols: Set[F.SchematicLabel[?]] = assumptions.toSet.flatMap(f => f.freeSchematicLabels.toSet)

    def asOutsideFact(j: JUSTIFICATION): OutsideFact

    @nowarn("msg=.*It would fail on pattern case: _: InnerProof.*")
    def depth: Int = this match {
      case p: Proof#InnerProof => 1 + p.parent.depth
      case _: BaseProof => 0
    }

    def newInnerProof(possibleGoal: Option[F.Sequent]) = new InnerProof(possibleGoal)
    final class InnerProof(val possibleGoal: Option[F.Sequent]) extends Proof(this.getAssumptions) {
      val parent: Proof.this.type = Proof.this
      val owningTheorem: THM = parent.owningTheorem
      type OutsideFact = parent.Fact
      override inline def asOutsideFact(j: JUSTIFICATION): OutsideFact = parent.asOutsideFact(j)

      override def sequentOfOutsideFact(of: parent.Fact): F.Sequent = of match {
        case j: JUSTIFICATION => j.statement
        case ds: Proof#ProofStep => ds.bot
        case _ => parent.sequentOfFact(of)
      }
    }

    /**
     * Contains the result of a tactic computing a K.SCProofTactic.
     * Can be successful or unsuccessful.
     */
    sealed abstract class ProofTacticJudgement {
      val tactic: ProofTactic
      val proof: Proof = Proof.this

      /**
       * Returns true if and only if the judgement is valid.
       */
      def isValid: Boolean = this match {
        case ValidProofTactic(_, _, _) => true
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
     * A Kernel Sequent Calculus proof step that has been correctly produced.
     */
    case class ValidProofTactic(bot: lisa.fol.FOL.Sequent, scps: Seq[K.SCProofStep], imports: Seq[Fact])(using val tactic: ProofTactic) extends ProofTacticJudgement {}

    /**
     * A proof step which led to an error when computing the corresponding K.Sequent Calculus proof step.
     */
    case class InvalidProofTactic(message: String)(using val tactic: ProofTactic) extends ProofTacticJudgement {
      private val nstack = Throwable()
      val stack: Array[StackTraceElement] = nstack.getStackTrace.drop(2)
    }
  }

  sealed class BaseProof(val owningTheorem: THM) extends Proof(Nil) {
    val goal: F.Sequent = owningTheorem.goal
    val possibleGoal: Option[F.Sequent] = Some(goal)
    type OutsideFact = JUSTIFICATION
    override inline def asOutsideFact(j: JUSTIFICATION): OutsideFact = j

    override def sequentOfOutsideFact(j: JUSTIFICATION): F.Sequent = j.statement
  }

  sealed abstract class JUSTIFICATION {
    def repr: String
    def innerJustification: theory.Justification
    def statement: F.Sequent
    def withSorry: Boolean = innerJustification match {
      case thm: theory.Theorem => thm.withSorry
      case fd: theory.FunctionDefinition => fd.withSorry
      case pd: theory.PredicateDefinition => false
      case ax: theory.Axiom => false
    }
  }

  class AXIOM(innerAxiom: theory.Axiom, val axiom: F.Formula, val name: String) extends JUSTIFICATION {
    def innerJustification: theory.Axiom = innerAxiom
    val statement: F.Sequent = F.Sequent(Set(), Set(axiom))
    if (statement.underlying != theory.sequentFromJustification(innerAxiom)) {
      throw new InvalidAxiomException("The provided kernel axiom and desired statement don't match.", name, axiom, library)
    }
    def repr: String = innerJustification.repr
  }

  def Axiom(name: String, axiom: F.Formula): AXIOM = {
    val ax: Option[theory.Axiom] = theory.addAxiom(name, axiom.underlying)
    ax match {
      case None => throw new InvalidAxiomException("Not all symbols belong to the theory", name, axiom, library)
      case Some(value) => AXIOM(value, axiom, name)
    }
  }

  // def Axiom(using om: OutputManager, line: Int, file: String)(ax: theory.Axiom): AXIOM = AXIOM(line, file, ax.)
  abstract class DEFINITION(line: Int, file: String) extends JUSTIFICATION {
    def repr: String = innerJustification.repr
    def label: F.ConstantLabel[?]
    knownDefs.update(label, Some(this))

  }

  class THM(using om: OutputManager)(val statement: F.Sequent, val fullName: String, line: Int, file: String, val kind: TheoremKind)(computeProof: Proof ?=> Unit) extends JUSTIFICATION {

    val goal: F.Sequent = statement
    val name: String = fullName

    val proof: BaseProof = new BaseProof(this)

    val innerJustification: theory.Theorem = prove(computeProof)

    def prettyGoal: String = lisa.utils.FOLPrinter.prettySequent(goal.underlying)
    def repr: String = innerJustification.repr

    private def prove(computeProof: Proof ?=> Unit): theory.Theorem = {
      try {
        computeProof(using proof)
      } catch {
        /*case e: NotImplementedError =>
          om.lisaThrow(new UnimplementedProof(this))*/
        case e: UserLisaException =>
          om.lisaThrow(e)
      }

      if (proof.length == 0)
        om.lisaThrow(new UnimplementedProof(this))

      val scp = proof.toSCProof
      theory.theorem(name, goal.underlying, scp, proof.getImports.map(_._1.innerJustification)) match {
        case K.Judgement.ValidJustification(just) =>
          library.last = Some(this)
          just
        case wrongJudgement: K.Judgement.InvalidJustification[?] =>
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

  given thmConv: Conversion[library.THM, theory.Theorem] = _.innerJustification

  trait TheoremKind {
    val kind2: String
    def apply(using om: OutputManager, name: sourcecode.Name, line: sourcecode.Line, file: sourcecode.File)(statement: F.Sequent)(computeProof: Proof ?=> Unit): THM = {
      val thm = new THM(statement, name.value, line.value, file.value, this)(computeProof) {}
      if (this == Theorem) {
        show(thm)
      }
      thm
    }

  }
  object Theorem extends TheoremKind { val kind2: String = "Theorem" }
  object Lemma extends TheoremKind { val kind2: String = "Lemma" }
  object Corollary extends TheoremKind { val kind2: String = "Corollary" }

  object InternalStatement extends TheoremKind { val kind2: String = "Internal, automatically produced" }

}
