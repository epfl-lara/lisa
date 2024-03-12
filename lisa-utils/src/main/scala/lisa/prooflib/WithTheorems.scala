package lisa.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.ProofTacticLib.UnimplementedProof
import lisa.prooflib.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.LisaException
import lisa.utils.UserLisaException
import lisa.utils.UserLisaException.*
import lisa.utils.parsing.FOLPrinter.prettySCProof
import lisa.utils.parsing.UnreachableException

import scala.annotation.nowarn
import scala.collection.mutable.Buffer as mBuf
import scala.collection.mutable.Map as mMap
import scala.collection.mutable.Stack as stack

trait WithTheorems {
  library: Library =>

  /**
   * The main builder for proofs. It is a mutable object that can be used to build a proof step by step.
   * It is used either to construct a theorem/lemma ([[BaseProof]]) or to construct a subproof ([[InnerProof]]).
   * We can add proof tactics to it producing intermediate results. In the end, obtain a [[K.SCProof]] from it.
   *
   * @param assump list of starting assumptions, usually propagated from outer proofs.
   */
  // TODO: reseal this class
  // see https://github.com/lampepfl/dotty/issues/19031
  // and https://github.com/epfl-lara/lisa/issues/190
  abstract class Proof(assump: List[F.Formula]) {
    val possibleGoal: Option[F.Sequent]
    type SelfType = this.type
    type OutsideFact >: JUSTIFICATION
    type Fact = ProofStep | InstantiatedFact | OutsideFact | Int

    /**
     * A proven fact (from a previously proven step, a theorem or a definition) with specific instantiations of free variables.
     *
     * @param fact The base fact
     * @param insts The instantiation of free variables
     */
    case class InstantiatedFact(
        fact: Fact,
        insts: Seq[F.SubstPair | F.Term]
    ) {
      val baseFormula: F.Sequent = sequentOfFact(fact)
      val (result, proof) = {
        val (terms, substPairs) = insts.partitionMap {
          case t: F.Term => Left(t)
          case sp: F.SubstPair => Right(sp)
        }

        val (s1, p1) = if substPairs.isEmpty then (baseFormula, Seq()) else baseFormula.instantiateWithProof(substPairs.map(sp => (sp._1, sp._2)).toMap, -1)
        val (s2, p2) = if terms.isEmpty then (s1, p1) else s1.instantiateForallWithProof(terms, p1.length - 1)
        (s2, p1 ++ p2)
      }

    }

    val library: WithTheorems.this.type = WithTheorems.this

    private var steps: List[ProofStep] = Nil
    private var imports: List[(OutsideFact, F.Sequent)] = Nil
    private var instantiatedFacts: List[(InstantiatedFact, Int)] = Nil
    private var assumptions: List[F.Formula] = assump
    private var eliminations: List[(F.Formula, (Int, F.Sequent) => List[K.SCProofStep])] = Nil

    def cleanAssumptions: Unit = assumptions = Nil

    /**
     * the theorem that is being proved (paritally, if subproof) by this proof.
     *
     * @return The theorem
     */
    def owningTheorem: THM

    /**
     * A proof step, containing a high level ProofTactic and the corresponding K.SCProofStep. If the tactic produce more than one
     * step, they must be encapsulated in a subproof. Usually constructed with [[ValidProofTactic.validate]]
     *
     * @param judgement The result of the tactic
     * @param scps The corresponding [[K.SCProofStep]]
     * @param position The position of the step in the proof
     */
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

    /**
     * A proof step can be constructed from a succesfully executed tactic
     */
    def newProofStep(judgement: ValidProofTactic): ProofStep =
      ProofStep.newProofStep(judgement)

    private def addStep(ds: ProofStep): Unit = steps = ds :: steps
    private def addImport(imp: OutsideFact, seq: F.Sequent): Unit = {
      imports = (imp, seq) :: imports
    }

    private def addInstantiatedFact(instFact: InstantiatedFact): Unit = {
      val step = ValidProofTactic(instFact.result, instFact.proof, Seq(instFact.fact))(using F.SequentInstantiationRule)
      newProofStep(step)
      instantiatedFacts = (instFact, steps.length - 1) :: instantiatedFacts
    }

    /**
     * Add an assumption the the proof, i.e. a formula that is automatically on the left side of the sequent.
     *
     * @param f
     */
    def addAssumption(f: F.Formula): Unit = {
      if (!assumptions.contains(f)) assumptions = f :: assumptions
    }

    def addElimination(f: F.Formula, elim: (Int, F.Sequent) => List[K.SCProofStep]): Unit = {
      eliminations = (f, elim) :: eliminations
    }

    def addDischarge(ji: Fact): Unit = {
      val (s1, t1) = sequentAndIntOfFact(ji)
      val f = s1.right.head
      val fu = f.underlying
      addElimination(
        f,
        (i, sequent) =>
          List(
            SC.Cut((sequent.underlying -<< fu) ++ (s1.underlying ->> fu), t1, i, fu)
          )
      )
    }
    /*
    def addDefinition(v: LocalyDefinedVariable, defin: F.Formula): Unit = {
      if localdefs.contains(v) then
        throw new UserInvalidDefinitionException("v", "Variable already defined with" + v.definition + " in current proof")
      else {
        localdefs(v) = defin
        addAssumption(defin)
      }
    }
    def getDefinition(v: LocalyDefinedVariable): Fact = localdefs(v)._2
     */

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
     * Produce the low level [[K.SCProof]] corresponding to the proof. Automatically eliminates any formula in the discharges that is still left of the sequent.
     *
     * @return
     */
    def toSCProof: K.SCProof = {
      import lisa.utils.KernelHelpers.{-<<, ->>}
      val finalSteps = eliminations.foldLeft[(List[SC.SCProofStep], F.Sequent)]((steps.map(_.scps), steps.head.bot)) { (cumul_bot, f_elim) =>
        val (cumul, bot) = cumul_bot
        val (f, elim) = f_elim
        val i = cumul.size
        val elimSteps = elim(i - 1, bot)
        (elimSteps.foldLeft(cumul)((cumul2, step) => step :: cumul2), bot -<< f)
      }

      val r = K.SCProof(finalSteps._1.reverse.toIndexedSeq, getImports.map(of => of._2.underlying).toIndexedSeq)
      r
    }

    def currentSCProof: K.SCProof = K.SCProof(steps.map(_.scps).reverse.toIndexedSeq, getImports.map(of => of._2.underlying).toIndexedSeq)

    /**
     * For a fact, returns the sequent that the fact proove and the position of the fact in the proof.
     *
     * @param fact Any fact, possibly instantiated, belonging to the proof
     * @return its proven sequent and position
     */
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

    /**
     * The number of steps in the proof. This is not the same as the number of steps in the corresponding [[K.SCProof]].
     * This also does not count the number of steps in the subproof.
     *
     * @return
     */
    def length: Int = steps.length

    /**
     * The set of symbols that can't be instantiated because they are free in an assumption.
     */
    def lockedSymbols: Set[F.SchematicLabel[?]] = assumptions.toSet.flatMap(f => f.freeSchematicLabels.toSet)

    /**
     * Used to "lift" the type of a justification when the compiler can't infer it.
     */
    def asOutsideFact(j: JUSTIFICATION): OutsideFact

    def depth: Int =
      (this: @unchecked) match {
        case p: Proof#InnerProof => 1 + p.parent.depth
        case _: BaseProof => 0
      }

    /**
     * Create a subproof inside the current proof. The subproof will have the same assumptions as the current proof.
     * Can have a goal known in advance (usually for a user-written subproof) or not (usually for a tactic-generated subproof).
     */
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

  /**
   * Top-level instance of [[Proof]] directly proving a theorem
   */
  sealed class BaseProof(val owningTheorem: THMFromProof) extends Proof(Nil) {
    val goal: F.Sequent = owningTheorem.goal
    val possibleGoal: Option[F.Sequent] = Some(goal)
    type OutsideFact = JUSTIFICATION
    override inline def asOutsideFact(j: JUSTIFICATION): OutsideFact = j

    override def sequentOfOutsideFact(j: JUSTIFICATION): F.Sequent = j.statement

    def justifications: List[JUSTIFICATION] = getImports.map(_._1)
  }

  /**
   * Abstract class representing theorems, axioms and different kinds of definitions. Corresponds to a [[theory.Justification]].
   */
  sealed abstract class JUSTIFICATION {

    /**
     * A pretty representation of the justification
     */
    def repr: String

    /**
     * The inner kernel justification
     */
    def innerJustification: theory.Justification

    /**
     * The sequent that the justification proves
     */
    def statement: F.Sequent

    /**
     * The complete name of the justification. Two justifications should never have the same full name. Typically, path is used to disambiguate.
     */
    def fullName: String

    /**
     * The short name of the justification (without the path).
     */
    val name: String = fullName.split("\\.").last

    /**
     * The "owning" object of the justification. Typically, the package/object in which it is defined.
     */
    val owner = fullName.split("\\.").dropRight(1).mkString(".")

    /**
     * Returns if the statement is unconditionaly proven or if it depends on some sorry step (including in the other justifications it relies on)
     */
    def withSorry: Boolean = innerJustification match {
      case thm: theory.Theorem => thm.withSorry
      case fd: theory.FunctionDefinition => fd.withSorry
      case pd: theory.PredicateDefinition => false
      case ax: theory.Axiom => false
    }
  }

  /**
   * A Justification, corresponding to [[K.Axiom]]
   */
  class AXIOM(innerAxiom: theory.Axiom, val axiom: F.Formula, val fullName: String) extends JUSTIFICATION {
    def innerJustification: theory.Axiom = innerAxiom
    val statement: F.Sequent = F.Sequent(Set(), Set(axiom))
    if (statement.underlying != theory.sequentFromJustification(innerAxiom)) {
      throw new InvalidAxiomException("The provided kernel axiom and desired statement don't match.", name, axiom, library)
    }
    def repr: String = s" Axiom $name := $axiom"
  }

  /**
   * Introduces a new axiom in the theory.
   *
   * @param fullName The name of the axiom, including the path. Usually fetched automatically by the compiler.
   * @param axiom The axiomatized formula.
   * @return
   */
  def Axiom(using fullName: sourcecode.FullName)(axiom: F.Formula): AXIOM = {
    val ax: Option[theory.Axiom] = theory.addAxiom(fullName.value, axiom.underlying)
    ax match {
      case None => throw new InvalidAxiomException("Not all symbols belong to the theory", fullName.value, axiom, library)
      case Some(value) => AXIOM(value, axiom, fullName.value)
    }
  }

  /**
   * A Justification, corresponding to [[K.FunctionDefinition]] or [[K.PredicateDefinition]]
   */
  abstract class DEFINITION(line: Int, file: String) extends JUSTIFICATION {
    val fullName: String
    def repr: String = innerJustification.repr

    def label: F.ConstantLabel[?]
    knownDefs.update(label, Some(this))

  }

  /**
   * A proven, reusable statement. A justification corresponding to [[K.Theorem]].
   */
  sealed abstract class THM extends JUSTIFICATION {
    def repr: String =
      s" Theorem ${name} := ${statement}${if (withSorry) " (!! Relies on Sorry)" else ""}"

    /**
     * The underlying Kernel proof [[K.SCProof]], if it is still available. Proofs are not kept in memory for efficiency.
     */
    def kernelProof: Option[K.SCProof]

    /**
     * The high level [[Proof]], if one was used to obtain the theorem. If the theorem was not produced by such high level proof but directly by a low level one, this is None.
     */
    def highProof: Option[BaseProof]
    val innerJustification: theory.Theorem

    /**
     * A pretty representation of the goal of the theorem
     */
    def prettyGoal: String = lisa.utils.FOLPrinter.prettySequent(statement.underlying)
  }
  object THM {

    /**
     * Standard way to construct a theorem using a high level proof.
     *
     * @param om The output manager, available in any file extending [[lisa.utils.BasicMain]]
     * @param statement The statement of the theorem
     * @param fullName The full name of the theorem, including the path. Usually fetched automatically by the compiler.
     * @param line The line at which the theorem is defined. Usually fetched automatically by the compiler. Used for error reporting
     * @param file The file in which the theorem is defined. Usually fetched automatically by the compiler. Used for error reporting
     * @param kind The kind of theorem (Theorem, Lemma, Corollary)
     * @param computeProof The proof computation. The proof is built by adding proof steps to the proof object. The proof object is an impicit argument of computeProof,
     * @see <a href="https://docs.scala-lang.org/scala3/reference/contextual/context-functions.html">Context Functions in Scala</a>
     * @return
     */
    def apply(using om: OutputManager)(statement: F.Sequent, fullName: String, line: Int, file: String, kind: TheoremKind)(computeProof: Proof ?=> Unit) =
      THMFromProof(statement, fullName, line, file, kind)(computeProof)

    /**
     * Constructs a "high level" theorem from an existing theorem in the
     *
     * @param om The output manager, available in any file extending [[lisa.utils.BasicMain]]
     * @param statement The statement of the theorem
     * @param fullName The full name of the theorem, including the path/package.
     * @param kind The kind of theorem (Theorem, Lemma, Corollary)
     * @param innerThm The inner theorem, coming from the kernel
     * @param getProof If available, a way to compute the Kernel proof again.
     */
    def fromKernel(using om: OutputManager)(statement: F.Sequent, fullName: String, kind: TheoremKind, innerThm: theory.Theorem, getProof: () => Option[K.SCProof]) =
      THMFromKernel(statement, fullName, kind, innerThm, getProof)

    /**
     * Construct a theorem (both in the kernel and high level) from a proof.
     *
     * @param om The output manager, available in any file extending [[lisa.utils.BasicMain]]
     * @param statement The statement of the theorem
     * @param fullName The full name of the theorem, including the path/package.
     * @param kind The kind of theorem (Theorem, Lemma, Corollary)
     * @param getProof The kernel proof.
     * @param justifs low level justifications used to justify the proof's imports
     * @return
     */
    def fromSCProof(using om: OutputManager)(statement: F.Sequent, fullName: String, kind: TheoremKind, getProof: () => K.SCProof, justifs: Seq[theory.Justification]): THM =
      val proof = getProof()
      theory.theorem(fullName, statement.underlying, proof, justifs) match {
        case K.Judgement.ValidJustification(just) =>
          fromKernel(statement, fullName, kind, just.asInstanceOf, () => Some(getProof()))
        case wrongJudgement: K.Judgement.InvalidJustification[?] =>
          om.lisaThrow(
            LisaException.InvalidKernelJustificationComputation(
              "The proof was rejected by LISA's logical kernel. ",
              wrongJudgement,
              None
            )
          )
      }

  }

  /**
   * A theorem that was produced from a kernel theorem and not from a high level proof. See [[THM.fromKernel]].
   * Those are typically theorems imported from another tool, or from serialization.
   */
  class THMFromKernel(using om: OutputManager)(val statement: F.Sequent, val fullName: String, val kind: TheoremKind, innerThm: theory.Theorem, getProof: () => Option[K.SCProof]) extends THM {

    val innerJustification: theory.Theorem = innerThm
    assert(innerThm.name == fullName)
    def kernelProof: Option[K.SCProof] = getProof()
    def highProof: Option[BaseProof] = None

    val goal: F.Sequent = statement

  }

  /**
   * A theorem that was produced from a high level proof. See [[THM.apply]].
   * Typical way to construct a theorem in the library, but serialization for example will produce a [[THMFromKernel]].
   */
  class THMFromProof(using om: OutputManager)(val statement: F.Sequent, val fullName: String, line: Int, file: String, val kind: TheoremKind)(computeProof: Proof ?=> Unit) extends THM {

    val goal: F.Sequent = statement

    val proof: BaseProof = new BaseProof(this)
    def kernelProof: Option[K.SCProof] = Some(proof.toSCProof)
    def highProof: Option[BaseProof] = Some(proof)

    import lisa.utils.Serialization.*
    val innerJustification: theory.Theorem =
      if library._draft.nonEmpty && library._draft.get.value != file
      then // if the draft option is activated, and the theorem is not in the file where the draft option is given, then we replace the proof by sorry
        theory.theorem(name, goal.underlying, SCProof(SC.Sorry(goal.underlying)), IndexedSeq.empty) match {
          case K.Judgement.ValidJustification(just) =>
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
      else if library._withCache then
        oneThmFromFile("cache/" + name, library.theory) match {
          case Some(thm) => thm // try to get the theorem from file

          case None =>
            val (thm, scp, justifs) = prove(computeProof) // if fail, prove it
            thmsToFile("cache/" + name, theory, List((name, scp, justifs))) // and save it to the file
            thm
        }
      else prove(computeProof)._1

    library.last = Some(this)

    /**
     * Construct the kernel theorem from the high level proof
     */
    private def prove(computeProof: Proof ?=> Unit): (theory.Theorem, SCProof, List[(String, theory.Justification)]) = {
      try {
        computeProof(using proof)
      } catch {
        case e: UserLisaException =>
          om.lisaThrow(e)
      }

      if (proof.length == 0)
        om.lisaThrow(new UnimplementedProof(this))

      val scp = proof.toSCProof
      val justifs = proof.getImports.map(e => (e._1.owner, e._1.innerJustification))
      theory.theorem(name, goal.underlying, scp, justifs.map(_._2)) match {
        case K.Judgement.ValidJustification(just) =>
          (just, scp, justifs)
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

    def apply(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: F.Sequent)(computeProof: Proof ?=> Unit): THM = {
      val thm = THM(statement, name.value, line.value, file.value, this)(computeProof)
      if this == Theorem then show(thm)
      thm
    }

  }

  /**
   * A "Theorem" kind of theorem, by opposition with a lemma or corollary. The difference is that theorem are always printed when a file defining one is run.
   */
  object Theorem extends TheoremKind { val kind2: String = "Theorem" }

  /**
   * Lemmas are like theorems, but are conceptually less importants and are not printed when a file defining one is run.
   */
  object Lemma extends TheoremKind { val kind2: String = "Lemma" }

  /**
   * Corollaries are like theorems, but are conceptually less importants and are not printed when a file defining one is run.
   */
  object Corollary extends TheoremKind { val kind2: String = "Corollary" }

  /**
   * Internal statements are internally produced theorems, for example as intermediate step in definitions.
   */
  object InternalStatement extends TheoremKind { val kind2: String = "Internal, automatically produced" }

}
