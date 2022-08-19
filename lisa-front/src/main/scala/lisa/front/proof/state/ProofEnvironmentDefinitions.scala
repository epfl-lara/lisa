package lisa.front.proof.state

import lisa.utils.Printer
import lisa.kernel.proof.{RunningTheory, SCProof, SCProofChecker}
import lisa.kernel.proof.RunningTheoryJudgement.*
import lisa.kernel.proof.SequentCalculus.{SCSubproof, sequentToFormula}
import lisa.front.fol.FOL.*
import lisa.utils.ProofsShrink

trait ProofEnvironmentDefinitions extends ProofStateDefinitions {

  import scala.collection.mutable

  /**
   * The proof environment represents a mutable context with axioms and theorems.
   * It is analogous to the kernel's [[RunningTheory]], but adapted to the front and with additional safety guarantees and utilities.
   * @param runningTheory the kernel's theory
   */
  final class ProofEnvironment(val runningTheory: RunningTheory, // For now, doesn't need to be generically typed
  ) extends ReadableProofEnvironment {
    private[ProofEnvironmentDefinitions] val proven: mutable.Map[Sequent, Seq[(Justified, runningTheory.Justification)]] = mutable.Map.empty

    private def addOne(sequent: Sequent, justified: Justified, kernelJustification: runningTheory.Justification): Unit = {
      if(!proven.contains(sequent)) {
        proven.addOne(sequent, Seq.empty)
      }
      proven.addOne(sequent, proven(sequent) :+ (justified, kernelJustification))
    }

    // Lift the initial axioms
    runningTheory.axiomsList.foreach { kernelAxiom =>
      val frontAxiom = Axiom(this, fromKernel(kernelAxiom.ax))
      addOne(frontAxiom.sequent, frontAxiom, kernelAxiom)
    }

    override def contains(sequent: Sequent): Boolean = proven.contains(sequent)

    def belongsToTheory(label: ConstantFunctionLabel[?]): Boolean = runningTheory.isSymbol(toKernel(label))
    def belongsToTheory(label: ConstantPredicateLabel[?]): Boolean = runningTheory.isSymbol(toKernel(label))
    def belongsToTheory(term: Term): Boolean =
      termLabelsOf(term).collect { case f: ConstantFunctionLabel[?] => f }.forall(belongsToTheory)
    def belongsToTheory(formula: Formula): Boolean =
      termLabelsOf(formula).collect { case f: ConstantFunctionLabel[?] => f }.forall(belongsToTheory) &&
        predicatesOf(formula).collect { case p: ConstantPredicateLabel[?] => p }.forall(belongsToTheory)
    def belongsToTheory(sequent: SequentBase): Boolean =
      sequent.left.forall(belongsToTheory) && sequent.right.forall(belongsToTheory)

    private def addSequentToEnvironment(sequent: Sequent, scProof: SCProof, justifiedImports: Map[Int, Sequent]): Theorem = {
      require(scProof.imports.size == justifiedImports.size && scProof.imports.indices.forall(justifiedImports.contains),
        "All imports must be justified")
      require(isAcceptedSequent(sequent)(this), "Invalid conclusion")
      require(lisa.kernel.proof.SequentCalculus.isSameSequent(sequentToKernel(sequent), scProof.conclusion),
        "Error: the proof conclusion does not match the provided sequent")
      val judgement = SCProofChecker.checkSCProof(scProof)
      if(!judgement.isValid) {
        throw new AssertionError(
          Seq(
            "Error: the theorem was found to produce an invalid proof; this could indicate a problem with a tactic or a bug in the implementation",
            "The produced proof is shown below for reference:",
            Printer.prettySCProof(judgement)
          ).mkString("\n")
        )
      }

      val justificationPairs = scProof.imports.indices.map(justifiedImports).map(proven).map(_.head)
      val justifications = justificationPairs.map { case (justification, _) => justification }

      val kernelJustifications = justificationPairs.map { case (_, kernelJustification) => kernelJustification }
      val kernelTheorem = runningTheory.makeTheorem(s"t${proven.size}", scProof.conclusion, scProof, kernelJustifications) match {
        case ValidJustification(result) => result
        case InvalidJustification(_, _) => throw new Error // Should have been caught before
      }

      val theorem = Theorem(this, sequent, scProof, justifications)
      addOne(sequent, theorem, kernelTheorem) // TODO should we salvage existing theorems instead of creating new ones?

      theorem
    }
    def mkTheorem(proof: Proof): Theorem = {
      require(proof.initialState.goals.sizeIs == 1, "The proof must start with exactly one goal")
      val sequent = proof.initialState.goals.head
      evaluateProof(proof)(this) match {
        case Some(proofModeState) =>
          val (scProof, theoremImports) = reconstructSCProof(proofModeState)
          addSequentToEnvironment(sequent, scProof, theoremImports)
        case None => throw new Exception // Failure in evaluating the proof
      }
    }
    def mkAxiom(formula: Formula): Axiom = {
      require(runningTheory.isAxiom(formula))
      Axiom(this, formula)
    }
    //def mkDefinition() // TODO
    def mkTheorem(sequent: Sequent, scProof: SCProof, theorems: IndexedSeq[Justified]): Theorem =
      addSequentToEnvironment(sequent, scProof, theorems.map(_.sequent).zipWithIndex.map(_.swap).toMap)
    //override def toString: String = proven.keySet.toSeq.map(Theorem(this, _)).map(_.toString).mkString("\n")
  }

  def newEmptyEnvironment(): ProofEnvironment = new ProofEnvironment(new RunningTheory)

  /**
   * A justified statement with respect to a theory is a sequent that is accepted by this theory.
   */
  sealed abstract class Justified extends ReadableJustified {
    private[proof] val environment: ProofEnvironment
    def sequent: Sequent
    final def sequentAsKernel: lisa.kernel.proof.SequentCalculus.Sequent = sequentToKernel(sequent)
  }

  /**
   * An axiom is a justified statement that is admitted without a proof.
   * It is guaranteed that this sequent has exactly one conclusion and no assumptions.
   * @param formula the original formula
   */
  case class Axiom private[ProofEnvironmentDefinitions](environment: ProofEnvironment, formula: Formula) extends Justified {
    override def sequent: Sequent = () |- formula
    override def toString: String = s"Axiom: $sequent"
  }

  /**
   * A theorem is a justified statement which has an associated proof depending on other justified statements.
   * @param proof the proof of this theorem
   * @param justifications the dependencies of this theorem (= assumptions)
   */
  case class Theorem private[ProofEnvironmentDefinitions](
    environment: ProofEnvironment,
    sequent: Sequent,
    proof: SCProof,
    justifications: IndexedSeq[Justified]) extends Justified {
    override def toString: String = s"Theorem: $sequent"
  }


  // Borrowed from past work: https://github.com/FlorianCassayre/competitive-scala
  private def topologicalSort[U](start: U, adjacency: Map[U, Set[U]]): Seq[U] = {
    def dfs(stack: Seq[(U, Set[U])], marks: Map[U, Boolean], sorted: Seq[U]): (Map[U, Boolean], Seq[U]) = {
      stack match {
        case (u, adjacent) +: tail =>
          adjacent.headOption match {
            case Some(v) =>
              marks.get(v) match {
                case Some(false) => throw new Exception // Cycle
                case Some(true) => dfs((u, adjacent.tail) +: tail, marks, sorted)
                case None => dfs((v, adjacency.getOrElse(v, Set.empty[U])) +: (u, adjacent.tail) +: tail, marks + (v -> false), sorted)
              }
            case None => dfs(tail, marks + (u -> true), u +: sorted)
          }
        case _ => (marks, sorted)
      }
    }
    val (_, sorted) = dfs(Seq((start, adjacency.getOrElse(start, Set.empty[U]))), Map(start -> false), Seq.empty)
    sorted
  }

  /**
   * Converts a theorem into a kernel proof where the imports are the assumption of that theorem.
   * @param theorem the theorem to convert
   * @return a kernel proof
   */
  def reconstructPartialSCProofForTheorem(theorem: Theorem): SCProof = theorem.proof // (that's it)

  /**
   * Converts a theorem into a kernel proof where the imports are all axioms of that theory.
   * Essentially inlines all dependent theorems recursively into a single, fat proof.
   * @param theorem the theorem to convert
   * @return a kernel proof
   */
  def reconstructSCProofForTheorem(theorem: Theorem): SCProof = {
    // Inefficient, no need to traverse/reconstruct the whole graph
    val environment = theorem.environment
    val theorems = environment.proven.values.flatMap(_.collect {
      case (theorem: Theorem, _) => theorem
    }).toSeq
    val sortedTheorems = topologicalSort(theorem, theorems.map(theorem =>
      (theorem, theorem.justifications.collect { case other: Theorem => other }.toSet) // This will have to be updated for definitions
    ).toMap.withDefaultValue(Set.empty)).reverse
    val sortedAxioms = sortedTheorems
      .flatMap(_.justifications.collect { case ax: Axiom => ax }).toSet
      .map(_.sequent).toIndexedSeq.sortBy(_.toString)
    val sequentToImport = sortedAxioms.zipWithIndex.toMap.view.mapValues(i => -(i + 1)).toMap

    assert(sortedTheorems.lastOption.contains(theorem))
    val sequentToIndex = sortedTheorems.map(_.sequent).zipWithIndex
      .reverse // This step is important: in case of duplicate nodes, this ensures we have no forward references
      .toMap ++ sequentToImport

    assert(sortedTheorems.zipWithIndex.forall { case (thm, i) => thm.justifications.map(_.sequent).forall(s => sequentToIndex.get(s).exists(_ < i)) })

    val scProof = SCProof(sortedTheorems.map(theorem =>
      SCSubproof(theorem.proof, theorem.justifications.map(_.sequent).map(sequentToIndex))
    ).toIndexedSeq, sortedAxioms.map(sequentToKernel))

    assert(scProof.conclusion == sequentToKernel(theorem.sequent))

    val judgement = SCProofChecker.checkSCProof(scProof)
    if(!judgement.isValid) {
      throw new AssertionError(
        Seq(
          "Error: the reconstructed proof was found to be invalid; this could indicate a bug in the implementation of this very method",
          "The reconstructed proof is shown below for reference:",
          Printer.prettySCProof(judgement)
        ).mkString("\n")
      )
    }

    val optimized = ProofsShrink.optimizeProofIteratively(scProof)
    assert(SCProofChecker.checkSCProof(optimized).isValid) // Assertion failure means a bug in `SCUtils`
    optimized
  }

}
