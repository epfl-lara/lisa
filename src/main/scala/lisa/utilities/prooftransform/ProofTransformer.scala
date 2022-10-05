package lisa.utilities.prooftransform

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.*
import lisa.utils.Printer

import java.text.Normalizer.Form

/**
 * A generic transformation on a proof with some useful utilities functions.
 *
 * Beware that the parameter should really be the same proof you will mainly work on
 * @param pr the proof to apply the transformation on
 */
abstract class ProofTransformer(pr: SCProof) {

  // PUBLIC FUNCTIONS###################################################################################################################
  /**
   * Main transformation function, should be the only function needed to be called by the user
   *
   * @return the transformed proof
   */
  def transform(): SCProof

  // PRIVATE FUNCTIONS##################################################################################################################
  /**
   * Gives for a given step all step that lead to it
   *
   * @param step the step for which the predecessors are to be found
   * @return a set of all steps that lead to the given step
   */
  protected def adjacencyMatrix[A](pr: IndexedSeq[A], imports: A => Seq[Int]): Map[Int, Set[Int]] = {
    val steps = pr
    val adjMat = scala.collection.mutable.Map[Int, Set[Int]]().withDefault(_ => Set.empty)

    steps.zipWithIndex.foreach((step, i) => {
      adjMat(i) = Set.empty ++ adjMat(i)
      imports(step).foreach((prem) => {
        if (prem > 0)
          adjMat(prem) = adjMat(prem) + i
      })
    })
    adjMat.toMap
  }

  /**
   * Gives a set of step indices that are the maximal tree spanning from the given step index embeded in the given proof
   *
   * @param st the root of the tree
   * @param pr the proof to be used as a graph
   * @return a set of step indices that are the maximal tree spanning from the given step index embeded in the given proof
   */
  protected def findBranch(st: Int, pr: SCProof): Seq[Int] = {

    val adjMat = adjacencyMatrix(pr.steps, (s) => s.premises)

    pr(st).premises.filter(_ > 0) match {
      case Nil => Seq(st)
      case pp if adjMat(st).size == 1 => st +: pp.flatMap((prem) => findBranch(prem, pr))
      case _ => Nil
    }

  }

  /**
   * Assigns to each node of a DAG all the imports (as defined in the parameters) attainable from it
   * Executes in liniear time
   * @param top_sort a topologically sorted array representing the DAG
   * @param children returns a list of all nodes linked to a given node
   * @param imports implementation dependent
   * @return node -> [imports(v) | exists a path between node and v]
   */
  protected def dependency_finder[A](top_sort: IndexedSeq[A], children: A => Seq[A], imports: A => Seq[Int]): Map[A, Set[Int]] = {
    var cache = scala.collection.mutable.Map[A, Set[Int]]().withDefault(_ => Set())
    def is_leaf(node: A): Boolean = imports(node).isEmpty | imports(node).forall(_ < 0)
    val adjMat = adjacencyMatrix(top_sort, imports)

    val rev = top_sort.reverse
    def inner(v: A): Seq[Int] = v match {
      case _ if is_leaf(v) => {
        cache(v) = imports(v).toSet
        imports(v)
      }
      case _ => {
        val current = imports(v).filter(_ < 0)
        val res = children(v).flatMap(inner) ++ current
        cache(v) = res.toSet
        res
      }
    }
    // Checks for empty proof
    val roots = adjMat.filter((i, s) => s.isEmpty).keySet.map(top_sort(_))
    roots.foreach(inner)
    cache.toMap
  }

  protected def sequentToFormulaNullable(s: Sequent): Formula = (s.left.toSeq, s.right.toSeq) match {

    case (Nil, _) => ConnectorFormula(Or, s.right.toSeq)
    case (_, Nil) => ConnectorFormula(And, s.left.toSeq)
    case (_, _) => sequentToFormula(s)

  }
}
