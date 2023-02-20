package lisa.utilities.prooftransform
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.KernelHelpers.*
import lisa.utils.Printer

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
    case (h :: Nil, _) => ConnectorFormula(Implies, List(h, ConnectorFormula(Or, s.right.toSeq)))
    case (_, h :: Nil) => ConnectorFormula(Implies, List(ConnectorFormula(And, s.left.toSeq), h))
    case (_, _) => sequentToFormula(s)

  }
}

/**
 * A transformation that ensures its result is a proof where no instantiaiton are left, rreplaced by imports and rewrites of their conclusion
 *
 * @param pr the proof to be modified
 */
case class ProofInstantiationRemover(pr: SCProof) extends ProofTransformer(pr) {

  private val adjMat = adjacencyMatrix(pr.steps, s => s.premises)
  private val neg_premises = dependency_finder(pr.steps, ps => ps.premises.filter(_ >= 0).map(pr.steps(_)), ps => ps.premises)

  // PUBLIC FUNCTIONS###################################################################################################################
  /**
   * Maps a proof to a new proof where Instantiations are replaced by hypothesis
   *
   * @return the modified proof
   */
  def transform(): SCProof = instsAsImports(pr)

  // PRIVATE FUNCTIONS##################################################################################################################
  /**
   * determines if a step is a problematic instantiation that should be transformed into an import
   *
   * @param step the step to check for
   * @return whether the given step is an Instantiation tha thas a link to an import
   */
  private def isInst(step: SCProofStep): Boolean = step match {
    case InstSchema(_, t, _, _, _) if neg_premises.getOrElse(step, Seq.empty).nonEmpty => true
    case _ => false
  }

  /**
   * Maps Instantiations to Rewrites of imports
   *
   * @return a proof where all instantiations are rewrites of imports
   */
  private def instsAsImports(pr: SCProof): SCProof = {
    val imps = pr.steps.zipWithIndex.filter((st, j) => isInst(st)).map(_._2).zipWithIndex

    val mImps = imps.toMap
    val mSteps = pr.steps.zipWithIndex.map((s, j) =>
      s match {
        case _ if isInst(s) => Restate(() |- sequentToFormulaNullable(s.bot), -pr.imports.length - mImps(j) - 1)
        case _ => s
      }
    )

    SCProof(mSteps, pr.imports ++ imps.map((j, i) => mSteps(j).bot))
  }

}

case class ProofUnconditionalizer(prOrig: SCProof) extends ProofTransformer(prOrig) {

  // ATTRIBUTES#########################################################################################################################
  private val pr = ProofInstantiationRemover(prOrig).transform()
  private val neg_premises = dependency_finder(pr.steps, ps => ps.premises.filter(_ >= 0).map(pr.steps(_)), ps => ps.premises)

  // We use a var because Subproofs require the results of precedent steps, topological order on proofs ensure we can always do this
  private var appended_steps = IndexedSeq[SCProofStep]()
  // PREDICATES#########################################################################################################################
  /**
   * Wether a step needs to be more modified than just appending hypothesis on the left of the conclusion
   *
   * @param sc the step to analyse
   * @return whether the step has a negative premise
   */
  private def is_problematic(sc: SCProofStep): Boolean = sc.premises.exists(_ < 0)

  // PUBLIC FUNCTIONS###################################################################################################################
  /**
   * Maps a proof to a new proof where all imports are made into suppositions on the left of the conclusion
   *
   * @return A proof where each steps has the necessary imports added as suppostitions on the left of their bottom
   */
  def transform(): SCProof = transformPrivate(IndexedSeq.empty)

  // PRIVATE FUNCTIONS##################################################################################################################
  /**
   * Private version used to keep track of imports that should not be removed, useful for SubProofs
   *
   * @param keep The indices not to be removed from the transformed proof
   * @return a proof zhose imports have been removed except for those present in keep
   */
  private def transformPrivate(keep: IndexedSeq[Sequent]): SCProof = {
    pr.steps.zipWithIndex.foreach((pS, i) => {
      appended_steps = appended_steps.appended(if (is_problematic(pS)) {
        mapProb(pS)
      } else {
        mapStep(pS, b => neg_premises.getOrElse(pS, Set[Int]()).map(i => sequentToFormulaNullable(pr.imports(-i - 1))) ++ b)
      })
    })
    SCProof(appended_steps.toIndexedSeq, keep)
  }

  /**
   * Deals with steps that have a negative premise
   * The strategy is to systematically add an hypothesis to introduce the import, rewrite it
   * to remove unwanted clutter and apply strictly the same transformation as if there was no negative premise.
   * To not mess with indices of proof and to keep a clearer proof structure all those steps are wrapped into a SubProof
   *
   * @param pS thestep to be modified
   * @return a subproof whose conclusion is the same step as in the argument but with changed premises and a left side bottom modified as
   * in the general algorithm
   */
  private def mapProb(pS: SCProofStep) = {
    val premises = pS.premises
      .filter(_ < 0)
      .map(i => pr.imports(-i - 1))
    val hypothesis = premises
      .map((se) => {
        val h = Hypothesis((se.left + sequentToFormulaNullable(se)) |- (se.right + sequentToFormulaNullable(se)), sequentToFormulaNullable(se))
        h
      })
    val rewrites = hypothesis.zipWithIndex.map((h, i) => {
      val r = Restate(h.bot.left |- (h.bot.right - sequentToFormulaNullable(premises(i))), i)
      r
    })
    // We must separate the case for subproofs for they need to use the modified version of the precedent
    val inner = pS match {
      case SCSubproof(_, _) =>
        SCProof(
          hypothesis.toIndexedSeq ++ rewrites.toIndexedSeq ++ IndexedSeq(
            mapStep(
              pS,
              b => neg_premises(pS).map(i => sequentToFormulaNullable(pr.imports(-i - 1))) ++ b,
              s =>
                s.map(i =>
                  i match {
                    case i if i < 0 => -i - 2 + hypothesis.length
                    case i => -i
                  }
                ),
              rewrites.map(_.bot)
            )
          ),
          pS.premises.filter(_ >= 0).map(appended_steps(_).bot).toIndexedSeq
        )

      case _ =>
        SCProof(
          hypothesis.toIndexedSeq ++ IndexedSeq(
            mapStep(
              pS,
              b => neg_premises(pS).map(i => sequentToFormulaNullable(pr.imports(-i - 1))) ++ b,
              premise =>
                premise.zipWithIndex.map((i, j) =>
                  i match {
                    case i if i < 0 => j
                    case i => -j
                  }
                )
            )
          ),
          pS.premises.filter(_ >= 0).map(appended_steps(_).bot).toIndexedSeq
        )
    }
    SCSubproof(inner, pS.premises.filter(_ >= 0))
  }

  /**
   * This function transform generically a proof step into another one
   *
   * @param pS the proofstep to modify
   * @param f the transformation on left side of bottom
   * @param fi transformation on premises
   * @param fsub sequents to keep on subproofs
   * @return a proofstep where each function is applied to the corresponding
   */
  protected def mapStep(pS: SCProofStep, f: Set[Formula] => Set[Formula], fi: Seq[Int] => Seq[Int] = identity, fsub: Seq[Sequent] = Nil): SCProofStep = pS match {
    case Restate(bot, t1) => Restate(f(bot.left) |- bot.right, fi(pS.premises).head)
    case RestateTrue(bot) => RestateTrue(f(bot.left) |- bot.right)
    case LeftExists(bot, t1, phi, x) => LeftExists(f(bot.left) |- bot.right, fi(pS.premises).head, phi, x)
    case RightAnd(bot, t, cunjuncts) => RightAnd(f(bot.left) |- bot.right, fi(t), cunjuncts)
    case RightOr(bot, t1, phi, psi) => RightOr(f(bot.left) |- bot.right, fi(pS.premises).head, phi, psi)
    case RightImplies(bot, t1, phi, psi) => RightImplies(f(bot.left) |- bot.right, fi(pS.premises).head, phi, psi)
    case RightIff(bot, t1, t2, phi, psi) => RightIff(f(bot.left) |- bot.right, fi(pS.premises).head, fi(pS.premises).last, phi, psi)
    case RightNot(bot, t1, phi) => RightNot(f(bot.left) |- bot.right, fi(pS.premises).head, phi)
    case RightForall(bot, t1, phi, x) => RightForall(f(bot.left) |- bot.right, fi(pS.premises).head, phi, x)
    case RightExists(bot, t1, phi, x, t) => RightExists(f(bot.left) |- bot.right, fi(pS.premises).head, phi, x, t)
    case RightExistsOne(bot, t1, phi, x) => RightExistsOne(f(bot.left) |- bot.right, fi(pS.premises).head, phi, x)
    case Weakening(bot, t1) => Weakening(f(bot.left) |- bot.right, fi(pS.premises).head)
    case LeftRefl(bot, t1, fa) => LeftRefl(f(bot.left) |- bot.right, fi(pS.premises).head, fa)
    case RightRefl(bot, fa) => RightRefl(f(bot.left) |- bot.right, fa)
    case LeftSubstEq(bot, t1, equals, lambdaPhi) => LeftSubstEq(f(bot.left) |- bot.right, fi(pS.premises).head, equals, lambdaPhi)
    case RightSubstEq(bot, t1, equals, lambdaPhi) => RightSubstEq(f(bot.left) |- bot.right, fi(pS.premises).head, equals, lambdaPhi)
    case LeftSubstIff(bot, t1, equals, lambdaPhi) => LeftSubstIff(f(bot.left) |- bot.right, fi(pS.premises).head, equals, lambdaPhi)
    case RightSubstIff(bot, t1, equals, lambdaPhi) => RightSubstIff(f(bot.left) |- bot.right, fi(pS.premises).head, equals, lambdaPhi)
    case InstSchema(bot, t1, mCon, mPred, mTerm) => InstSchema(instantiateSchemaInSequent(f(bot.left) |- bot.right, mCon, mPred, mTerm).left |- bot.right, fi(pS.premises).head, mCon, mPred, mTerm)
    case SCSubproof(pp, t) => {
      SCSubproof(ProofUnconditionalizer(pp).transformPrivate(fsub.toIndexedSeq ++ t.filter(_ >= 0).map(i => appended_steps(i).bot).toIndexedSeq), fi(t))
    }
    case _ => ???
  }

}
