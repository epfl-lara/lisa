package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*

/**
 * Utilities to work with sequent-calculus proofs.
 * All of these methods assume that the provided proof are well-formed but not necessarily valid.
 * If the provided proofs are valid, then the resulting proofs will also be valid.
 */
object ProofsShrink {

  /**
   * Computes the size of a proof. Size corresponds to the number of proof steps.
   * Subproofs are count as one plus the size of their body.
   * @param proof the proof to analyze
   * @return the size of that proof
   */
  def proofSize(proof: SCProof): Int =
    proof.steps.map {
      case SCSubproof(sp, _, _) => 1 + proofSize(sp)
      case _ => 1
    }.sum

  /**
   * Computes the depth of a proof. Depth corresponds to the maximum number of nested subproofs plus one.
   * @param proof the proof to analyze
   * @return the depth of that proof
   */
  def proofDepth(proof: SCProof): Int =
    proof.steps.map {
      case SCSubproof(sp, _, _) => 1 + proofDepth(sp)
      case _ => 1
    }.max

  /**
   * Updates the indices of the premises in a proof step according to some provided mapping. For example:
   * <pre>
   * mapPremises(Rewrite(sequent, 1), i => i + 1) == Rewrite(sequent, 2)
   * </pre>
   * @param step the proof step to update
   * @param mapping the provided mapping
   * @return a new step with the updated indices
   */
  def mapPremises(step: SCProofStep, mapping: Int => Int): SCProofStep = step match {
    case s: Rewrite => s.copy(t1 = mapping(s.t1))
    case s: Hypothesis => s
    case s: Cut => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: LeftAnd => s.copy(t1 = mapping(s.t1))
    case s: LeftOr => s.copy(t = s.t.map(mapping))
    case s: LeftImplies => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: LeftIff => s.copy(t1 = mapping(s.t1))
    case s: LeftNot => s.copy(t1 = mapping(s.t1))
    case s: LeftForall => s.copy(t1 = mapping(s.t1))
    case s: LeftExists => s.copy(t1 = mapping(s.t1))
    case s: LeftExistsOne => s.copy(t1 = mapping(s.t1))
    case s: RightAnd => s.copy(t = s.t.map(mapping))
    case s: RightOr => s.copy(t1 = mapping(s.t1))
    case s: RightImplies => s.copy(t1 = mapping(s.t1))
    case s: RightIff => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: RightNot => s.copy(t1 = mapping(s.t1))
    case s: RightForall => s.copy(t1 = mapping(s.t1))
    case s: RightExists => s.copy(t1 = mapping(s.t1))
    case s: RightExistsOne => s.copy(t1 = mapping(s.t1))
    case s: Weakening => s.copy(t1 = mapping(s.t1))
    case s: LeftRefl => s.copy(t1 = mapping(s.t1))
    case s: RightRefl => s
    case s: LeftSubstEq => s.copy(t1 = mapping(s.t1))
    case s: RightSubstEq => s.copy(t1 = mapping(s.t1))
    case s: LeftSubstIff => s.copy(t1 = mapping(s.t1))
    case s: RightSubstIff => s.copy(t1 = mapping(s.t1))
    case s: SCSubproof => s.copy(premises = s.premises.map(mapping))
    case s: InstFunSchema => s.copy(t1 = mapping(s.t1))
    case s: InstPredSchema => s.copy(t1 = mapping(s.t1))
  }

  /**
   * Flattens a proof recursively; in other words it removes all occurrences of [[SCSubproof]].
   * Because subproofs imports can be rewritten, [[Rewrite]] steps may be inserted where that is necessary.
   * The order of proof steps is preserved, indices of premises are adapted to reflect the new sequence.
   * @param proof the proof to be flattened
   * @return the flattened proof
   */
  def flattenProof(proof: SCProof): SCProof = {
    def flattenProofRecursive(steps: IndexedSeq[SCProofStep], topPremises: IndexedSeq[(Int, Sequent)], offset: Int): IndexedSeq[SCProofStep] = {
      val (finalAcc, _) = steps.foldLeft((IndexedSeq.empty[SCProofStep], IndexedSeq.empty[(Int, Sequent)])) { case ((acc, localToGlobal), step) =>
        def resolve(i: Int): (Int, Sequent) = if(i >= 0) localToGlobal(i) else topPremises(-i - 1)
        val newAcc = step match {
          case SCSubproof(subProof, subPremises, _) =>
            val (rewrittenPremises, rewrittenSeq) = subPremises.zipWithIndex.flatMap { case (i, j) =>
              val (k, sequent) = resolve(i)
              val imported = subProof.imports(j)
              if(sequent != imported) {
                Some((Rewrite(imported, k), -(j - 1) -> imported))
              } else {
                None
              }
            }.unzip
            val rewrittenMap = rewrittenSeq.zipWithIndex.map { case ((i, sequent), j) => i -> (offset + acc.size + j, sequent) }.toMap
            val childTopPremises = subPremises.map(i => rewrittenMap.getOrElse(i, resolve(i))).toIndexedSeq
            acc ++ rewrittenPremises ++ flattenProofRecursive(subProof.steps, childTopPremises, offset + acc.size + rewrittenPremises.size)
          case _ =>
            acc :+ mapPremises(step, i => resolve(i)._1)
        }
        (newAcc, localToGlobal :+ (offset + newAcc.size - 1, step.bot))
      }
      finalAcc
    }
    SCProof(flattenProofRecursive(proof.steps, proof.imports.zipWithIndex.map { case (imported, i) => (-i - 1, imported) }, 0), proof.imports)
  }

  /**
   * Eliminates all steps that are not indirectly referenced by the conclusion (last step) of the proof.
   * This procedure is applied recursively on all subproofs. The elimination of unused top-level imports can be configured.
   * The order of proof steps is preserved, indices of premises are adapted to reflect the new sequence.
   * @param proof the proof to be simplified
   * @param eliminateTopLevelDeadImports whether the unused top-level imports should be eliminated as well
   * @return the proof with dead steps eliminated
   */
  def deadStepsElimination(proof: SCProof, eliminateTopLevelDeadImports: Boolean = true): SCProof = {
    def deadStepsEliminationInternal(proof: SCProof, eliminateDeadImports: Boolean): (SCProof, IndexedSeq[Int]) = {
      // We process the leaves first, otherwise we could miss dead branches (subproofs that more imports than necessary)
      val processedSteps = proof.steps.map {
        case SCSubproof(sp, premises, display) =>
          val (newSubProof, newImportsIndices) = deadStepsEliminationInternal(sp, true)
          SCSubproof(newSubProof, newImportsIndices.map(premises), display)
        case other => other
      }
      val graph = processedSteps.map(_.premises)
      val nodes = graph.indices
      def bfs(visited: Set[Int], toVisit: Set[Int]): Set[Int] = {
        if(toVisit.nonEmpty) {
          val next = toVisit.flatMap(graph).diff(visited)
          bfs(visited ++ next, next.filter(_ >= 0))
        } else {
          visited
        }
      }
      val conclusionNode = nodes.last // Must exist by assumption
      val visited = bfs(Set(conclusionNode), Set(conclusionNode))
      val newNodes = nodes.filter(visited.contains)
      val newImports = proof.imports.indices.map(i => -(i + 1)).filter(i => !eliminateDeadImports || visited.contains(i))
      val newImportsIndices = newImports.map(i => -(i + 1))
      val oldToNewStep = newNodes.zipWithIndex.toMap
      val oldToNewImport = newImports.zipWithIndex.map { case (i, j) => (i, -(j + 1)) }.toMap
      val map = oldToNewStep ++ oldToNewImport
      val newSteps = newNodes.map(processedSteps).map(step => mapPremises(step, map))
      val newProof = SCProof(newSteps, newImportsIndices.map(proof.imports))
      (newProof, newImportsIndices)
    }
    val (newProof, _) = deadStepsEliminationInternal(proof, eliminateTopLevelDeadImports)
    newProof
  }

  /**
   * Removes proof steps that are identified to be redundant. The registered simplifications are the following:
   * <ul>
   * <li>Double/fruitless rewrites/weakening</li>
   * <li>Fruitless instantiations</li>
   * <li>Useless cut</li>
   * </ul>
   * This procedure may need to be called several times; it is guaranteed that a fixed point will eventually be reached.
   * Imports will not change, dead branches will be preserved (but can still be simplified).
   * @param proof the proof to be simplified
   * @return the simplified proof
   */
  def simplifyProof(proof: SCProof): SCProof = {
    def isSequentSubset(subset: Sequent, superset: Sequent): Boolean =
      isSubset(subset.left, superset.left) && isSubset(subset.right, superset.right)
    def schematicPredicatesLabels(sequent: Sequent): Set[SchematicVarOrPredLabel] =
      (sequent.left ++ sequent.right).flatMap(_.schematicPredicateLabels)
    def schematicTermLabels(sequent: Sequent): Set[SchematicTermLabel] =
      (sequent.left ++ sequent.right).flatMap(_.schematicTermLabels)
    def freeSchematicTerms(sequent: Sequent): Set[SchematicTermLabel] =
      (sequent.left ++ sequent.right).flatMap(_.freeSchematicTermLabels)
    val (newSteps, _) = proof.steps.zipWithIndex.foldLeft((IndexedSeq.empty[SCProofStep], IndexedSeq.empty[Int])) { case ((acc, map), (oldStep, i)) =>
      def resolveLocal(j: Int): Int = {
        require(j < i)
        if(j >= 0) map(j) else j
      }
      def getSequentLocal(j: Int): Sequent = {
        require(j < i)
        if(j >= 0) acc(map(j)).bot else proof.getSequent(j)
      }
      object LocalStep {
        def unapply(j: Int): Option[SCProofStep] = {
          require(j < i)
          if(j >= 0) Some(acc(map(j))) else None
        }
      }
      val step = mapPremises(oldStep, resolveLocal)
      val either: Either[SCProofStep, Int] = step match {
        // General unary steps
        case _ if step.premises.sizeIs == 1 && getSequentLocal(step.premises.head) == step.bot =>
          Right(step.premises.head)
        case _ if !step.isInstanceOf[Rewrite] && step.premises.sizeIs == 1 && isSameSequent(getSequentLocal(step.premises.head), step.bot) =>
          Left(Rewrite(step.bot, step.premises.head))
        case _ if !step.isInstanceOf[Rewrite] && !step.isInstanceOf[Weakening]
          && step.premises.sizeIs == 1 && isSequentSubset(getSequentLocal(step.premises.head), step.bot) =>
          Left(Weakening(step.bot, step.premises.head))
        // Recursive
        case SCSubproof(sp, premises, display) =>
          Left(SCSubproof(simplifyProof(sp), premises, display))
        // Double rewrite
        case Rewrite(bot1, LocalStep(Rewrite(bot2, t2))) if isSameSequent(bot1, bot2) =>
          Left(Rewrite(bot1, t2))
        // Double weakening
        case Weakening(bot1, LocalStep(Weakening(bot2, t2))) if isSequentSubset(bot2, bot1) =>
          Left(Weakening(bot1, t2))
        // Rewrite and weakening
        case Weakening(bot1, LocalStep(Rewrite(_, t2))) if isSequentSubset(getSequentLocal(t2), bot1) =>
          Left(Weakening(bot1, t2))
        // Weakening and rewrite
        case Rewrite(bot1, LocalStep(Weakening(_, t2))) if isSequentSubset(getSequentLocal(t2), bot1) =>
          Left(Weakening(bot1, t2))
        // Hypothesis and rewrite
        case Rewrite(bot1, LocalStep(Hypothesis(_, phi))) if bot1.left.contains(phi) && bot1.right.contains(phi) =>
          Left(Hypothesis(bot1, phi))
        // Hypothesis and weakening
        case Weakening(bot1, LocalStep(Hypothesis(_, phi))) if bot1.left.contains(phi) && bot1.right.contains(phi) =>
          Left(Hypothesis(bot1, phi))
        // Useless cut
        case Cut(bot, _, t2, phi) if bot.left.contains(phi) =>
          Left(Weakening(bot, t2))
        case Cut(bot, t1, _, phi) if bot.right.contains(phi) =>
          Left(Weakening(bot, t1))
        // Fruitless instantiation
        case InstPredSchema(bot, t1, _) if isSameSequent(bot, getSequentLocal(t1)) =>
          Left(Rewrite(bot, t1))
        case InstFunSchema(bot, t1, _) if isSameSequent(bot, getSequentLocal(t1)) =>
          Left(Rewrite(bot, t1))
        // Instantiation simplification
        case InstPredSchema(bot, t1, insts) if !insts.keySet.subsetOf(schematicPredicatesLabels(getSequentLocal(t1))) =>
          val newInsts = insts -- insts.keySet.diff(schematicPredicatesLabels(getSequentLocal(t1)))
          Left(InstPredSchema(bot, t1, newInsts))
        case InstFunSchema(bot, t1, insts) if !insts.keySet.subsetOf(schematicTermLabels(getSequentLocal(t1))) =>
          val newInsts = insts -- insts.keySet.diff(schematicTermLabels(getSequentLocal(t1)))
          Left(InstFunSchema(bot, t1, newInsts))
        case other => Left(other)
      }
      either match {
        case Left(newStep) => (acc :+ newStep, map :+ acc.size)
        case Right(index) => (acc :+ oldStep, map :+ index)
      }
    }
    SCProof(newSteps, proof.imports)
  }

  /**
   * Attempts to factor the premises such that the first occurrence of a proven sequent is used.
   * This procedure is greedy.
   * Unused proof steps will not be removed. Use [[deadStepsElimination]] for that.
   * @param proof the proof to be factored
   * @return the factored proof
   */
  def factorProof(proof: SCProof): SCProof = {
    val (initialMap, initialCache) = proof.imports.zipWithIndex.foldLeft((Map.empty[Int, Int], Map.empty[Sequent, Int])) { case ((map, cache), (sequent, i)) =>
      val originalIndex = -(i + 1)
      cache.get(sequent) match {
        case Some(existingIndex) => (map + (originalIndex -> existingIndex), cache)
        case None => (map + (originalIndex -> originalIndex), cache + (sequent -> originalIndex))
      }
    }
    val (newSteps, _, _) = proof.steps.zipWithIndex.foldLeft((IndexedSeq.empty[SCProofStep], initialMap, initialCache)) { case ((acc, map, cache), (step, i)) =>
      val sequent = step.bot
      val mappedStep = mapPremises(step, map) match {
        case SCSubproof(sp, premises, display) =>
          SCSubproof(factorProof(sp), premises, display)
        case other => other
      }
      val (newMap, newCache) = cache.get(sequent) match {
        case Some(existingIndex) => (map + (i -> existingIndex), cache)
        case None => (map + (i -> i), cache + (sequent -> i))
      }
      (acc :+ mappedStep, newMap, newCache)
    }
    SCProof(newSteps, proof.imports)
  }

  /**
   * Optimizes a proof by applying all the available reduction rules until a fixed point is reached.
   * @param proof the proof to be optimized
   * @return the optimized proof
   */
  def optimizeProofIteratively(proof: SCProof): SCProof = {
    def optimizeFixedPoint(proof: SCProof): SCProof = {
      val optimized = deadStepsElimination(factorProof(simplifyProof(proof)))
      if(optimized == proof) optimized else optimizeFixedPoint(optimized)
    }
    optimizeFixedPoint(flattenProof(proof))
  }

}
