package lisa.automation.front.predef

import lisa.kernel.proof.SCProof
import lisa.front.fol.FOL.*
import lisa.kernel.proof.SequentCalculus as KSC
import lisa.automation.kernel.SimplePropositionalSolver
import lisa.front.proof.state.ProofEnvironmentDefinitions
import lisa.front.proof.unification.UnificationUtils
import lisa.front.proof.Proof.*

trait PredefTacticsDefinitions {

  case object TacticSolverNative extends TacticGoalFunctional {
    import Notations.*

    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      val steps = SimplePropositionalSolver.solveSequent(proofGoal).steps
      Some((IndexedSeq.empty, () => steps))
    }
  }
  case class TacticRewritePartial(left: Map[Int, Formula] = Map.empty, right: Map[Int, Formula] = Map.empty) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(left.keySet.forall(proofGoal.left.indices.contains) && right.keySet.forall(proofGoal.right.indices.contains)) {
        val rewritten = Sequent(
          proofGoal.left.indices.map(i => left.getOrElse(i, proofGoal.left(i))),
          proofGoal.right.indices.map(i => right.getOrElse(i, proofGoal.right(i)))
        )
        if(isSameSequent(proofGoal, rewritten)) {
          Some((IndexedSeq(rewritten), () => IndexedSeq(KSC.Rewrite(rewritten, -1))))
        } else {
          None
        }
      } else {
        None
      }
    }
  }

  case class TacticRewriteSequent(rewritten: Sequent) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(isSameSequent(proofGoal, rewritten)) {
        Some((IndexedSeq(rewritten), () => IndexedSeq(KSC.Rewrite(proofGoal, -1))))
      } else {
        None
      }
    }
  }

  object TacticalRewrite {
    def apply(left: Map[Int, Formula] = Map.empty, right: Map[Int, Formula] = Map.empty): TacticRewritePartial =
      TacticRewritePartial(left, right)
    def apply(rewritten: Sequent): TacticRewriteSequent = TacticRewriteSequent(rewritten)
  }

  case class TacticWeakenPartial(left: Set[Int] = Set.empty, right: Set[Int] = Set.empty) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(left.forall(proofGoal.left.indices.contains) && right.forall(proofGoal.right.indices.contains)) {
        val weaker = Sequent(
          proofGoal.left.zipWithIndex.filter { case (_, i) => !left.contains(i) }.map { case (f, _) => f },
          proofGoal.right.zipWithIndex.filter { case (_, i) => !right.contains(i) }.map { case (f, _) => f }
        )
        Some((IndexedSeq(weaker), () => IndexedSeq(KSC.Weakening(proofGoal, -1))))
      } else {
        None
      }
    }
  }

  case class TacticWeakenSequent(weaker: Sequent) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      // This can be made powerful with a matching algorithm
      ???
    }
  }

  object TacticalWeaken {
    def apply(left: Set[Int] = Set.empty, right: Set[Int] = Set.empty): TacticWeakenPartial =
      TacticWeakenPartial(left, right)
    //def apply(weaker: Sequent): TacticWeakenSequent = TacticWeakenSequent(weaker)
  }

  case class TacticInstantiateFunctionSchema(sequent: Sequent, assigned: AssignedFunction) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      val map = Seq(assigned)
      val instantiated = Sequent(
        sequent.left.map(formula => instantiateFormulaSchemas(formula, functions = map)),
        sequent.right.map(formula => instantiateFormulaSchemas(formula, functions = map))
      )
      if(isSameSequent(proofGoal, instantiated)) {
        Some((
          IndexedSeq(sequent),
          () => IndexedSeq(KSC.InstFunSchema(proofGoal, -1, Map(toKernel(assigned.schema) -> assigned.lambda)))
        ))
      } else {
        None
      }
    }
  }

  extension (theorem: Theorem) {
    def apply(assigned: AssignedFunction): Theorem = {
      val map: Seq[AssignedFunction] = Seq(assigned)
      val replaced = Sequent(
        theorem.sequent.left.map(formula => instantiateFormulaSchemas(formula, functions = map)),
        theorem.sequent.right.map(formula => instantiateFormulaSchemas(formula, functions = map))
      )
      val scProof = SCProof(
        IndexedSeq(
          KSC.InstFunSchema(replaced, -1, Map(toKernel(assigned.schema) -> assigned.lambda))
        ),
        IndexedSeq(sequentToKernel(theorem.sequent))
      )
      theorem.environment.mkTheorem(replaced, scProof, IndexedSeq(theorem))
    }
    def apply(assigned: AssignedPredicate): Theorem = {
      val map: Seq[AssignedPredicate] = Seq(assigned)
      val replaced = Sequent(
        theorem.sequent.left.map(formula => instantiateFormulaSchemas(formula, predicates = map)),
        theorem.sequent.right.map(formula => instantiateFormulaSchemas(formula, predicates = map))
      )
      val scProof = SCProof(
        IndexedSeq(
          KSC.InstPredSchema(replaced, -1, Map(toKernel(assigned.schema) -> assigned.lambda))
        ),
        IndexedSeq(sequentToKernel(theorem.sequent))
      )
      theorem.environment.mkTheorem(replaced, scProof, IndexedSeq(theorem))
    }

    def rewrite(rewritten: Sequent): Theorem =
      TacticRewriteSequent(theorem.sequent).apply(rewritten).map { case (_, reconstruct) =>
        val scProof = SCProof(reconstruct(), IndexedSeq(sequentToKernel(theorem.sequent)))
        theorem.environment.mkTheorem(rewritten, scProof, IndexedSeq(theorem))
      }.get
  }

  case class TacticInstantiateApplyJustification(justified: Justified) extends TacticGoalFunctionalPruning {
    def apply(proofGoal: Sequent): Option[(IndexedSeq[Either[Sequent, Justified]], ReconstructSteps)] = {
      val patterns = IndexedSeq(PartialSequent(justified.sequent.left, justified.sequent.right))
      val values = IndexedSeq(proofGoal)
      matchIndices(Map.empty, patterns, values).flatMap { selector =>
        // TODO we should instantiate to temporary schemas first otherwise we risk clashing names
        unifyAndResolve(patterns, values, patterns, UnificationContext(), selector).map { case (IndexedSeq(resolved), ctx) =>
          val withFunctions = instantiateSequentSchemas(justified.sequent, ctx.assignedFunctions, Seq.empty, Seq.empty)
          val withFunctionsAndPredicates = instantiateSequentSchemas(withFunctions, Seq.empty, ctx.assignedPredicates, Seq.empty)
          (
            IndexedSeq(Right(justified)),
            () => IndexedSeq(
              KSC.InstFunSchema(
                sequentToKernel(withFunctions),
                -1,
                ctx.assignedFunctions.map(assigned => toKernel(assigned.schema) -> toKernel(assigned.lambda)).toMap,
              ),
              KSC.InstPredSchema(
                sequentToKernel(withFunctionsAndPredicates),
                0,
                ctx.assignedPredicates.map(assigned => toKernel(assigned.schema) -> toKernel(assigned.lambda)).toMap,
              ),
              KSC.Weakening(sequentToKernel(proofGoal), 1),
            ),
          )
        }
      }.headOption
    }
  }

}
