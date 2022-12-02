package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Library
import lisa.utils.Printer
import sourcecode.Text.generate
object ProofTest extends lisa.Main {


  val x: VariableLabel = variable
  val y: VariableLabel = variable
  val z: VariableLabel = variable
  val h: VariableFormulaLabel = formulaVariable

  val unorderedPair_symmetry = makeTHM(() |- forall(y, forall(x, unorderedPair(x, y) === unorderedPair(y, x)))) {

      val objectiveA : Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))
      val objectiveB : Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x))

      val part1 = have(objectiveA) subproof {
          val pr0 = have(() |- in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z)) by InstFunSchema(Map(
            x -> LambdaTermTerm(Seq(), y),
            y -> LambdaTermTerm(Seq(), x)))(ax"pairAxiom")
          val pr1 = have(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z) |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by
            RightSubstIff(List((in(z, unorderedPair(y, x)), (x === z) \/ (y === z))),
              LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h))(ax"pairAxiom")
          have(() |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by Cut.withParameters(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z))(pr0, pr1)
          andThen(objectiveA) by RightForall.withParameters(in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)), z)
      }

    val part2 = have(objectiveB) by InstFunSchema(Map(
      x -> LambdaTermTerm(Seq(), unorderedPair(x, y)),
      y -> LambdaTermTerm(Seq(), unorderedPair(y, x))))(ax"extensionalityAxiom")

      have(() |- unorderedPair(x, y) === unorderedPair(y, x)) by ByEquiv(objectiveB.right.head, objectiveA.right.head)(part1, part2)
      andThen(() |- forall(y, forall(x, unorderedPair(x, y) === unorderedPair(y, x)))) by GeneralizeToForallNoForm(x, y)

      showCurrentProof()
    }
  show
}