package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus.isSameSequent
import lisa.test.ProofCheckerSuite
import lisa.utils.Helpers.*

import scala.collection.immutable.Set

class SequentUtilsTest extends ProofCheckerSuite {
  val simpleSequent: Sequent = s === t |- s === t
  val sequent: Sequent = Set(s === t, t === u) |- Set(s === t, s === u)
  val emptySequent: Sequent = () |- ()

  test("left remove formula") {
    val leftFormula = simpleSequent.left.head
    // plain removal
    assert((simpleSequent -< leftFormula) === (() |- simpleSequent.right))
    // isSame removal
    val sameFormula = leftFormula /\ (s === s)
    assert(!(sameFormula == leftFormula))
    assert(isSame(leftFormula, sameFormula))
    assert((simpleSequent -< sameFormula) === (simpleSequent -< leftFormula))
  }

  test("right remove formula") {
    val rightFormula = simpleSequent.right.head
    // plain removal
    assert((simpleSequent -> rightFormula) === (simpleSequent.left |- ()))
    // isSame removal
    val sameFormula = rightFormula /\ (s === s)
    assert(!(sameFormula == rightFormula))
    assert(isSame(rightFormula, sameFormula))
    assert((simpleSequent -> sameFormula) === (simpleSequent -> rightFormula))
  }

  test("left remove set") {
    assert(sequent --< sequent === (() |- sequent.right))
    val sameLeft = Sequent(sequent.left.map(_ /\ (u === u)), sequent.right)
    assert((sequent --< sameLeft) === (() |- sequent.right))
  }

  test("right remove set") {
    assert((sequent --> sequent) === (sequent.left |- ()))
    val sameRight = Sequent(sequent.left, sequent.right.map(_ /\ (u === u)))
    assert(!(sequent.right === sameRight))
    assert(isSameSet(sequent.right, sameRight.right))
    assert(sequent --> sameRight === (sequent.left |- ()))
  }

  test("sequent remove sequent") {
    val equivalentSequent = Set((s === t) /\ (s === s), t === u) |- Set(s === t, (s === u) /\ (u === u))
    assert(sequent -- equivalentSequent === emptySequent)
  }
}
