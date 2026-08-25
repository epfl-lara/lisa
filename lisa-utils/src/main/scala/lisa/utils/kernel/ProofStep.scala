package lisa.utils.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.Sequent

sealed trait ProofStep:
  val statement: Sequent
  val premises: Array[Int]

case class Sorry(statement: Sequent) extends ProofStep:
  val premises: Array[Int] = Array.empty

case class Axiom(statement: Sequent) extends ProofStep:
  val premises: Array[Int] = Array.empty

case class Assume(statement: Sequent) extends ProofStep:
  val premises: Array[Int] = Array.empty

case class Discharge(statement: Sequent, premise: Int, justification: Int) extends ProofStep:
  val premises: Array[Int] = Array(premise, justification)

case class Definition(statement: Sequent, cst: Constant, vars: Seq[Variable], exp: Expression) extends ProofStep:
  val premises: Array[Int] = Array.empty

case class Restate(statement: Sequent, premise: Int) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RestateTrue(statement: Sequent) extends ProofStep:
  val premises: Array[Int] = Array.empty

case class Hypothesis(statement: Sequent, phi: Expression) extends ProofStep:
  val premises: Array[Int] = Array.empty

case class Cut(statement: Sequent, premise1: Int, premise2: Int, phi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise1, premise2)

case class LeftAnd(statement: Sequent, premise: Int, phi: Expression, psi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class LeftOr(statement: Sequent, premises: Array[Int], disjuncts: Seq[Expression]) extends ProofStep

case class LeftImplies(statement: Sequent, premise1: Int, premise2: Int, phi: Expression, psi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise1, premise2)

case class LeftIff(statement: Sequent, premise: Int, phi: Expression, psi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class LeftNot(statement: Sequent, premise: Int, phi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class LeftForall(statement: Sequent, premise: Int, phi: Expression, x: Variable, t: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class LeftExists(statement: Sequent, premise: Int, phi: Expression, x: Variable) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightAnd(statement: Sequent, premises: Array[Int], conjuncts: Seq[Expression]) extends ProofStep

case class RightOr(statement: Sequent, premise: Int, phi: Expression, psi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightImplies(statement: Sequent, premise: Int, phi: Expression, psi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightIff(statement: Sequent, premise1: Int, premise2: Int, phi: Expression, psi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise1, premise2)

case class RightNot(statement: Sequent, premise: Int, phi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightForall(statement: Sequent, premise: Int, phi: Expression, x: Variable) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightExists(statement: Sequent, premise: Int, phi: Expression, x: Variable, t: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightEpsilon(statement: Sequent, premise: Int, phi: Expression, x: Variable, t: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class Weakening(statement: Sequent, premise: Int) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class LeftRefl(statement: Sequent, premise: Int, phi: Expression) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightRefl(statement: Sequent, phi: Expression) extends ProofStep:
  val premises: Array[Int] = Array.empty

case class LeftSubstEq(
    statement: Sequent,
    premise: Int,
    equals: Seq[(Expression, Expression)],
    lambdaPhi: (Seq[Variable], Expression)
) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class RightSubstEq(
    statement: Sequent,
    premise: Int,
    equals: Seq[(Expression, Expression)],
    lambdaPhi: (Seq[Variable], Expression)
) extends ProofStep:
  val premises: Array[Int] = Array(premise)

case class InstSchema(statement: Sequent, premise: Int, subst: Map[Variable, Expression]) extends ProofStep:
  val premises: Array[Int] = Array(premise)
