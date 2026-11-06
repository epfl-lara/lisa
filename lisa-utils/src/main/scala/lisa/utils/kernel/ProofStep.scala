package lisa.utils.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.Sequent

sealed trait ProofStep:
  val statement: Sequent
  val premises: Array[Int]

object ProofStep:
  /**
   * Remap every premise reference without changing the inference.
   */
  def mapPremises(step: ProofStep, f: Int => Int): ProofStep = step match
    case s: Discharge => s.copy(premise = f(s.premise), justification = f(s.justification))
    case s: Restate => s.copy(premise = f(s.premise))
    case s: Cut => s.copy(premise1 = f(s.premise1), premise2 = f(s.premise2))
    case s: LeftAnd => s.copy(premise = f(s.premise))
    case s: LeftOr => s.copy(premises = s.premises.map(f))
    case s: LeftImplies => s.copy(premise1 = f(s.premise1), premise2 = f(s.premise2))
    case s: LeftIff => s.copy(premise = f(s.premise))
    case s: LeftNot => s.copy(premise = f(s.premise))
    case s: LeftForall => s.copy(premise = f(s.premise))
    case s: LeftExists => s.copy(premise = f(s.premise))
    case s: RightAnd => s.copy(premises = s.premises.map(f))
    case s: RightOr => s.copy(premise = f(s.premise))
    case s: RightImplies => s.copy(premise = f(s.premise))
    case s: RightIff => s.copy(premise1 = f(s.premise1), premise2 = f(s.premise2))
    case s: RightNot => s.copy(premise = f(s.premise))
    case s: RightForall => s.copy(premise = f(s.premise))
    case s: RightExists => s.copy(premise = f(s.premise))
    case s: RightEpsilon => s.copy(premise = f(s.premise))
    case s: Weakening => s.copy(premise = f(s.premise))
    case s: LeftRefl => s.copy(premise = f(s.premise))
    case s: LeftSubstEq => s.copy(premise = f(s.premise))
    case s: RightSubstEq => s.copy(premise = f(s.premise))
    case s: InstSchema => s.copy(premise = f(s.premise))
    case _: Sorry | _: Axiom | _: Assume | _: Definition | _: RestateTrue | _: Hypothesis | _: RightRefl => step

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

object LeftOr:
  def apply(statement: Sequent, premises: Seq[Int], disjuncts: Seq[Expression]): LeftOr =
    new LeftOr(statement, premises.toArray, disjuncts)

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

object RightAnd:
  def apply(statement: Sequent, premises: Seq[Int], conjuncts: Seq[Expression]): RightAnd =
    new RightAnd(statement, premises.toArray, conjuncts)

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
