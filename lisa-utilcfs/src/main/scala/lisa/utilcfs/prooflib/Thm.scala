package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*

final case class Thm(statement: Sequent, kernel: K.Thm):
  def kernelStatement: K.Sequent = kernel.statement
  def left: Set[Expr[Prop]] = statement.left
  def right: Set[Expr[Prop]] = statement.right
  def leftK: Set[K.Expression] = kernel.statement.left
  def rightK: Set[K.Expression] = kernel.statement.right

object Thm:
  def apply(kernel: K.Thm): Thm =
    Thm(Sequent(kernel.statement.left.map(liftFormula), kernel.statement.right.map(liftFormula)), kernel)

  def liftFormula(expression: K.Expression): Expr[Prop] =
    liftExpression(expression).asInstanceOf[Expr[Prop]]

  given asKernel: Conversion[Thm, K.Thm] = _.kernel
