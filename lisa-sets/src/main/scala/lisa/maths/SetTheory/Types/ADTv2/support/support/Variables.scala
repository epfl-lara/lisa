package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.K

class UniqueVariable(id: K.Identifier, baseName: String) extends Variable[Ind](id) {
  // override def toString: String = baseName
  override def toString: String = s"$baseName($id)"
}

object UniqueVariable {

  private var existingVariables: Set[Expr[Ind]] = Set.empty

  def apply(name: String, fullname: String): UniqueVariable = {
    val freshId = K.freshId(existingVariables.flatMap(_.freeVars.map(_.id)), fullname)
    val newVariable = new UniqueVariable(freshId, name)
    existingVariables = existingVariables + newVariable
    newVariable
  }

  def apply(name: String): UniqueVariable = apply(name, s"${name}AutoGen")

  def apply(using name: sourcecode.Name)(): UniqueVariable =
    apply(name.value, s"${name.value}AutoGen")

  def save(existing: Expr[Ind]*): Unit = existingVariables = existingVariables ++ existing

  def getNbVars: Int = existingVariables.size

  def getVars: Set[Expr[Ind]] =
    // Return a copy to prevent external modification
    collection.immutable.Set.empty ++ existingVariables

}

object MyVariables {

  // Variables
  val a, b, c, d = variable[Ind]
  val f, g = variable[Ind]
  val k, n, m = variable[Ind]
  val r, s, t = variable[Ind]
  val x, y, z = variable[Ind]
  val α, β = variable[Ind]

  var h: Variable[Ind] = variable[Ind]

  val A, B = variable[Ind]

  // Propositions
  val p, p1, p2, p3, p4 = variable[Prop]
  val q1, q2 = variable[Prop]

  // Predicates
  val P, Q = variable[Ind >>: Prop]
  val schemPred = variable[Ind >>: Prop]
  val P2 = variable[Ind >>: Ind >>: Prop]

  // Constants
  val N: Expr[Ind] = lisa.maths.SetTheory.Ordinals.Integer.ω

}
