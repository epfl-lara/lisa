package lisa.fol

import scala.annotation.showAsInfix

trait Sequents extends Common {


  class Sequent(left:Set[Formula], right:Set[Formula]) extends LisaObject[Sequent] with Absolute{
    def underlying:lisa.kernel.proof.SequentCalculus.Sequent = lisa.kernel.proof.SequentCalculus.Sequent(left.map(_.underlying), right.map(_.underlying))

    def allSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.allSchematicLabels)
    def freeSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.freeSchematicLabels)
    def substitute[S <: LisaObject[S]](map: Map[SchematicLabel[S], S]): Sequent = Sequent(left.map(_.substitute(map)), right.map(_.substitute(map)))
  }

}
