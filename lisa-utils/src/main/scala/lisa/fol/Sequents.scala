package lisa.fol

//import lisa.kernel.proof.SequentCalculus.Sequent

import scala.annotation.showAsInfix

trait Sequents extends Common {


  case class Sequent(left:Set[Formula], right:Set[Formula]) extends LisaObject[Sequent] with Absolute{
    def underlying:lisa.kernel.proof.SequentCalculus.Sequent = lisa.kernel.proof.SequentCalculus.Sequent(left.map(_.underlying), right.map(_.underlying))

    def allSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.allSchematicLabels)
    def freeSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.freeSchematicLabels)
    def substitute[S <: LisaObject[S]](map: Map[SchematicLabel[S], S]): Sequent = Sequent(left.map(_.substitute(map)), right.map(_.substitute(map)))

    infix def +<<(f: Formula): Sequent = this.copy(left = this.left + f)
    infix def -<<(f: Formula): Sequent = this.copy(left = this.left - f)
    infix def +>>(f: Formula): Sequent = this.copy(right = this.right + f)
    infix def ->>(f: Formula): Sequent = this.copy(right = this.right - f)
    infix def ++<<(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left)
    infix def --<<(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left)
    infix def ++>>(s1: Sequent): Sequent = this.copy(right = this.right ++ s1.right)
    infix def -->>(s1: Sequent): Sequent = this.copy(right = this.right -- s1.right)
    infix def ++(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left, right = this.right ++ s1.right)
    infix def --(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left, right = this.right -- s1.right)
/*
    infix def removeLeft(f: Formula): Sequent = this.copy(left = this.left.filterNot(isSame(_, f)))
    infix def removeRight(f: Formula): Sequent = this.copy(right = this.right.filterNot(isSame(_, f)))
    infix def removeAllLeft(s1: Sequent): Sequent = this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))))
    infix def removeAllLeft(s1: Set[Formula]): Sequent = this.copy(left = this.left.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Sequent): Sequent = this.copy(right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Set[Formula]): Sequent = this.copy(right = this.right.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAll(s1: Sequent): Sequent = this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))), right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
  */
  }

  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  given Conversion[Formula, Sequent] = f => Sequent(Set.empty, Set(f))

}
