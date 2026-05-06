package ADTv2Examples.builder

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

object Specialization extends lisa.Main {

  val boxUnit = box(unit)
  val listNat = list(nat)
  val optionBoxUnit = option(boxUnit)

  // val boolUnion = union(bool)
  // val boolUnionUnit = union(bool, unit)

  section("Specialized ADTs")
  show(box.semantic.induction)
  show(box.induction)
  show(box.inductionAt(unit))
  show(list.inductionAt(nat))
  show(option.elimAt(boxUnit))

  section("Specialized constructors")
  show(pack.introAt(unit))
  show(pack.introAppAt(unit))
  show(cons.introAt(nat))

  section("Specialized recursive functions")
  show(length.introAt(nat))
  show(length.introAt(unit))

  section("More complex specialization")

  // show(union.induction)
  // show(union.inductionAt(bool))
  // show(union.inductionAt(bool, unit))
}
