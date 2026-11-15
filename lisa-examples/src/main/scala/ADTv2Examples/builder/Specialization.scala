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
  show(list.induction)
  show(option.elim)

  section("Specialized constructors")
  show(pack.intro)
  show(pack.introApp)
  show(cons.intro)

  section("Specialized recursive functions")
  show(length.intro)
  show(length.intro)

  section("More complex specialization")

  // show(union.induction)
  // show(union.induction(bool))
  // show(union.induction(bool, unit))
}
