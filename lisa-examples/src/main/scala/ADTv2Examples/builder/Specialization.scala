package ADTv2Examples.builder

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

object Specialization extends lisa.Main {

  val boxUnit = box.specialize(unit)
  val listNat = list.specialize(nat)
  val optionBoxUnit = option.specialize(boxUnit)

  section("Specialized ADTs")
  show(boxUnit.induction)
  show(listNat.induction)
  show(optionBoxUnit.elim)

  section("Specialized constructors")
  show(pack.specialize(unit).intro)
  show(pack.specialize(unit).introApp)
  show(cons.specialize(nat).intro)

  section("Specialized recursive functions")
  show(length.specialize(nat).intro)
  show(length.specialize(unit).intro)
}
