package ADTv2Examples.builder

import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.ADTv2.support.Time

object DebugADTs extends lisa.Main {

  private val debugTypeHeavyTypePool: Seq[Expr[Ind]] =
    Seq(unit, nat, bool, list(nat), option(unit))

  private def instantiatedTypeArgsFor(adt: lisa.maths.SetTheory.Types.ADTv2.interface.ADT[?]): Seq[Expr[Ind]] =
    adt.typeVariablesSeq.indices.map(index => debugTypeHeavyTypePool(index % debugTypeHeavyTypePool.size))

  // Time.reset()
  val t0 = Time.get()

  val typeHeavyArgs = instantiatedTypeArgsFor(debugTypeHeavy)
  val _ = debugTypeHeavy.induction(typeHeavyArgs.head, typeHeavyArgs.tail*)
  val _ = debugTypeHeavy.elim(typeHeavyArgs.head, typeHeavyArgs.tail*)
  val _ = debugTypeHeavy.constructors.head.intro(typeHeavyArgs.head, typeHeavyArgs.tail*)
  val _ = debugTypeHeavy.constructors.head.introApp(typeHeavyArgs.head, typeHeavyArgs.tail*)


  val t1 = Time.get()


  val _ = debugConstructorHeavy.induction(unit)
  val _ = debugConstructorHeavy.elim(unit)
  val _ = debugConstructorHeavy.injectivity(
    debugConstructorHeavy.constructors(0),
    debugConstructorHeavy.constructors(1),
    unit
  )
  val _ = debugConstructorHeavy.constructors.head.intro(unit)


  val _ = debugArgumentHeavy.induction(unit)
  val _ = debugArgumentHeavy.elim(unit)
  val _ = debugArgumentHeavy.constructors.head.intro(unit)
  val _ = debugArgumentHeavy.constructors.head.introApp(unit)


  val _ = debugRecursive.induction(unit)
  val _ = debugRecursive.elim(unit)
  val _ = debugRecursive.injectivity(
    debugRecursive.constructors(0),
    debugRecursive.constructors.last,
    unit
  )
  val _ = debugRecursive.constructors.last.intro(unit)
  val _ = debugRecursive.constructors.last.introApp(unit)


  val t4 = Time.get()

}
