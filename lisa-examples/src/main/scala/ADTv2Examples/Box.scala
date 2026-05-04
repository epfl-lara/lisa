import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}
import lisa.maths.SetTheory.Functions.Pi.{->:}

object Box extends lisa.Main {

  val A = variable[Ind]
  val B = variable[Ind]
  val x = variable[Ind]
  val f = variable[Ind]
  val content = variable[Ind]

  val box = API.defineAST(
    name = "box",
    typeVars = Seq("A"),
    constructors = Seq(
      ("pack", Seq(("content", "A")))
    )
  )
  val pack = box.constructors(0)

  // val get = fun(box, A):
  //   Case(pack, content):
  //     content
  val get = recFun(box, A) { self =>
    Case(pack, content):
      content
  }

  val unit = API.defineAST(
    name = "unit",
    typeVars = Seq.empty,
    constructors = Seq(
      ("star", Seq.empty)
    )
  )
  val star = unit.constructors(0)

  val box_unit = box(unit)
  val boxedStar = pack(unit) * star

  println(s"box: ${box}")
  println(s"box(unit): ${box_unit}")
  println(s"pack: ${pack}")
  println(s"pack(unit): ${pack(unit)}")
  println(s"get: ${get}")
  println(s"get(unit): ${get(unit)}")

  section("Summary of the ADT")
  show(pack.intro)
  show(pack.introApp)
  show(get.intro)
  show(get.elim(pack))

  section("Instantiation of ADT theorems")
  show(pack(unit).intro)
  show(pack(unit).introApp)
  show(get(unit).intro)
  show(get.elim(pack))

  // Allowed:
  //   - define a polymorphic ADT family box[A]
  //   - instantiate it with a concrete term unit
  //   - define a polymorphic function get[A] : box[A] -> A
  //   - specialize generic theorems at A := unit
  //
  // Limitation shown by this example:
  //   - the specialized theorem for pack(unit) proves membership in the schematic
  //     term boxTerm, not directly in box(unit)
  //   - likewise get(unit) is typed over boxTerm, not directly over box(unit)
  //   - generic Typecheck automation on specialized terms like pack(unit) or get(unit)
  //     does not reconstruct the concrete instantiated type box(unit) automatically
  //
  // So the following direct lemma is intentionally left commented:
  //
  // val packTypingAtUnitConcrete = Lemma(boxedStar :: box_unit) {
  //   have(thesis) by Tautology.from(pack.introApp of (A := unit, content := star), star.intro)
  // }
  //
  // Not allowed semantically:
  //   - pretending that content : A is automatically also of type unit for every A
  //
  // For example, this would be a bad definition:
  //
  // val badGet = fun(box, unit):
  //   Case(pack, content):
  //     content
  //
  // because the branch body has type A, not unit in general.

}
