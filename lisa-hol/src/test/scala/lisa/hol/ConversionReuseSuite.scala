package lisa.hol

import lisa.hol.Import.Transformers.*
import lisa.hol.HOLHelperTheorems.{One, 𝔹}
import lisa.hol.{core => h}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class ConversionReuseSuite extends AnyFunSuite:
  locally:
    val context = new lisa.hol.extractor.ExtractorContext(Iterator.empty, Iterator.empty)
    try new Import.StepStore()(using context)
    finally context.close()

  test("reuse converted function types without confusing their arguments"):
    resetConversionCache()
    val a = h.TypeVariable("conversion-A")
    val first = h.FunType(a, h.BoolType).toLisaType
    assert(isSame(first, a.toLisaType ->: 𝔹))
    assert(!isSame(first, h.FunType(h.BoolType, a).toLisaType))
    if Config.typeCacheCapacity > 0 then
      assert(first eq h.FunType(a, h.BoolType).toLisaType)

  test("reuse constant instances without confusing polymorphic types"):
    resetConversionCache()
    val raw = h.Constant("=", h.FunType(h.BoolType, h.FunType(h.BoolType, h.BoolType)))
    val term = raw.toLisaTerm
    assert(term == VarsAndFunctions.holeq(𝔹))
    if Config.constantCacheCapacity > 0 then assert(term eq raw.toLisaTerm)
    val a = h.TypeVariable("conversion-equality-A")
    assert(term != h.Constant("=", h.FunType(a, h.FunType(a, h.BoolType))).toLisaTerm)

  test("release frontend objects when conversion reuse is reset"):
    val raw = h.TypeVariable("conversion-reset")
    val first = raw.toLisaType
    resetConversionCache()
    val second = raw.toLisaType
    assert(first == second)
    assert(!(first eq second))

  test("reject undefined types on every lookup without poisoning valid conversions"):
    val name = "conversion-late-type"
    val raw = h.TypeApplication(name, Nil)
    for _ <- 1 to 2 do intercept[NoSuchElementException](raw.toLisaType)
    assert(h.BoolType.toLisaType == 𝔹)

  test("reject undefined constants and malformed instances on every lookup"):
    val name = "conversion-late-constant"
    val raw = h.Constant(name, h.BoolType)
    for _ <- 1 to 2 do
      intercept[NoSuchElementException](raw.toLisaTerm)
      intercept[Import.MalformedConstantInstance](h.Constant("T", h.FunType(h.BoolType, h.BoolType)).toLisaTerm)

  test("evict old conversions without changing their types or variable identifiers"):
    resetConversionCache()
    val raw = h.TypeVariable("conversion-evicted")
    val first = raw.toLisaType
    val variable = h.Variable("conversion-variable", raw).toLisaVar
    for i <- 0 until 5000 do h.TypeVariable(s"conversion-fill-$i").toLisaType
    val second = raw.toLisaType
    assert(first == second)
    if Config.typeCacheCapacity <= 5000 then assert(!(first eq second))
    assert(h.Variable("conversion-variable", raw).toLisaVar.id == variable.id)
    assert(conversionCacheSize <= Config.typeCacheCapacity)
