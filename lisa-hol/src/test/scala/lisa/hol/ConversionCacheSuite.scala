package lisa.hol

import org.scalatest.funsuite.AnyFunSuite

class ConversionCacheSuite extends AnyFunSuite:
  test("cache only successful conversions and tolerate recursive fills"):
    val cache = new Import.ConversionCache[Int, Int](1)
    var calls = 0
    def compute(): Int = { calls += 1; 7 }
    assert(cache(1)(cache(2)(compute())) == 7)
    assert(cache(1)(compute()) == 7 && calls == 1)
    assertThrows[IllegalArgumentException](cache(3)(throw new IllegalArgumentException("failed")))
    assert(cache(3)(9) == 9)
    cache.clear()
    assert(cache(1)(compute()) == 7 && calls == 2)
