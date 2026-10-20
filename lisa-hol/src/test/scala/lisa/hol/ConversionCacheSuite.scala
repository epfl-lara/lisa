package lisa.hol

import org.scalatest.funsuite.AnyFunSuite

class ConversionCacheSuite extends AnyFunSuite:
  test("cache only successful conversions and tolerate recursive fills"):
    val cache = lisa.utils.collection.BoundedCache.fifo[Int, Int](1)
    var calls = 0
    def compute(): Int = { calls += 1; 7 }
    assert(cache.getOrElseUpdate(1)(cache.getOrElseUpdate(2)(compute())) == 7)
    assert(cache.getOrElseUpdate(1)(compute()) == 7 && calls == 1)
    assertThrows[IllegalArgumentException](cache.getOrElseUpdate(3)(throw new IllegalArgumentException("failed")))
    assert(cache.getOrElseUpdate(3)(9) == 9)
    cache.clear()
    assert(cache.getOrElseUpdate(1)(compute()) == 7 && calls == 2)
