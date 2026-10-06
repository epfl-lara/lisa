package lisa.utils.collection

import org.scalatest.funsuite.AnyFunSuite

class BoundedCacheSuite extends AnyFunSuite:
  test("reject invalid capacities and generation counts"):
    assertThrows[IllegalArgumentException](BoundedCache.fifo[Int, Int](-1))
    assertThrows[IllegalArgumentException](BoundedCache.generational[Int, Int](-1))
    assertThrows[IllegalArgumentException](BoundedCache.generational[Int, Int](1, 0))
    assertThrows[IllegalArgumentException](BoundedCache.generational[Int, Int](Int.MaxValue, 2))

  test("evict FIFO entries without refreshing hits or replacements"):
    val cache = BoundedCache.fifo[Int, String](2)
    cache.put(1, "one")
    cache.put(2, "two")
    assert(cache.get(1).contains("one"))
    cache.put(1, "updated")
    cache.put(3, "three")
    assert(cache.get(1).isEmpty && cache.get(2).contains("two"))
    assert(cache.size == 2 && cache.evictions == 1)

  for count <- Seq(1, 2, 3) do
    test(s"retain full generations until the next insertion rotates ($count generations)"):
      val cache = BoundedCache.generational[Int, Int](2, count)
      for key <- 0 until 2 * count do cache.put(key, key)
      assert(cache.size == 2 * count && cache.evictions == 0)
      for key <- 0 until 2 * count do assert(cache.get(key).contains(key))
      cache.put(0, -1)
      assert(cache.get(0).contains(-1) && cache.size == 2 * count)
      cache.put(2 * count, 99)
      assert(cache.get(0).isEmpty && cache.get(1).isEmpty)
      for key <- 2 until 2 * count do assert(cache.get(key).contains(key))
      assert(cache.size == 2 * count - 1 && cache.evictions == 2)

    test(s"match a reference model through repeated rotations and removals ($count generations)"):
      val capacity = 3
      val cache = BoundedCache.generational[Int, Int](capacity, count)
      var model = Vector.fill(count)(Map.empty[Int, Int])
      var active = 0
      var evicted = 0L
      val random = new scala.util.Random(20260930L + count)
      for operation <- 0 until 2000 do
        val key = random.nextInt(19)
        random.nextInt(6) match
          case 0 =>
            val previous = model.iterator.flatMap(_.get(key)).nextOption()
            assert(cache.remove(key) == previous)
            model = model.map(_ - key)
          case 1 =>
            assert(cache.get(key) == model.iterator.flatMap(_.get(key)).nextOption())
          case 2 if operation % 17 == 0 =>
            cache.clear()
            model = Vector.fill(count)(Map.empty)
            active = 0
            evicted = 0
          case _ =>
            val existing = model.indexWhere(_.contains(key))
            if existing >= 0 then model = model.updated(existing, model(existing).updated(key, operation))
            else
              if model(active).size == capacity then
                active = (active + 1) % count
                evicted += model(active).size
                model = model.updated(active, Map.empty)
              model = model.updated(active, model(active).updated(key, operation))
            cache.put(key, operation)
        assert(cache.size == model.map(_.size).sum)
        assert(cache.size <= capacity * count && cache.evictions == evicted)
        for candidate <- 0 until 19 do
          assert(cache.get(candidate) == model.iterator.flatMap(_.get(candidate)).nextOption())

  for (name, create) <- Seq(
    "FIFO" -> ((n: Int) => BoundedCache.fifo[Int, Int](n)),
    "generational" -> ((n: Int) => BoundedCache.generational[Int, Int](n))
  ) do
    test(s"disable retention at zero capacity ($name)"):
      val cache = create(0)
      var calls = 0
      for _ <- 0 until 3 do assert(cache.getOrElseUpdate(1) { calls += 1; 7 } == 7)
      assert(calls == 3 && cache.size == 0 && cache.evictions == 0)

    test(s"cache successful recursive computations but not exceptions ($name)"):
      val cache = create(1)
      val result = cache.getOrElseUpdate(1):
        cache.put(2, 2)
        cache.put(3, 3)
        1
      assert(result == 1 && cache.get(1).contains(1))
      assert(cache.getOrElseUpdate(1)(throw new AssertionError("cache hit evaluated default")) == 1)
      assertThrows[IllegalStateException](cache.getOrElseUpdate(4)(throw new IllegalStateException("failed")))
      assert(cache.get(4).isEmpty)
      assert(cache.size <= (if name == "FIFO" then 1 else 2))

    test(s"remove entries and reset state without counting explicit removals ($name)"):
      val cache = create(1)
      (1 to 4).foreach(n => cache.put(n, n))
      val evictions = cache.evictions
      assert(cache.remove(4).contains(4) && cache.remove(4).isEmpty)
      assert(cache.evictions == evictions)
      cache.clear()
      assert(cache.size == 0 && cache.evictions == 0)
      cache.put(5, 5)
      assert(cache.get(5).contains(5) && cache.size == 1)
