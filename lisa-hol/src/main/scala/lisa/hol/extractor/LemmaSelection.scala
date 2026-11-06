package lisa.hol.extractor

import java.io.File
import java.util.Arrays
import scala.collection.mutable
import scala.util.Using

/** Select shared proof boundaries without decoding terms or theorem statements. */
object LemmaSelection:
  final case class Result(ids: Set[Long], records: Int, reachable: Int)

  /** Record preprocessing cost independently of theorem reconstruction. */
  final case class Timing(enabled: Boolean, elapsedNanos: Long, records: Int, reachable: Int, selectedLemmas: Int):
    def elapsedSeconds: Double = elapsedNanos / 1e9

  /**
   * Run the optional prepass, report its cost, and notify the caller before reconstruction.
   *
   * @throws IllegalArgumentException if enabled selection encounters invalid dependencies
   * @throws java.io.IOException if reading the proof store fails
   */
  @throws[IllegalArgumentException]
  @throws[java.io.IOException]
  def prepare(proofs: File, roots: Set[Long], enabled: Boolean)(onComplete: Timing => Unit = _ => ()): (Result, Timing) =
    val started = System.nanoTime()
    val result = if enabled then analyze(proofs, roots) else Result(Set.empty, 0, 0)
    val timing = Timing(enabled, if enabled then System.nanoTime() - started else 0L, result.records, result.reachable, result.ids.size)
    println("HOL_PREPROCESSING_METRICS " + ujson.Obj(
      "precompute_lemmas" -> enabled,
      "preprocessing_seconds" -> timing.elapsedSeconds,
      "selected_lemmas" -> timing.selectedLemmas,
      "records" -> timing.records,
      "reachable" -> timing.reachable
    ))
    onComplete(timing)
    (result, timing)

  /**
   * Promote steps reached from two distinct proof contexts, then propagate from
   * each promoted step as a new context. Named theorems and definitions already
   * form boundaries. Sharing within a single context needs no extra lemma.
   *
   * Read only through the largest requested root. Reject missing roots or
   * premises, forward references and non-increasing IDs in that prefix.
   * Selection is a retention hint, not a certificate of proof validity.
   *
   * @throws IllegalArgumentException if IDs, references or dependency headers are invalid
   * @throws java.io.IOException if reading fails
   */
  @throws[IllegalArgumentException]
  @throws[java.io.IOException]
  def analyze(proofs: File, roots: Set[Long]): Result =
    require(roots.forall(_ >= 0), "Lemma roots must be non-negative.")
    if roots.isEmpty then return Result(Set.empty, 0, 0)

    val ids = new mutable.ArrayBuilder.ofLong
    val first = new mutable.ArrayBuilder.ofLong
    val second = new mutable.ArrayBuilder.ofLong
    val definitions = new mutable.ArrayBuilder.ofBoolean
    val limit = roots.max
    Using.resource(new TraceReader(proofs)): reader =>
      var last = -1L
      var ended = false
      while last < limit && !ended do
        TraceHeader.readDependencies(reader) match
          case None => ended = true
          case Some(record) =>
            val id = record.header.id
            require(id > last, s"Non-increasing proof ID $id after $last.")
            require(record.first < id && record.second < id, s"Non-earlier premise at $id.")
            ids += id
            first += record.first
            second += record.second
            definitions += record.header.isDefinition
            last = id
            reader.skipLine()

    partition(ids.result(), first.result(), second.result(), definitions.result(), roots)

  private def partition(ids: Array[Long], first: Array[Long], second: Array[Long], definitions: Array[Boolean], roots: Set[Long]): Result =
    val mandatory = definitions
    roots.foreach: id =>
      val node = Arrays.binarySearch(ids, id)
      require(node >= 0, s"Missing named proof $id.")
      mandatory(node) = true

    def resolve(premise: Long, node: Int): Int =
      if premise == -1 then -1
      else
        val found = Arrays.binarySearch(ids, 0, node, premise)
        require(found >= 0, s"Missing premise $premise at ${ids(node)}.")
        found

    val left = new Array[Int](ids.length)
    val right = new Array[Int](ids.length)
    for node <- ids.indices do
      left(node) = resolve(first(node), node)
      right(node) = if second(node) == first(node) then -1 else resolve(second(node), node)

    // -1 means unreachable; -2 means reached from more than one context.
    val owners = Array.fill(ids.length)(-1)
    val selected = Set.newBuilder[Long]
    var reachable = 0
    var node = ids.length - 1
    while node >= 0 do
      val owner =
        if mandatory(node) then node
        else if owners(node) == -2 then
          selected += ids(node)
          node
        else owners(node)
      if owner >= 0 then
        reachable += 1
        def inherit(parent: Int): Unit =
          if parent >= 0 then
            if owners(parent) == -1 then owners(parent) = owner
            else if owners(parent) != owner then owners(parent) = -2
        inherit(left(node))
        inherit(right(node))
      node -= 1
    Result(selected.result(), ids.length, reachable)
