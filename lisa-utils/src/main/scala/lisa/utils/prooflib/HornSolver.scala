package lisa.utils.prooflib

import scala.collection.mutable

/** Performs forward chaining on definite Horn clauses. */
object HornSolver:

  /** Represents `body => head`. */
  final case class Clause[A](body: Vector[A], head: A)

  enum Origin:
    case Initial
    case ByClause(index: Int)

  /** Records the first derivation of an atom. */
  final case class Step[A](atom: A, origin: Origin)

  /** Contains the reached goal, if any, and the derivations performed before stopping. */
  final case class Result[A](goal: Option[A], steps: Vector[Step[A]]):
    def reached: Boolean = goal.nonEmpty
    def derived: Vector[A] = steps.map(_.atom)

  /**
   * Derive a goal by forward chaining.
   *
   * Atoms with equal `cutKey` values are interchangeable. Runtime is linear in
   * the number of body occurrences, assuming constant-time key construction and
   * hashing.
   */
  def solve[A, Key](initialFacts: Iterable[A], clauses: IndexedSeq[Clause[A]], goals: Iterable[A])(cutKey: A => Key): Result[A] =
    val facts = initialFacts.iterator.toVector
    val targets = goals.iterator.toVector

    val ids = mutable.HashMap.empty[Key, Int]
    var nextId = 0
    def intern(atom: A): Int =
      ids.getOrElseUpdate(
        cutKey(atom), {
          val id = nextId
          nextId += 1
          id
        }
      )

    val compiled = clauses.map: clause =>
      val seen = mutable.HashSet.empty[Int]
      val body = clause.body.iterator.map(intern).filter(seen.add).toVector
      body -> intern(clause.head)

    val factIds = facts.map(atom => intern(atom) -> atom)
    val goalIds = targets.iterator.map(intern).toSet
    val watchers = Array.fill[List[Int]](nextId)(Nil)
    val remaining = Array.ofDim[Int](clauses.size)

    compiled.indices.foreach: clauseIndex =>
      val (body, _) = compiled(clauseIndex)
      remaining(clauseIndex) = body.size
      body.foreach(atomId => watchers(atomId) = clauseIndex :: watchers(atomId))

    val known = Array.fill(nextId)(false)
    val queue = mutable.ArrayDeque.empty[Int]
    val steps = mutable.ArrayBuffer.empty[Step[A]]
    var reached: Option[A] = None

    def derive(atomId: Int, atom: A, origin: Origin): Unit =
      if !known(atomId) then
        known(atomId) = true
        queue.append(atomId)
        steps += Step(atom, origin)
        if goalIds.contains(atomId) then reached = Some(atom)

    val factIterator = factIds.iterator
    while factIterator.hasNext && reached.isEmpty do
      val (atomId, atom) = factIterator.next()
      derive(atomId, atom, Origin.Initial)

    var clauseIndex = 0
    while clauseIndex < clauses.size && reached.isEmpty do
      if remaining(clauseIndex) == 0 then
        derive(compiled(clauseIndex)._2, clauses(clauseIndex).head, Origin.ByClause(clauseIndex))
      clauseIndex += 1

    while queue.nonEmpty && reached.isEmpty do
      val atomId = queue.removeHead()
      var dependentClauses = watchers(atomId)
      while dependentClauses.nonEmpty && reached.isEmpty do
        val dependent = dependentClauses.head
        remaining(dependent) -= 1
        if remaining(dependent) == 0 then
          derive(compiled(dependent)._2, clauses(dependent).head, Origin.ByClause(dependent))
        dependentClauses = dependentClauses.tail

    Result(reached, steps.toVector)
