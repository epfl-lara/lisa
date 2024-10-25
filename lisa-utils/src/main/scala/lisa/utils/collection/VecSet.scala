package lisa.utils.collection

import scala.collection.mutable
import scala.collection.IterableFactory
import scala.collection.IterableFactoryDefaults
import scala.collection.immutable.HashSet
import scala.collection.immutable.SetOps

object VecSet extends IterableFactory[VecSet]:
  def empty[A]: VecSet[A] = 
    new VecSet(Vector.empty, Set.empty)
  def from[A](source: IterableOnce[A]): VecSet[A] =
    val vec = Vector.from(source) 
    new VecSet(vec, vec.to(Set))
  def newBuilder[A]: mutable.ReusableBuilder[A, VecSet[A]] = new VecSetBuilder()

  private sealed class VecSetBuilder[A] () extends mutable.ReusableBuilder[A, VecSet[A]]:
    protected val vecBuilder: mutable.ReusableBuilder[A, Vector[A]] = Vector.newBuilder[A]
    protected val setBuilder: mutable.ReusableBuilder[A, Set[A]] = HashSet.newBuilder[A]
    protected var currentSize = 0

    def addOne(elem: A): this.type =
      vecBuilder.addOne(elem)
      setBuilder.addOne(elem)
      currentSize += 1
      this

    override def clear(): Unit = 
      vecBuilder.clear()
      setBuilder.clear()
      currentSize = 0

    override def result(): VecSet[A] = 
      new VecSet(vecBuilder.result(), setBuilder.result())

sealed class VecSet[A] private (protected val evec: Vector[A], protected val eset: Set[A]) 
  extends Set[A]
    with SetOps[A, VecSet, VecSet[A]]
    with IterableFactoryDefaults[A, VecSet]:
    // invariants:
    // require( evec.toSet == eset )
    // require( evec.distinct == evec )

    def iterator: Iterator[A] = evec.iterator

    def length: Int = evec.length

    override def iterableFactory: IterableFactory[VecSet] = VecSet

    override def contains(elem: A): Boolean = eset.contains(elem)

    override def excl(elem: A): VecSet[A] = 
      eset(elem) match
        case false => this
        case true => 
          // specialized version of Vector.diff 
          // without the added dramatic flair
          val builder = Vector.newBuilder[A]
          val iter = evec.iterator

          while (iter.hasNext) do 
            val next = iter.next
            if next == elem then 
              // found the element to remove, rush through the remaining
              builder.addAll(iter)
            else builder.addOne(next)

          new VecSet(builder.result(), eset.excl(elem))

    override def incl(elem: A): VecSet[A] = 
      eset(elem) match
        case false => new VecSet(evec :+ elem, eset + elem)
        case true => this
