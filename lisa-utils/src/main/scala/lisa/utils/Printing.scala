package lisa.utils

object Printing:
  def printList[T](seq: Iterable[T], prefix: String = "\n\t"): String =
    prefix + (seq lazyZip (0 until seq.size)).map((x, i) => s"$i: $x").mkString(prefix)

