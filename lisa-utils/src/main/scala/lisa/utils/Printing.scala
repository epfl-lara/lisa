package lisa.utils

object Printing:
  def printList[T](seq: Iterable[T], separator: String = "\n\t"): String =
    (seq lazyZip (0 until seq.size)).map((x, i) => s"$i: $x").mkString(separator)

