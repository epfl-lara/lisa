package lisa.front.printer

/**
 * Represents the result of printing expressed as a tree.
 * This allows to extract positional information.
 */
sealed abstract class FrontPrintNode {
  import FrontPrintNode.*

  def print: String = this match {
    case FrontLeaf(value) => value
    case FrontBranch(children) => children.map(_.print).mkString
  }
}

object FrontPrintNode {
  case class FrontLeaf(value: String) extends FrontPrintNode
  case class FrontBranch(children: IndexedSeq[FrontPrintNode]) extends FrontPrintNode {
    def locate(pos: Seq[Int]): (Int, Int) = {
      def locate(that: FrontBranch, pos: Seq[Int], start: Int): (Int, Int) = pos match {
        case h +: t =>
          val (child, index) = that.children.view.zipWithIndex.collect {
            case (branch: FrontBranch, i) => (branch, i)
          }.drop(h).head
          val newStart = start + that.children.take(index).map(_.print.length).sum
          locate(child, t, newStart)
        case _ =>
          val length = that.children.map(_.print.length).sum
          (start, length)
      }
      locate(this, pos, 0)
    }
  }

  object FrontBranch {
    def apply(children: FrontPrintNode*): FrontBranch = new FrontBranch(children.toIndexedSeq)
  }

  given Conversion[String, FrontLeaf] = FrontLeaf.apply
}
