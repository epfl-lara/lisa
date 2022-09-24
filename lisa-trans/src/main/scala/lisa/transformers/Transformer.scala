package lisa.transformers

class Transformer {

    def dependency_finder[A](top_sort :  IndexedSeq[A], children: A => Seq[A], imports : A => Seq[Int]) : Map[A, Set[Int]] = {
        def is_leaf(node: A): Boolean = imports(node).isEmpty | imports(node).forall(_ < 0)

        val rev = top_sort.reverse
        def inner(v : A) : Seq[Int] = v match {
            case _ if is_leaf(v) =>  imports(v)
            case _ => children(v).flatMap(inner) ++ imports(v).filter(_ < 0)
        }
        
        rev.map(v => (v, inner(v).toSet)).toMap
    }    
    
    def dfs[A](root: A, children: A => Seq[A], imports : A => Seq[Int]) = {
        def is_leaf(node: A): Boolean = imports(node).isEmpty | imports(node).forall(_ < 0)
        var cache = scala.collection.mutable.Map[A, Set[Int]]().withDefault(_ => Set())
        var finished = scala.collection.mutable.Set[A]()

        def backpropagate(current: Seq[A]): Seq[A] = current match {
            case head::tail => {
                if(children(head).forall(finished contains _)) {
                    finished += head
                    backpropagate(tail)
                } else {
                    current
                }
            }
            case Nil => Nil
        }

        def loop(toVisit: Seq[A], visited: Seq[A], current: Seq[A]): Seq[A] = toVisit match {
            case Nil => visited
            case head::tail if (visited contains head) & is_leaf(head) => {
                finished += head
                current.foreach(st => cache(st) = cache(st) ++ imports(head))
                loop(tail, visited, backpropagate(current))
            }
            case head::tail if is_leaf(head) => {
                finished += head
                current.foreach(st => cache(st) = cache(st) ++ imports(head))
                loop(tail, head +: visited, backpropagate(current))
            }
            case head::tail if visited contains head => loop(tail, visited, current)
            case head::tail => loop(children(head) ++ tail, head +: visited, head +: current)
        }
        (loop(Seq(root), Seq.empty, Seq.empty), cache.toMap)
    }
}