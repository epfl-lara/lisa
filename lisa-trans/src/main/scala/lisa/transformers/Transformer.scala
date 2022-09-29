package lisa.transformers

class Transformer {

    def dependency_finder[A](top_sort :  IndexedSeq[A], children: A => Seq[A], imports : A => Seq[Int]) : Map[A, Set[Int]] = {
        def is_leaf(node: A): Boolean = imports(node).isEmpty | imports(node).forall(_ < 0)
        var cache = scala.collection.mutable.Map[A, Set[Int]]().withDefault(_ => Set())

        val rev = top_sort.reverse
        def inner(v : A) : Seq[Int] = v match {
            case _ if is_leaf(v) =>  imports(v)
            case _ => {
                val res = children(v).flatMap(inner) ++ imports(v).filter(_ < 0)
                cache(v) = res.toSet
                res
                }
        }
        
        inner(rev.head)
        cache.toMap
    }    
}