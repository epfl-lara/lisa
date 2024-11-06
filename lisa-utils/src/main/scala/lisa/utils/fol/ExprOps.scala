package lisa.utils.fol

import lisa.fol.Syntax

/**
  * Functional Tree-like operations for expressions.
  */
trait ExprOps extends Syntax {
  extension[A] (e: Expr[A])
    /**
      * Apply a function to the expression tree. The function is applied to a
      * node before traversing its (now new) children.
      *
      * @param f the function to apply
      * @return the transformed expression
      */
    def preMap(f: Expr[?] => Expr[?]): Expr[?] = ???

    /**
      * Apply a function to the expression tree. The function is applied to a
      * node after traversing its children.
      *
      * @param f the function to apply
      * @return the transformed expression
      */
    def postMap(f: Expr[?] => Expr[?]): Expr[?] = ???

    /**
      * All subexpressions of this expression, including itself, in depth-first
      * order.
      */
    def subexpressions: Iterator[Expr[?]] = 
      e match
        case Variable(id) => Iterator(e)
        case Constant(id) => Iterator(e)
        case App(f, arg)  => Iterator(e) ++ f.subexpressions ++ arg.subexpressions
        case Abs(v, body) => Iterator(e) ++ body.subexpressions

    /**
      * Collect all sub-expressions which satisfy a given predicate
      *
      * @param p the predicate
      * @return the (depth-first) sequence of sub-expressions satisfying `p`
      */
    def filter(p: Expr[?] => Boolean): Seq[Expr[?]] = 
      e.subexpressions.filter(p).toVector

    /**
      * Collect all sub-expressions to which a given partial function applies,
      * after applying the function.
      *
      * @param f the partial function
      * @return the (depth-first) sequence of sub-expressions to which `f`
      * applies
      */
    def collect(f: PartialFunction[Expr[?], Expr[?]]): Seq[Expr[?]] = 
      e.subexpressions.collect(f).toVector
}
