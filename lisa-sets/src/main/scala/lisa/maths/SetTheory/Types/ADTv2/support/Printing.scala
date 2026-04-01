package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.SetTheory.{Expr, given}
import lisa.maths.SetTheory.Functions.Function.app
import lisa.utils.fol.FOL.App

object Printing {

  @volatile private var installed: Boolean = false

  private def unfoldSetApplicationChain(func: Expr[?], lastArg: Expr[?]): (Expr[?], List[Expr[?]]) =
    def rec(e: Expr[?], acc: List[Expr[?]]): (Expr[?], List[Expr[?]]) = e match
      case App(App(`app`, innerFunc), innerArg) => rec(innerFunc, innerArg :: acc)
      case App(innerFunc, innerArg) => rec(innerFunc, innerArg :: acc)
      case _ => (e, acc)
    rec(func, List(lastArg))

  private def adtv2AppPrinter(args: Seq[Expr[?]]): String =
    val func = args(0)
    val x = args(1)
    val (head, allArgs) = unfoldSetApplicationChain(func, x)
    head.mkString(allArgs)

  def install(): Unit =
    if !installed then
      app.printAs(args => adtv2AppPrinter(args))
      installed = true
}
