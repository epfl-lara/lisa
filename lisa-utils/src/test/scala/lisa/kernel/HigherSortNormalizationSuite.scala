package lisa.kernel

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class HigherSortNormalizationSuite extends AnyFunSuite:
  test("normalize higher-sort lambda binders without treating them as free"):
    val sort = Arrow(Ind, Ind)
    val f = Variable(Identifier("higher-f"), sort)
    val g = Variable(Identifier("higher-g"), sort)
    val x = Variable(Identifier("higher-x"), Ind)
    assert(isSame(Lambda(f, f(x)), Lambda(g, g(x))))
    assert(!isSame(Lambda(f, f(x)), Lambda(g, f(x))))

  test("distinguish same-named free variables of another sort"):
    val id = Identifier("same-sort-name")
    val function = Variable(id, Arrow(Ind, Ind))
    val term = Variable(id, Ind)
    val fresh = Variable(Identifier("fresh-sort-name"), function.sort)
    assert(isSame(Lambda(function, function(term)), Lambda(fresh, fresh(term))))
    assert(!isSame(Lambda(function, function(term)), Lambda(fresh, function(term))))
