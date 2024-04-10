package lisa.automation
import lisa.fol.FOL.{*, given}
import lisa.automation.Congruence.*
import org.scalatest.funsuite.AnyFunSuite


class CongruenceTest extends AnyFunSuite with lisa.Main {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  val a = variable
  val b = variable
  val c = variable
  val d = variable
  val e = variable
  val f = variable
  val g = variable
  val h = variable
  val i = variable
  val j = variable
  val k = variable
  val l = variable
  val m = variable
  val n = variable
  val o = variable

  val x = variable

  val F = function[1]

  val one = variable
  val two = variable
  val * = ConstantFunctionLabel.infix("*", 2)
  val << = ConstantFunctionLabel.infix("<<", 2)
  val / = ConstantFunctionLabel.infix("/", 2)

  
  val af = formulaVariable
  val bf = formulaVariable
  val cf = formulaVariable
  val df = formulaVariable
  val ef = formulaVariable
  val ff = formulaVariable
  val gf = formulaVariable
  val hf = formulaVariable
  val if_ = formulaVariable
  val jf = formulaVariable
  val kf = formulaVariable
  val lf = formulaVariable
  val mf = formulaVariable
  val nf = formulaVariable
  val of = formulaVariable

  val xf = formulaVariable

  val Ff = SchematicConnectorLabel("Ff", 1)
  val Fp = SchematicPredicateLabel("Fp", 1)

  val onef = formulaVariable
  val twof = formulaVariable
  val `*f` = SchematicConnectorLabel("*f", 2)
  val `<<f` = SchematicConnectorLabel("<<f", 2)
  val `/f` = SchematicConnectorLabel("/f", 2)


  test("3 terms no congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(a)
    egraph.add(b)
    egraph.add(c)
    egraph.merge(a, b)
    assert(egraph.idEq(a, b))
    assert(!egraph.idEq(a, c))

  }

  test("8 terms no congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(a)
    egraph.add(b)
    egraph.add(c)
    egraph.add(d)
    egraph.add(e)
    egraph.add(f)
    egraph.add(g)
    egraph.add(h)
    egraph.merge(a, b)
    egraph.merge(c, d)
    egraph.merge(e, f)
    egraph.merge(g, h)
    egraph.merge(a, c)
    egraph.merge(f, h)
    egraph.merge(a, f)
    assert(egraph.idEq(a, h))

  }

  test("15 terms no congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(a)
    egraph.add(b)
    egraph.add(c)
    egraph.add(d)
    egraph.add(e)
    egraph.add(f)
    egraph.add(g)
    egraph.add(h)
    egraph.add(i)
    egraph.add(j)
    egraph.add(k)
    egraph.add(l)
    egraph.add(m)
    egraph.add(n)
    egraph.add(o)
    egraph.merge(a, c)
    egraph.merge(e, f)
    egraph.merge(i, k)
    egraph.merge(m, n)
    egraph.merge(a, b)
    egraph.merge(o, m)
    egraph.merge(i, m)
    egraph.merge(g, h)
    egraph.merge(l, k)
    egraph.merge(c, d)
    egraph.merge(a, e)
    egraph.merge(a, i)
    egraph.merge(g, e)
    egraph.merge(i, j)
    assert(egraph.idEq(a, o))

  }

  test("15 terms no congruence egraph test with redundant merges") {
    val egraph = new EGraphTerms()
    egraph.add(a)
    egraph.add(b)
    egraph.add(c)
    egraph.add(d)
    egraph.add(e)
    egraph.add(f)
    egraph.add(g)
    egraph.add(h)
    egraph.add(i)
    egraph.add(j)
    egraph.add(k)
    egraph.add(l)
    egraph.add(m)
    egraph.add(n)
    egraph.add(o)
    egraph.merge(a, c)
    egraph.merge(e, f)
    egraph.merge(i, k)
    egraph.merge(m, n)
    egraph.merge(a, b)
    egraph.merge(o, m)
    egraph.merge(i, m)
    egraph.merge(g, h)
    egraph.merge(l, k)
    egraph.merge(b, c)
    egraph.merge(f, e)
    egraph.merge(o, i)
    egraph.merge(g, e)
    egraph.merge(i, j)

    assert(egraph.idEq(b, c))
    assert(egraph.idEq(f, h))
    assert(egraph.idEq(i, o))
    assert(!egraph.idEq(a, d))
    assert(!egraph.idEq(b, g))
    assert(!egraph.idEq(f, i))
    assert(!egraph.idEq(n, c))
    assert(egraph.termUF.getClasses.size == 4)

  }

  test("4 terms withcongruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(F(a))
    egraph.add(F(b))
    egraph.merge(a, b)
    assert(egraph.idEq(a, b))
    assert(egraph.idEq(F(a), F(b)))
    assert(!egraph.idEq(a, F(a)))
    assert(!egraph.idEq(a, F(b)))
    assert(!egraph.idEq(b, F(a)))
    assert(!egraph.idEq(b, F(b)))

    assert(egraph.explain(F(a), F(b)) == Some(List(egraph.TermCongruence((F(a), F(b))))) )

  }



  test("divide-mult-shift in terms by 2 egraph test") {

    val egraph = new EGraphTerms()
    egraph.add(one)
    egraph.add(two)
    egraph.add(a)
    val ax2    = egraph.add(*(a, two))
    val ax2_d2 = egraph.add(/(*(a, two), two))
    val `2d2`  = egraph.add(/(two, two))
    val ax_2d2 = egraph.add(*(a, /(two, two)))
    val ax1    = egraph.add(*(a, one))
    val as1    = egraph.add(<<(a, one))

    egraph.merge(ax2, as1)
    egraph.merge(ax2_d2, ax_2d2)
    egraph.merge(`2d2`, one)
    egraph.merge(ax1, a)


    assert(egraph.idEq(one, `2d2`))
    assert(egraph.idEq(ax2, as1))
    assert(egraph.idEq(ax2_d2, ax_2d2))
    assert(egraph.idEq(ax_2d2, ax1))
    assert(egraph.idEq(ax_2d2, a))

    assert(!egraph.idEq(ax2, ax2_d2))
    assert(!egraph.idEq(ax2, `2d2`))
    assert(!egraph.idEq(ax2, ax_2d2))
    assert(!egraph.idEq(ax2, ax1))
    assert(!egraph.idEq(ax2, a))
    assert(!egraph.idEq(ax2_d2, `2d2`))

    assert(egraph.explain(one, `2d2`) == Some(List(egraph.TermExternal((one, `2d2`)))) )
    assert(egraph.explain(ax2, as1) == Some(List(egraph.TermExternal((ax2, as1)))) )
    assert(egraph.explain(ax2_d2, ax_2d2) == Some(List(egraph.TermExternal((ax2_d2, ax_2d2)))) )

    assert(egraph.explain(ax_2d2, ax1) == Some(List(egraph.TermCongruence((ax_2d2, ax1)))) )
    assert(egraph.explain(ax_2d2, a) == Some(List(egraph.TermCongruence((ax_2d2, ax1)), egraph.TermExternal((ax1, a))) ))


  }

  test("long chain of terms congruence eGraph") {
    val egraph = new EGraphTerms()
    egraph.add(x)
    val fx = egraph.add(F(x))
    val ffx = egraph.add(F(fx))
    val fffx = egraph.add(F(ffx))
    val ffffx = egraph.add(F(fffx))
    val fffffx = egraph.add(F(ffffx))
    val ffffffx = egraph.add(F(fffffx))
    val fffffffx = egraph.add(F(ffffffx))
    val ffffffffx = egraph.add(F(fffffffx))


    egraph.merge(ffffffffx, x)
    egraph.merge(fffffx, x)
    assert(egraph.idEq(fffx, x))
    assert(egraph.idEq(ffx, x))
    assert(egraph.idEq(fx, x))
    assert(egraph.idEq(x, fx))

    assert(egraph.explain(fx, x) == Some(List(egraph.TermCongruence(fx, fffx), egraph.TermCongruence(fffx, ffffffffx), egraph.TermExternal(ffffffffx, x))))

  }


  test("3 formulas no congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(af)
    egraph.add(bf)
    egraph.add(cf)
    egraph.merge(af, bf)
    assert(egraph.idEq(af, bf))
    assert(!egraph.idEq(af, cf))

  }

  test("8 formulas no congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(af)
    egraph.add(bf)
    egraph.add(cf)
    egraph.add(df)
    egraph.add(ef)
    egraph.add(ff)
    egraph.add(gf)
    egraph.add(hf)
    egraph.merge(af, bf)
    egraph.merge(cf, df)
    egraph.merge(ef, ff)
    egraph.merge(gf, hf)
    egraph.merge(af, cf)
    egraph.merge(ff, hf)
    egraph.merge(af, ff)
    assert(egraph.idEq(af, hf))

  }

  test("15 formulas no congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(af)
    egraph.add(bf)
    egraph.add(cf)
    egraph.add(df)
    egraph.add(ef)
    egraph.add(ff)
    egraph.add(gf)
    egraph.add(hf)
    egraph.add(if_)
    egraph.add(jf)
    egraph.add(kf)
    egraph.add(lf)
    egraph.add(mf)
    egraph.add(nf)
    egraph.add(of)
    egraph.merge(af, cf)
    egraph.merge(ef, ff)
    egraph.merge(if_, kf)
    egraph.merge(mf, nf)
    egraph.merge(af, bf)
    egraph.merge(of, mf)
    egraph.merge(if_, mf)
    egraph.merge(gf, hf)
    egraph.merge(lf, kf)
    egraph.merge(cf, df)
    egraph.merge(af, ef)
    egraph.merge(af, if_)
    egraph.merge(gf, ef)
    egraph.merge(if_, jf)
    assert(egraph.idEq(af, of))

  }

  test("15 formulas no congruence egraph test with redundant merges") {
    val egraph = new EGraphTerms()
    egraph.add(af)
    egraph.add(bf)
    egraph.add(cf)
    egraph.add(df)
    egraph.add(ef)
    egraph.add(ff)
    egraph.add(gf)
    egraph.add(hf)
    egraph.add(if_)
    egraph.add(jf)
    egraph.add(kf)
    egraph.add(lf)
    egraph.add(mf)
    egraph.add(nf)
    egraph.add(of)
    egraph.merge(af, cf)
    egraph.merge(ef, ff)
    egraph.merge(if_, kf)
    egraph.merge(mf, nf)
    egraph.merge(af, bf)
    egraph.merge(of, mf)
    egraph.merge(if_, mf)
    egraph.merge(gf, hf)
    egraph.merge(lf, kf)
    egraph.merge(bf, cf)
    egraph.merge(ff, ef)
    egraph.merge(of, if_)
    egraph.merge(gf, ef)
    egraph.merge(if_, jf)

    assert(egraph.idEq(bf, cf))
    assert(egraph.idEq(ff, hf))
    assert(egraph.idEq(if_, of))
    assert(!egraph.idEq(af, df))
    assert(!egraph.idEq(bf, gf))
    assert(!egraph.idEq(ff, if_))
    assert(!egraph.idEq(nf, cf))
    assert(egraph.formulaUF.getClasses.size == 4)

  }

  test("4 formulas withcongruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(Ff(af))
    egraph.add(Ff(bf))
    egraph.merge(af, bf)
    assert(egraph.idEq(af, bf))
    assert(egraph.idEq(Ff(af), Ff(bf)))
    assert(!egraph.idEq(af, Ff(af)))
    assert(!egraph.idEq(af, Ff(bf)))
    assert(!egraph.idEq(bf, Ff(af)))
    assert(!egraph.idEq(bf, Ff(bf)))

    assert(egraph.explain(Ff(af), Ff(bf)) == Some(List(egraph.FormulaCongruence((Ff(af), Ff(bf))))) )

  }

  test("divide-mult-shift in formulas by 2 egraph test") {

    val egraph = new EGraphTerms()
    egraph.add(onef)
    egraph.add(twof)
    egraph.add(af)
    val ax2    = egraph.add(`*f`(af, twof))
    val ax2_d2 = egraph.add(`/f`(`*f`(af, twof), twof))
    val `2d2`  = egraph.add(`/f`(twof, twof))
    val ax_2d2 = egraph.add(`*f`(af, `/f`(twof, twof)))
    val ax1    = egraph.add(`*f`(af, onef))
    val as1    = egraph.add(`<<f`(af, onef))

    egraph.merge(ax2, as1)
    egraph.merge(ax2_d2, ax_2d2)
    egraph.merge(`2d2`, onef)
    egraph.merge(ax1, af)


    assert(egraph.idEq(onef, `2d2`))
    assert(egraph.idEq(ax2, as1))
    assert(egraph.idEq(ax2_d2, ax_2d2))
    assert(egraph.idEq(ax_2d2, ax1))
    assert(egraph.idEq(ax_2d2, af))

    assert(!egraph.idEq(ax2, ax2_d2))
    assert(!egraph.idEq(ax2, `2d2`))
    assert(!egraph.idEq(ax2, ax_2d2))
    assert(!egraph.idEq(ax2, ax1))
    assert(!egraph.idEq(ax2, af))
    assert(!egraph.idEq(ax2_d2, `2d2`))

    assert(egraph.explain(onef, `2d2`) == Some(List(egraph.FormulaExternal((onef, `2d2`)))) )
    assert(egraph.explain(ax2, as1) == Some(List(egraph.FormulaExternal((ax2, as1)))) )
    assert(egraph.explain(ax2_d2, ax_2d2) == Some(List(egraph.FormulaExternal((ax2_d2, ax_2d2)))) )

    assert(egraph.explain(ax_2d2, ax1) == Some(List(egraph.FormulaCongruence((ax_2d2, ax1)))) )
    assert(egraph.explain(ax_2d2, af) == Some(List(egraph.FormulaCongruence((ax_2d2, ax1)), egraph.FormulaExternal((ax1, af))) ))

    


  }

  test("long chain of formulas congruence eGraph") {
    val egraph = new EGraphTerms()
    egraph.add(xf)
    val fx = egraph.add(Ff(xf))
    val ffx = egraph.add(Ff(fx))
    val fffx = egraph.add(Ff(ffx))
    val ffffx = egraph.add(Ff(fffx))
    val fffffx = egraph.add(Ff(ffffx))
    val ffffffx = egraph.add(Ff(fffffx))
    val fffffffx = egraph.add(Ff(ffffffx))
    val ffffffffx = egraph.add(Ff(fffffffx))


    egraph.merge(ffffffffx, xf)
    egraph.merge(fffffx, xf)
    assert(egraph.idEq(fffx, xf))
    assert(egraph.idEq(ffx, xf))
    assert(egraph.idEq(fx, xf))
    assert(egraph.idEq(xf, fx))
    assert(egraph.explain(fx, xf) == Some(List(egraph.FormulaCongruence(fx, ffffffffx), egraph.FormulaExternal(ffffffffx, xf))))

  }

  //////////////////////////////////////
  //// With both terms and formulas ////
  //////////////////////////////////////

  test("2 terms 6 predicates with congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(Ff(Ff(Fp(a))))
    egraph.add(Ff(Ff(Fp(b))))
    egraph.merge(a, b)
    assert(egraph.idEq(a, b))
    assert(egraph.idEq(Fp(a), Fp(b)))
    assert(egraph.idEq(Ff(Fp(a)), Ff(Fp(b))))
    assert(egraph.idEq(Ff(Ff(Fp(a))), Ff(Ff(Fp(b)))))
    assert(!egraph.idEq(Fp(a), Ff(Fp(a))))
    assert(!egraph.idEq(Fp(a), Ff(Fp(b))))
    assert(!egraph.idEq(Fp(b), Ff(Fp(a))))
    assert(!egraph.idEq(Fp(b), Ff(Ff(Fp(b)))))
    assert(!egraph.idEq(Ff(Fp(a)), Ff(Ff(Fp(b)))))
    assert(egraph.formulaUF.getClasses.size == 3)

    egraph.merge(Fp(a), Ff(Fp(a)))
    assert(egraph.idEq(Fp(a), Ff(Fp(b))))
    assert(egraph.idEq(Fp(b), Ff(Fp(a))))
    assert(egraph.idEq(Ff(Fp(a)), Ff(Ff(Fp(a)))))
    assert(egraph.idEq(Fp(b), Ff(Ff(Fp(a)))))
    assert(egraph.formulaUF.getClasses.size == 1)

  }

    test("6 terms 6 predicates with congruence egraph test") {
    val egraph = new EGraphTerms()
    egraph.add(Ff(Ff(Fp(F(F(a))))))
    egraph.add(Ff(Ff(Fp(F(F(b))))))
    egraph.merge(a, b)
    assert(egraph.idEq(a, b))
    assert(egraph.idEq(F(a), F(b)))
    assert(egraph.idEq(Fp(F(F(a))), Fp(F(F(b)))))
    assert(egraph.idEq(Ff(Ff(Fp(F(F(a))))), Ff(Ff(Fp(F(F(b)))))))
    assert(egraph.formulaUF.getClasses.size == 3)
    assert(egraph.termUF.getClasses.size == 3)

    egraph.merge(Fp(F(F(b))), Ff(Fp(F(F(a)))))
    assert(egraph.formulaUF.getClasses.size == 1)

  }


  test("15 terms no congruence proofs test with redundant merges") {
    import lib.*
    val egraph = new EGraphTerms()
    egraph.add(a)
    egraph.add(b)
    egraph.add(c)
    egraph.add(d)
    egraph.add(e)
    egraph.add(f)
    egraph.add(g)
    egraph.add(h)
    egraph.add(i)
    egraph.add(j)
    egraph.add(k)
    egraph.add(l)
    egraph.add(m)
    egraph.add(n)
    egraph.add(o)
    egraph.merge(a, c)
    egraph.merge(e, f)
    egraph.merge(i, k)
    egraph.merge(m, n)
    egraph.merge(a, b)
    egraph.merge(o, m)
    egraph.merge(i, m)
    egraph.merge(g, h)
    egraph.merge(l, k)
    egraph.merge(b, c)
    egraph.merge(f, e)
    egraph.merge(o, i)
    egraph.merge(g, e)
    egraph.merge(i, j)
    val base = List(a === c, e === f, i === k, m === n, a === b, o === m, i === m, g === h, l === k, b === c, f === e, o === i, g === e, i === j)

    val test1 = Theorem(base |- (b === c)) {
      egraph.proveInner(b, c, base |- ())
    }

    val test2 = Theorem(base |- (f === h)) {
      egraph.proveInner(f, h, base |- ())
    }

    val test3 = Theorem(base |- (i === o)) {
      egraph.proveInner(i, o, base |- ())
    }

    val test4 = Theorem(base |- (o === i)) {
      egraph.proveInner(o, i, base |- ())
    }

  }

/*
  test("4 elements with congruence proof test with explain") {
    import lib.*
    val egraph = new EGraphTerms()
    egraph.add(F(a))
    egraph.add(F(b))
    egraph.merge(a, b)
    val test5 = Theorem(a===b |- F(a) === F(b)) {
      egraph.proveInner(a, b, () |- ())
    }
  }
*/

  /*

  test("divide-mult-shift by 2 egraph test with explain") {

    val egraph = new EGraphTerms()
    val one = egraph.add(Term("one", List()))
    val two = egraph.add(Term("two", List()))
    val a = egraph.add(Term("a", List()))
    val ax2 = egraph.add(Term("*", List(a, two)))
    val ax2_d2 = egraph.add(Term("/", List(ax2, two)))
    val `2d2` = egraph.add(Term("/", List(two, two)))
    val ax_2d2 = egraph.add(Term("*", List(a, `2d2`)))
    val ax1 = egraph.add(Term("*", List(a, one)))

    val as1 = egraph.add(Term("<<", List(a, one)))
    val * : TermSymbol = FunctionSymbol("*", 2)

    egraph.merge(ax2, as1)
    egraph.merge(ax2_d2, ax_2d2)
    egraph.merge(`2d2`, one)
    egraph.merge(ax1, a)
    val ctx = List(ax2 === as1, ax2_d2 === ax_2d2, `2d2` === one, ax1 === a)

    assert(egraph.explain(one, `2d2`) == Some(List(egraph.External((one, `2d2`)))) )
    assert(egraph.explain(ax2, as1) == Some(List(egraph.External((ax2, as1)))) )
    assert(egraph.explain(ax2_d2, ax_2d2) == Some(List(egraph.External((ax2_d2, ax_2d2)))) )

    assert(egraph.explain(ax_2d2, ax1) == Some(List(egraph.Congruence((ax_2d2, ax1)))) )
    assert(egraph.explain(ax_2d2, a) == Some(List(egraph.Congruence((ax_2d2, ax1)), egraph.External((ax1, a))) ))

    println(s"\n Proving ${one} === ${`2d2`} \n")
    println(egraph.prove(one, `2d2`, SC.Sequent(ctx, List()), "s"))

    println(s"\n Proving ${ax2} === ${as1} \n")
    println(egraph.prove(ax2, as1, SC.Sequent(ctx, List()), "s"))

    println(s"\n Proving ${ax2_d2} === ${ax_2d2} \n")
    println(egraph.prove(ax2_d2, ax_2d2, SC.Sequent(ctx, List()), "s"))

    println(s"\n Proving ${ax_2d2} === ${ax1} \n")
    println(egraph.prove(ax_2d2, ax1, SC.Sequent(ctx, List()), "s"))

    println(s"\n Proving ${ax_2d2} === ${a} \n")
    println(egraph.prove(ax_2d2, a, SC.Sequent(ctx, List()), "s"))


  }


  test("long chain congruence eGraph with explain") {
    val egraph = new EGraphTerms()
    val x = egraph.add(Term("x", List()))
    val fx = egraph.add(Term(F, List(x)))
    val ffx = egraph.add(Term(F, List(fx)))
    val fffx = egraph.add(Term(F, List(ffx)))
    val ffffx = egraph.add(Term(F, List(fffx)))
    val fffffx = egraph.add(Term(F, List(ffffx)))
    val ffffffx = egraph.add(Term(F, List(fffffx)))
    val fffffffx = egraph.add(Term(F, List(ffffffx)))
    val ffffffffx = egraph.add(Term(F, List(fffffffx)))


    egraph.merge(ffffffffx, x)
    egraph.merge(fffffx, x)
    assert(egraph.idEq(fffx, x))
    assert(egraph.idEq(ffx, x))
    assert(egraph.idEq(fx, x))
    assert(egraph.idEq(x, fx))

    val ctx = List(ffffffffx === x, fffffx === x)
    def shorten(s:String): String = 
      s.replace("F(F(F(F(F(F(F(F(x))))))))", "F8x")
      .replace("F(F(F(F(F(F(F(x)))))))", "F7x")
      .replace("F(F(F(F(F(F(x))))))", "F6x")
      .replace("F(F(F(F(F(x)))))", "F5x")
      .replace("F(F(F(F(x)))", "F4x")
      .replace("F(F(F(x)))", "F3x")
      .replace("F(F(x))", "F2x")
      .replace("F(x)", "Fx")

    println(s"\n Proving ${fffx} === ${x} \n")
    println(shorten(egraph.prove(fffx, x, SC.Sequent(ctx, List()), "s").get.toString()))

    println(s"\n Proving ${ffx} === ${x} \n")
    println(shorten(egraph.prove(ffx, x, SC.Sequent(ctx, List()), "s").get.toString()))

    println(s"\n Proving ${fx} === ${x} \n")
    println(shorten(egraph.prove(fx, x, SC.Sequent(ctx, List()), "s").get.toString()))

  }

*/
}