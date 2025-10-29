package lisa.automation
import lisa.automation.Congruence
import lisa.automation.Congruence._
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class CongruenceTest extends AnyFunSuite with lisa.TestMain {

  // TODO: Port to new kernel

  /*

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
  val * = SchematicFunctionLabel("*", 2)
  val << = SchematicFunctionLabel("<<", 2)
  val / = SchematicFunctionLabel("/", 2)


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
    val egraph = new EGraphExpr()
    egraph.add(a)
    egraph.add(b)
    egraph.add(c)
    egraph.merge(a, b)
    assert(egraph.idEq(a, b))
    assert(!egraph.idEq(a, c))

  }

  test("8 terms no congruence egraph test") {
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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

    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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

  }


  test("3 formulas no congruence egraph test") {
    val egraph = new EGraphExpr()
    egraph.add(af)
    egraph.add(bf)
    egraph.add(cf)
    egraph.merge(af, bf)
    assert(egraph.idEq(af, bf))
    assert(!egraph.idEq(af, cf))

  }

  test("8 formulas no congruence egraph test") {
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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

    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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
    val egraph = new EGraphExpr()
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


  test("15 terms no congruence with redundant merges test with proofs") {
    val egraph = new EGraphExpr()
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
      egraph.proveInnerTerm(b, c, base |- ())
    }

    val test2 = Theorem(base |- (f === h)) {
      egraph.proveInnerTerm(f, h, base |- ())
    }

    val test3 = Theorem(base |- (i === o)) {
      egraph.proveInnerTerm(i, o, base |- ())
    }

    val test4 = Theorem(base |- (o === i)) {
      egraph.proveInnerTerm(o, i, base |- ())
    }

  }


  test("4 elements with congruence test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(F(a))
    egraph.add(F(b))
    egraph.merge(a, b)
    val test5 = Theorem(a===b |- F(a) === F(b)) {
      egraph.proveInnerTerm(F(a), F(b), (a === b) |- ())
    }
  }


  test("divide-mult-shift by 2 in terms egraph test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(one)
    egraph.add(two)
    egraph.add(a)
    val ax2    = egraph.add(`*`(a, two))
    val ax2_d2 = egraph.add(`/`(`*`(a, two), two))
    val `2d2`  = egraph.add(`/`(two, two))
    val ax_2d2 = egraph.add(`*`(a, `/`(two, two)))
    val ax1    = egraph.add(`*`(a, one))
    val as1    = egraph.add(`<<`(a, one))

    egraph.merge(ax2, as1)
    egraph.merge(ax2_d2, ax_2d2)
    egraph.merge(`2d2`, one)
    egraph.merge(ax1, a)

    val base = List[Formula](ax2 === as1, ax2_d2 === ax_2d2, `2d2` === one, ax1 === a)

    val one_2d2 = Theorem(base |- (one === `2d2`)) {
      egraph.proveInnerTerm(one, `2d2`, base  |- ())
    }

    val ax2_as1 = Theorem(base |- (ax2 === as1)) {
      egraph.proveInnerTerm(ax2, as1, base  |- ())
    }

    val ax2_d2_ax_2d2 = Theorem(base |- (ax2_d2 === ax_2d2)) {
      egraph.proveInnerTerm(ax2_d2, ax_2d2, base  |- ())
    }

    val ax_2d2_ax1 = Theorem(base |- (ax_2d2 === ax1)) {
      egraph.proveInnerTerm(ax_2d2, ax1, base  |- ())
    }

    val ax_2d2_a = Theorem(base |- (ax_2d2 === a)) {
      egraph.proveInnerTerm(ax_2d2, a, base  |- ())
    }

  }

  test("long chain of termscongruence eGraph with proofs") {
    val egraph = new EGraphExpr()
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


    val base = List(ffffffffx === x, fffffx === x)


    val test2 = Theorem(base |- fffx === x) {
      egraph.proveInnerTerm(fffx, x, base |- ())
    }
    val test3 = Theorem(base |- ffx === x) {
      egraph.proveInnerTerm(ffx, x, base |- ())
    }
    val test4 = Theorem(base |- fx === x) {
      egraph.proveInnerTerm(fx, x, base |- ())
    }

  }


  test("15 formulas no congruence proofs with redundant merges test with proofs") {
    val egraph = new EGraphExpr()
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

    val base = List(af <=> cf, ef <=> ff, if_ <=> kf, mf <=> nf, af <=> bf,
     of <=> mf, if_ <=> mf, gf <=> hf, lf <=> kf, bf <=> cf, ff <=> ef, of <=> if_, gf <=> ef, if_ <=> jf)

    val test1 = Theorem(base |- bf <=> cf) {
      egraph.proveInnerFormula(bf, cf, base |- ())
    }

    val test2 = Theorem(base |- ff <=> hf) {
      egraph.proveInnerFormula(ff, hf, base |- ())
    }

    val test3 = Theorem(base |- if_ <=> of) {
      egraph.proveInnerFormula(if_, of, base |- ())
    }

    val test4 = Theorem(base |- of <=> if_) {
      egraph.proveInnerFormula(of, if_, base |- ())
    }

  }

  test("4 formulas with congruence test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(Ff(af))
    egraph.add(Ff(bf))
    egraph.merge(af, bf)
    val test5 = Theorem(af <=> bf |- Ff(af) <=> Ff(bf)) {
      egraph.proveInnerFormula(Ff(af), Ff(bf), (af <=> bf) |- ())
    }
  }

  test("divide-mult-shift by 2 in formulas egraph test with proofs") {
    val egraph = new EGraphExpr()
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

    val base = List[Formula](ax2 <=> as1, ax2_d2 <=> ax_2d2, `2d2` <=> onef, ax1 <=> af)

    val one_2d2 = Theorem(base |- onef <=> `2d2`) {
      egraph.proveInnerFormula(onef, `2d2`, base  |- ())
    }

    val ax2_as1 = Theorem(base |- ax2 <=> as1) {
      egraph.proveInnerFormula(ax2, as1, base  |- ())
    }

    val ax2_d2_ax_2d2 = Theorem(base |- ax2_d2 <=> ax_2d2) {
      egraph.proveInnerFormula(ax2_d2, ax_2d2, base  |- ())
    }

    val ax_2d2_ax1 = Theorem(base |- ax_2d2 <=> ax1) {
      egraph.proveInnerFormula(ax_2d2, ax1, base  |- ())
    }

    val ax_2d2_a = Theorem(base |- ax_2d2 <=> af) {
      egraph.proveInnerFormula(ax_2d2, af, base  |- ())
    }

  }

  test("long chain of formulas congruence eGraph with proofs") {
    val egraph = new EGraphExpr()
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

    val base = List(ffffffffx <=> xf, fffffx <=> xf)

    val test2 = Theorem(base |- fffx <=> xf) {
      egraph.proveInnerFormula(fffx, xf, base |- ())
    }
    val test3 = Theorem(base |- ffx <=> xf) {
      egraph.proveInnerFormula(ffx, xf, base |- ())
    }
    val test4 = Theorem(base |- fx <=> xf) {
      egraph.proveInnerFormula(fx, xf, base |- ())
    }
  }


  test("2 terms 6 predicates with congruence egraph test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(Ff(Ff(Fp(a))))
    egraph.add(Ff(Ff(Fp(b))))
    egraph.merge(a, b)

    val test5 = Theorem((a === b) |- Fp(a) <=> Fp(b)) {
      egraph.proveInnerFormula(Fp(a), Fp(b), (a === b) |- ())
    }

    val test6 = Theorem((a === b) |- Ff(Fp(a)) <=> Ff(Fp(b))) {
      egraph.proveInnerFormula(Ff(Fp(a)), Ff(Fp(b)), (a === b) |- ())
    }

    val test7 = Theorem((a === b) |- Ff(Ff(Fp(a))) <=> Ff(Ff(Fp(b))) ) {
      egraph.proveInnerFormula(Ff(Ff(Fp(a))), Ff(Ff(Fp(b))), (a === b) |- ())
    }

  }

  test("6 terms 6 predicates with congruence egraph test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(Ff(Ff(Fp(F(F(a))))))
    egraph.add(Ff(Ff(Fp(F(F(b))))))
    egraph.merge(a, b)

    val test5 = Theorem((a === b) |- (F(a) === F(b))) {
      egraph.proveInnerTerm(F(a), F(b), (a === b) |- ())
    }

    val test6 = Theorem((a === b) |- Fp(F(F(a))) <=> Fp(F(F(b))) ) {
      egraph.proveInnerFormula(Fp(F(F(a))), Fp(F(F(b))), (a === b) |- ())
    }

    val test7 = Theorem((a === b) |- Ff(Ff(Fp(F(F(a))))) <=> Ff(Ff(Fp(F(F(b))))) ) {
      egraph.proveInnerFormula(Ff(Ff(Fp(F(F(a))))), Ff(Ff(Fp(F(F(b))))), (a === b) |- ())
    }

    egraph.merge(Fp(F(F(b))), Ff(Fp(F(F(a)))))

    val test8 = Theorem(((a === b), Fp(F(F(b))) <=> Ff(Fp(F(F(a)))) ) |- Ff(Ff(Fp(F(F(a))))) <=> Ff(Ff(Fp(F(F(b))))) ) {
      egraph.proveInnerFormula(Ff(Ff(Fp(F(F(a))))), Ff(Ff(Fp(F(F(b))))), (a === b, Fp(F(F(b))) <=> Ff(Fp(F(F(a)))) ) |- ())
    }

  }

  test("Full congruence tactic tests") {
    println("Full congruence tactic tests\n")

    val base1 = List(a === c, e === f, i === k, m === n, a === b, o === m, i === m, g === h, l === k, b === c, f === e, o === i, g === e, i === j)

    val test1 = Theorem(base1 |- (b === c)) {
      have(thesis) by Congruence
    }

    val test2 = Theorem(base1 |- (f === h)) {
      have(thesis) by Congruence
    }

    val test3 = Theorem(base1 |- (i === o)) {
      have(thesis) by Congruence
    }


    val ax2    = `*`(a, two)
    val ax2_d2 = `/`(`*`(a, two), two)
    val `2d2`  = `/`(two, two)
    val ax_2d2 = `*`(a, `/`(two, two))
    val ax1    = `*`(a, one)
    val as1    = `<<`(a, one)

    val base2 = List[Formula](ax2 === as1, ax2_d2 === ax_2d2, `2d2` === one, ax1 === a)


    val one_2d2 = Theorem(base2 |- (one === `2d2`)) {
      have(thesis) by Congruence
    }

    val ax2_as1 = Theorem(base2 |- (ax2 === as1)) {
      have(thesis) by Congruence
    }

    val ax2_d2_ax_2d2 = Theorem(base2 |- (ax2_d2 === ax_2d2)) {
      have(thesis) by Congruence
    }

    val ax_2d2_ax1 = Theorem(base2 |- (ax_2d2 === ax1)) {
      have(thesis) by Congruence
    }

    val ax_2d2_a = Theorem(base2 |- (ax_2d2 === a)) {
      have(thesis) by Congruence
    }

    val ax_2d2_a_2 = Theorem(base2 |- (Fp(ax_2d2) <=> Fp(a))) {
      have(thesis) by Congruence
    }

    val ax_2d2_a_1 = Theorem((Fp(a) :: base2) |- Fp(ax_2d2)) {
      have(thesis) by Congruence
    }

    val ax_2d2_a_3 = Theorem((base2 :+ Fp(ax_2d2) :+ !Fp(a)) |- () ) {
      have(thesis) by Congruence
    }

    val test5 = Theorem(a===b |- F(a) === F(b)) {
      have(thesis) by Congruence
    }

    val test6 = Theorem(a === b |- F(a) === F(b)) {
      have(thesis) by Congruence
    }

    val test7 = Theorem((Ff(Ff(Ff(Ff(Ff(Ff(Ff(xf))))))) <=> xf, Ff(Ff(Ff(Ff(Ff(xf))))) <=> xf) |- Ff(Ff(Ff(xf))) <=> xf) {
      have(thesis) by Congruence
    }

    val test8 = Theorem((Ff(Ff(Ff(Ff(Ff(Ff(Ff(xf))))))) <=> xf, Ff(Ff(Ff(Ff(Ff(xf))))) <=> xf) |- Ff(xf) <=> xf) {
      have(thesis) by Congruence
    }

    val test9 = Theorem((a === b) |- (Fp(F(F(a))), !Fp(F(F(b)))) ) {
      have(thesis) by Congruence
    }

    val test10 = Theorem((a === b) |- Fp(F(F(a))) <=> Fp(F(F(b))) ) {
      have(thesis) by Congruence
    }


    val test11 = Theorem((a === b) |- Ff(Ff(Fp(F(F(a))))) <=> Ff(Ff(Fp(F(F(b))))) ) {
      have(thesis) by Congruence
    }

    val test12 = Theorem(((a === b), Fp(F(F(b))) <=> Ff(Fp(F(F(a)))), Ff(Ff(Fp(F(F(a))))) ) |- Ff(Ff(Fp(F(F(b))))) ) {
      have(thesis) by Congruence
    }


  }

   */

}
