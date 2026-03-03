package lisa.automation



import org.scalatest.funsuite.AnyFunSuite

class CongruenceTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  val a = variable[Ind]
  val b = variable[Ind]
  val c = variable[Ind]
  val d = variable[Ind]
  val e = variable[Ind]
  val f = variable[Ind]
  val g = variable[Ind]
  val h = variable[Ind]
  val i = variable[Ind]
  val j = variable[Ind]
  val k = variable[Ind]
  val l = variable[Ind]
  val m = variable[Ind]
  val n = variable[Ind]
  val o = variable[Ind]

  val x = variable[Ind]

  val F = variable[Ind >>: Ind]

  val one = variable[Ind]
  val two = variable[Ind]
  val * = variable[Ind >>: Ind >>: Ind]
  val << = variable[Ind >>: Ind >>: Ind]
  val / = variable[Ind >>: Ind >>: Ind]


  val af = variable[Prop]
  val bf = variable[Prop]
  val cf = variable[Prop]
  val df = variable[Prop]
  val ef = variable[Prop]
  val ff = variable[Prop]
  val gf = variable[Prop]
  val hf = variable[Prop]
  val if_ = variable[Prop]
  val jf = variable[Prop]
  val kf = variable[Prop]
  val lf = variable[Prop]
  val mf = variable[Prop]
  val nf = variable[Prop]
  val of = variable[Prop]

  val xf = variable[Prop]
  val Ff = variable[Prop >>: Prop]
  val Fp = variable[Ind >>: Prop]

  val y = variable[Ind]
  val z = variable[Ind]
  val p = variable[Ind >>: Prop]
  val q = variable[Ind >>: Prop]
  val r = variable[Ind >>: Prop]

  val onef = variable[Prop]
  val twof = variable[Prop]
  val `*f` = variable[Prop >>: Prop >>: Prop]
  val `<<f` = variable[Prop >>: Prop >>: Prop]
  val `/f` = variable[Prop >>: Prop >>: Prop]

  def checkExplanation(egraph: EGraphExpr, a: Expr[?], b: Expr[?]): Boolean = {
    val explanation = egraph.explain(a, b)

    // A CongruenceStep (l, r) is sound iff l and r are applications of the same
    // function symbol to the same number of arguments, and each argument pair is
    // either identical or has a recursively valid explanation.
    def checkCongruenceStep(l: Expr[?], r: Expr[?]): Boolean =
      (l, r) match {
        case (Multiapp(labelL, argsL), Multiapp(labelR, argsR)) =>
          labelL == labelR &&
          argsL.size == argsR.size &&
          argsL.zip(argsR).forall { case (al, ar) =>
            al == ar || checkExplanation(egraph, al, ar)
          }
      }

    explanation match {
      case None       => false   // a and b are in different equivalence classes
      case Some(Nil)  => a == b  // empty explanation is valid only for identical nodes
      case Some(steps) =>
        val pairs = steps.map(_.between)

        // 1. Chain check: the oriented steps form a path a → … → b
        val chainOk =
          pairs.head._1 == a &&
          pairs.last._2 == b &&
          pairs.zip(pairs.tail).forall { case ((_, r1), (l2, _)) => r1 == l2 }

        // 2. Soundness of every individual step
        val stepsOk = steps.forall {
          case egraph.ExternalStep((l, r))   => true
          case egraph.CongruenceStep((l, r)) => checkCongruenceStep(l, r)
        }

        chainOk && stepsOk
    }
  }

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
    assert(egraph.UF.getClasses.size == 4)

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

    assert(checkExplanation(egraph, F(a), F(b)))

  }



  test("divide-mult-shift in terms by 2 egraph test") {

    val egraph = new EGraphExpr()
    egraph.add(one)
    egraph.add(two)
    egraph.add(a)
    val ax2    = egraph.add(*(a)(two))
    val ax2_d2 = egraph.add(/(*(a)(two))(two))
    val `2d2`  = egraph.add(/(two)(two))
    val ax_2d2 = egraph.add(*(a)(/(two)(two)))
    val ax1    = egraph.add(*(a)(one))
    val as1    = egraph.add(<<(a)(one))

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

    assert(checkExplanation(egraph, one, `2d2`))
    assert(checkExplanation(egraph, ax2, as1))
    assert(checkExplanation(egraph, ax2_d2, ax_2d2))

    assert(checkExplanation(egraph, ax_2d2, ax1))
    assert(checkExplanation(egraph, ax_2d2, a))


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
    assert(egraph.UF.getClasses.size == 4)

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

    assert(checkExplanation(egraph, Ff(af), Ff(bf)))

  }

  test("divide-mult-shift in formulas by 2 egraph test") {

    val egraph = new EGraphExpr()
    egraph.add(onef)
    egraph.add(twof)
    egraph.add(af)
    val ax2    = egraph.add(`*f`(af)( twof))
    val ax2_d2 = egraph.add(`/f`(`*f`(af)(twof))( twof))
    val `2d2`  = egraph.add(`/f`(twof)(twof))
    val ax_2d2 = egraph.add(`*f`(af)(`/f`(twof)(twof)))
    val ax1    = egraph.add(`*f`(af)(onef))
    val as1    = egraph.add(`<<f`(af)(onef))

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

    assert(checkExplanation(egraph, onef, `2d2`))
    assert(checkExplanation(egraph, ax2, as1))
    assert(checkExplanation(egraph, ax2_d2, ax_2d2))

    assert(checkExplanation(egraph, ax_2d2, ax1))
    assert(checkExplanation(egraph, ax_2d2, af))




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
    assert(checkExplanation(egraph, fx, xf))

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
    assert(egraph.UF.getClasses.size == 4)

    egraph.merge(Fp(a), Ff(Fp(a)))
    assert(egraph.idEq(Fp(a), Ff(Fp(b))))
    assert(egraph.idEq(Fp(b), Ff(Fp(a))))
    assert(egraph.idEq(Ff(Fp(a)), Ff(Ff(Fp(a)))))
    assert(egraph.idEq(Fp(b), Ff(Ff(Fp(a)))))
    assert(egraph.UF.getClasses.size == 2)

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
    assert(egraph.UF.getClasses.size == 6)

    egraph.merge(Fp(F(F(b))), Ff(Fp(F(F(a)))))
    assert(egraph.UF.getClasses.size == 4)

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
    val ax2    = egraph.add(`*`(a)(two))
    val ax2_d2 = egraph.add(`/`(`*`(a)(two))(two))
    val `2d2`  = egraph.add(`/`(two)(two))
    val ax_2d2 = egraph.add(`*`(a)(`/`(two)(two)))
    val ax1    = egraph.add(`*`(a)(one))
    val as1    = egraph.add(`<<`(a)(one))

    egraph.merge(ax2, as1)
    egraph.merge(ax2_d2, ax_2d2)
    egraph.merge(`2d2`, one)
    egraph.merge(ax1, a)

    val base = List[Expr[Prop]](ax2 === as1, ax2_d2 === ax_2d2, `2d2` === one, ax1 === a)

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
      egraph.proveInnerTerm(bf, cf, base |- ())
    }

    val test2 = Theorem(base |- ff <=> hf) {
      egraph.proveInnerTerm(ff, hf, base |- ())
    }

    val test3 = Theorem(base |- if_ <=> of) {
      egraph.proveInnerTerm(if_, of, base |- ())
    }

    val test4 = Theorem(base |- of <=> if_) {
      egraph.proveInnerTerm(of, if_, base |- ())
    }

  }

  test("4 formulas with congruence test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(Ff(af))
    egraph.add(Ff(bf))
    egraph.merge(af, bf)
    val test5 = Theorem(af <=> bf |- Ff(af) <=> Ff(bf)) {
      egraph.proveInnerTerm(Ff(af), Ff(bf), (af <=> bf) |- ())
    }
  }

  test("divide-mult-shift by 2 in formulas egraph test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(onef)
    egraph.add(twof)
    egraph.add(af)
    val ax2    = egraph.add(`*f`(af)(twof))
    val ax2_d2 = egraph.add(`/f`(`*f`(af)(twof))(twof))
    val `2d2`  = egraph.add(`/f`(twof)(twof))
    val ax_2d2 = egraph.add(`*f`(af)(`/f`(twof)(twof)))
    val ax1    = egraph.add(`*f`(af)(onef))
    val as1    = egraph.add(`<<f`(af)(onef))

    egraph.merge(ax2, as1)
    egraph.merge(ax2_d2, ax_2d2)
    egraph.merge(`2d2`, onef)
    egraph.merge(ax1, af)

    val base = List[Expr[Prop]](ax2 <=> as1, ax2_d2 <=> ax_2d2, `2d2` <=> onef, ax1 <=> af)

    val one_2d2 = Theorem(base |- onef <=> `2d2`) {
      egraph.proveInnerTerm(onef, `2d2`, base  |- ())
    }

    val ax2_as1 = Theorem(base |- ax2 <=> as1) {
      egraph.proveInnerTerm(ax2, as1, base  |- ())
    }

    val ax2_d2_ax_2d2 = Theorem(base |- ax2_d2 <=> ax_2d2) {
      egraph.proveInnerTerm(ax2_d2, ax_2d2, base  |- ())
    }

    val ax_2d2_ax1 = Theorem(base |- ax_2d2 <=> ax1) {
      egraph.proveInnerTerm(ax_2d2, ax1, base  |- ())
    }

    val ax_2d2_a = Theorem(base |- ax_2d2 <=> af) {
      egraph.proveInnerTerm(ax_2d2, af, base  |- ())
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
      egraph.proveInnerTerm(fffx, xf, base |- ())
    }
    val test3 = Theorem(base |- ffx <=> xf) {
      egraph.proveInnerTerm(ffx, xf, base |- ())
    }
    val test4 = Theorem(base |- fx <=> xf) {
      egraph.proveInnerTerm(fx, xf, base |- ())
    }
  }


  test("2 terms 6 predicates with congruence egraph test with proofs") {
    val egraph = new EGraphExpr()
    egraph.add(Ff(Ff(Fp(a))))
    egraph.add(Ff(Ff(Fp(b))))
    egraph.merge(a, b)

    val test5 = Theorem((a === b) |- Fp(a) <=> Fp(b)) {
      egraph.proveInnerTerm(Fp(a), Fp(b), (a === b) |- ())
    }

    val test6 = Theorem((a === b) |- Ff(Fp(a)) <=> Ff(Fp(b))) {
      egraph.proveInnerTerm(Ff(Fp(a)), Ff(Fp(b)), (a === b) |- ())
    }

    val test7 = Theorem((a === b) |- Ff(Ff(Fp(a))) <=> Ff(Ff(Fp(b))) ) {
      egraph.proveInnerTerm(Ff(Ff(Fp(a))), Ff(Ff(Fp(b))), (a === b) |- ())
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
      egraph.proveInnerTerm(Fp(F(F(a))), Fp(F(F(b))), (a === b) |- ())
    }

    val test7 = Theorem((a === b) |- Ff(Ff(Fp(F(F(a))))) <=> Ff(Ff(Fp(F(F(b))))) ) {
      egraph.proveInnerTerm(Ff(Ff(Fp(F(F(a))))), Ff(Ff(Fp(F(F(b))))), (a === b) |- ())
    }

    egraph.merge(Fp(F(F(b))), Ff(Fp(F(F(a)))))

    val test8 = Theorem(((a === b), Fp(F(F(b))) <=> Ff(Fp(F(F(a)))) ) |- Ff(Ff(Fp(F(F(a))))) <=> Ff(Ff(Fp(F(F(b))))) ) {
      egraph.proveInnerTerm(Ff(Ff(Fp(F(F(a))))), Ff(Ff(Fp(F(F(b))))), (a === b, Fp(F(F(b))) <=> Ff(Fp(F(F(a)))) ) |- ())
    }

  }
  


  test("Fp(ax_2d2) idEq Fp(a) egraph test") {
    val egraph = new EGraphExpr()
    egraph.add(one)
    egraph.add(two)
    egraph.add(a)
    val ax2    = egraph.add(`*`(a)(two))
    val ax2_d2 = egraph.add(`/`(`*`(a)(two))(two))
    val `2d2`  = egraph.add(`/`(two)(two))
    val ax_2d2 = egraph.add(`*`(a)(`/`(two)(two)))
    val ax1    = egraph.add(`*`(a)(one))
    val as1    = egraph.add(`<<`(a)(one))
    egraph.add(Fp(ax_2d2))
    egraph.add(Fp(a))

    egraph.merge(ax2, as1)       // *(a)(two)       === <<(a)(one)
    egraph.merge(ax2_d2, ax_2d2) // /(*(a)(two))(two) === *(a)(/(two)(two))
    egraph.merge(`2d2`, one)     // /(two)(two)      === one
    egraph.merge(ax1, a)         // *(a)(one)        === a

    // /(two)(two) ≡ one  →  *(a)(/(two)(two)) ≡ *(a)(one) = ax1 ≡ a  (congruence then external)
    assert(egraph.idEq(ax_2d2, a))
    // Fp is a unary predicate, so congruence lifts ax_2d2 ≡ a to Fp(ax_2d2) ≡ Fp(a)
    assert(egraph.idEq(Fp(ax_2d2), Fp(a)))
    assert(checkExplanation(egraph, Fp(ax_2d2), Fp(a)))
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
    


    val ax2    = `*`(a)(two)
    val ax2_d2 = `/`(`*`(a)(two))(two)
    val `2d2`  = `/`(two)(two)
    val ax_2d2 = `*`(a)(`/`(two)(two))
    val ax1    = `*`(a)(one)
    val as1    = `<<`(a)(one)

    val base2 = List[Expr[Prop]](ax2 === as1, ax2_d2 === ax_2d2, `2d2` === one, ax1 === a)

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


  test("Congruence.from with previous step") {
    val t1 = Theorem((p(y), x === y) |- p(x)) {
      have(p(x) |- p(x)) by Restate
      thenHave((p(y), x === y) |- p(x)) by Congruence
    }
    val t2 = Theorem((p(F(y)), x === y) |- p(F(x))) {
      have(p(F(x)) |- p(F(x))) by Restate
      thenHave((p(F(y)), x === y) |- p(F(x))) by Congruence
    }
    val t3 = Theorem((p(y), F(x) === y) |- p(F(x))) {
      have(p(F(x)) |- p(F(x))) by Restate
      thenHave((p(y), F(x) === y) |- p(F(x))) by Congruence
    }
    val t4 = Theorem((p(F(F(y))), x === y) |- p(F(F(x)))) {
      have(p(F(F(x))) |- p(F(F(x)))) by Restate
      thenHave((p(F(F(y))), x === y) |- p(F(F(x)))) by Congruence
    }
    val t5 = Theorem((p(y), q(y), x === y) |- r(x)) {
      have((p(x), q(x)) |- r(x)) subproof { sorry }
      thenHave((p(y), q(y), x === y) |- r(x)) by Congruence
    }
    val t6 = Theorem((p(a), q(b), x === a, y === b) |- r(x)) {
      have((p(x), q(y)) |- r(x)) subproof { sorry }
      thenHave((p(a), q(b), x === a, y === b) |- r(x)) by Congruence
    }
    val t7 = Theorem((p(x), q(b), y === b) |- r(x)) {
      have((p(x), q(y)) |- r(x)) subproof { sorry }
      thenHave((p(x), q(b), y === b) |- r(x)) by Congruence
    }
    val t8 = Theorem((p(y) /\ (x === y)) |- p(x)) {
      have(p(x) |- p(x)) by Restate
      thenHave((p(y), x === y) |- p(x)) by Congruence
      thenHave((p(y) /\ (x === y)) |- p(x)) by Restate
    }
    val t9 = Theorem((p(a), q(b), x === a, y === b) |- r(x)) {
      val fact1 = have(p(x) |- r(x)) subproof { sorry }
      val fact2 = have(q(y) |- r(x)) subproof { sorry }
      have((p(a), q(b), x === a, y === b) |- r(x)) by Congruence.from(fact1, fact2)
    }
    val t10 = Theorem((p(a), x === a) |- q(a)) {
      val fact1 = have(p(x) |- x === y) subproof { sorry }
      val fact2 = have(p(y) |- q(y)) subproof { sorry }
      have((p(a), x === a) |- q(a)) by Congruence.from(fact1, fact2)
    }
  }

}
