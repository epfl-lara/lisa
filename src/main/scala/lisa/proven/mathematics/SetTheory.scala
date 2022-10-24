package lisa.proven.mathematics

import lisa.automation.kernel.Destructors.*
import lisa.automation.kernel.ProofTactics.*

/**
 * An embryo of mathematical development, containing a few example theorems and the definition of the ordered unorderedPair.
 */
object SetTheory extends lisa.Main {

  THEOREM("russelParadox") of "∀'x. elem('x, 'y) ↔ ¬elem('x, 'x) ⊢" PROOF {
    val y = VariableLabel("y")
    val x = VariableLabel("x")

    have(in(y, y) <=> !in(y, y) |- ()) by Restate
    andThen(forall(x, in(x, y) <=> !in(x, x)) |- ()) by LeftForall(in(x, y) <=> !in(x, x), x, y)
  }
  show

  THEOREM("unorderedPair_symmetry") of
    "⊢ ∀'y. ∀'x. unordered_pair('x, 'y) = unordered_pair('y, 'x)" PROOF2 {
      val x = VariableLabel("x")
      val y = VariableLabel("y")
      val z = VariableLabel("z")
      val h = VariableFormulaLabel("h")
      val fin = SC.SCSubproof(
        {
          val pr0 = SC.SCSubproof(
            {
              val pairSame11 = instantiateForall(new SCProof(steps(), imports(ax"pairAxiom")), pairAxiom, x)
              val pairSame12 = instantiateForall(pairSame11, pairSame11.conclusion.right.head, y)
              instantiateForall(pairSame12, pairSame12.conclusion.right.head, z)
            },
            Seq(-1)
          )
          val pr1 = SC.SCSubproof(
            {
              val pairSame21 = instantiateForall(new SCProof(steps(), imports(ax"pairAxiom")), pairAxiom, y)
              val pairSame22 = instantiateForall(pairSame21, pairSame21.conclusion.right.head, x)
              instantiateForall(pairSame22, pairSame22.conclusion.right.head, z)
            },
            Seq(-1)
          )
          val pr2 = SC.RightSubstIff(
            Sequent(pr1.bot.right, Set(in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))),
            0,
            List(((x === z) \/ (y === z), in(z, unorderedPair(y, x)))),
            LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h)
          )
          val pr3 = SC.Cut(Sequent(pr1.bot.left, pr2.bot.right), 1, 2, pr2.bot.left.head)
          val pr4 = SC.RightForall(Sequent(Set(), Set(forall(z, pr2.bot.right.head))), 3, pr2.bot.right.head, z)
          SCProof(steps(pr0, pr1, pr2, pr3, pr4), imports(ax"pairAxiom"))
        },
        Seq(-2)
      )
      val pairExt = SC.SCSubproof(
        {
          val pairExt1 = instantiateForall(SCProof(steps(), imports(ax"extensionalityAxiom")), ax"extensionalityAxiom", unorderedPair(x, y))
          instantiateForall(pairExt1, pairExt1.conclusion.right.head, unorderedPair(y, x))
        },
        Seq(-1)
      )
      val fin2 = byEquiv(
        pairExt.bot.right.head,
        fin.bot.right.head
      )(pairExt, fin)
      val fin3 = generalizeToForall(fin2, fin2.conclusion.right.head, x)
      val fin4 = generalizeToForall(fin3, fin3.conclusion.right.head, y)
      fin4.copy(imports = imports(ax"extensionalityAxiom", ax"pairAxiom"))
    } using (ax"extensionalityAxiom", AxiomaticSetTheory.pairAxiom)
  show

  // This proof is old and very unoptimised
  THEOREM("unorderedPair_deconstruction") of
    "⊢ ∀'x. ∀'y. ∀ 'x1. ∀ 'y1. unordered_pair('x, 'y) = unordered_pair('x1, 'y1) ⇒ 'y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1" PROOF2 {
      val x = VariableLabel("x")
      val y = VariableLabel("y")
      val x1 = VariableLabel("x'")
      val y1 = VariableLabel("y'")
      val z = VariableLabel("z")
      val g = VariableLabel("g")
      val h = VariableFormulaLabel("h")
      val pxy = unorderedPair(x, y)
      val pxy1 = unorderedPair(x1, y1)
      val p0 = SC.SCSubproof(
        {
          val p0 = SC.SCSubproof(
            {
              val zf = in(z, pxy)
              val p1_0 = hypothesis(zf)
              val p1_1 = SC.RightImplies(emptySeq +> (zf ==> zf), 0, zf, zf)
              val p1_2 = SC.RightIff(emptySeq +> (zf <=> zf), 1, 1, zf, zf) //  |- (z in {x,y} <=> z in {x,y})
              val p1_3 = SC.RightSubstEq(emptySeq +< (pxy === pxy1) +> (zf <=> in(z, pxy1)), 2, List((pxy, pxy1)), LambdaTermFormula(Seq(g), zf <=> in(z, g)))
              SCProof(IndexedSeq(p1_0, p1_1, p1_2, p1_3), IndexedSeq(() |- pairAxiom))
            },
            Seq(-1)
          ) //  ({x,y}={x',y'}) |- ((z∈{x,y})↔(z∈{x',y'}))
          val p1 = SC.SCSubproof(
            {
              val p1_0 = SC.Rewrite(() |- pairAxiom, -1) //  |- ∀∀∀((z$1∈{x$3,y$2})↔((x$3=z$1)∨(y$2=z$1)))
              val p1_1 = instantiateForall(SCProof(IndexedSeq(p1_0), IndexedSeq(() |- pairAxiom)), x, y, z)
              p1_1
            },
            Seq(-1)
          ) //  |- (z in {x,y}) <=> (z=x \/ z=y)
          val p2 = SC.SCSubproof(
            {
              val p2_0 = SC.Rewrite(() |- pairAxiom, -1) //  |- ∀∀∀((z$1∈{x$3,y$2})↔((x$3=z$1)∨(y$2=z$1)))
              val p2_1 = instantiateForall(SCProof(IndexedSeq(p2_0), IndexedSeq(() |- pairAxiom)), x1, y1, z)
              p2_1
            },
            Seq(-1)
          ) //  |- (z in {x',y'}) <=> (z=x' \/ z=y')
          val p3 = SC.RightSubstEq(
            emptySeq +< (pxy === pxy1) +> (in(z, pxy1) <=> ((z === x) \/ (z === y))),
            1,
            List((pxy, pxy1)),
            LambdaTermFormula(Seq(g), in(z, g) <=> ((z === x) \/ (z === y)))
          ) //   ({x,y}={x',y'}) |- ((z∈{x',y'})↔((z=x)∨(z=y)))
          val p4 = SC.RightSubstIff(
            emptySeq +< p3.bot.left.head +< p2.bot.right.head +> (((z === x) \/ (z === y)) <=> ((z === x1) \/ (z === y1))),
            3,
            List(((z === x1) \/ (z === y1), in(z, pxy1))),
            LambdaFormulaFormula(Seq(h), h <=> ((z === x) \/ (z === y)))
          ) //  ((z∈{x',y'})↔((x'=z)∨(y'=z))), ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
          val p5 = SC.Cut(emptySeq ++< p3.bot ++> p4.bot, 2, 4, p2.bot.right.head)
          SCProof(IndexedSeq(p0, p1, p2, p3, p4, p5), IndexedSeq(() |- pairAxiom))
        },
        Seq(-1)
      ) //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))

      val p1 = SC.SCSubproof(
        SCProof(
          byCase(x === x1)(
            SC.SCSubproof(
              {
                val pcm1 = p0
                val pc0 = SC.SCSubproof(
                  SCProof(
                    byCase(y === x)(
                      SC.SCSubproof(
                        {
                          val pam1 = pcm1
                          val pa0 = SC.SCSubproof(
                            {
                              val f1 = z === x
                              val pa0_m1 = pcm1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                              val pa0_0 = SC.SCSubproof(
                                {
                                  val pa0_0_0 = hypothesis(f1)
                                  val pa0_1_1 = SC.RightOr(emptySeq +< f1 +> (f1 \/ f1), 0, f1, f1)
                                  val pa0_1_2 = SC.RightImplies(emptySeq +> (f1 ==> (f1 \/ f1)), 1, f1, f1 \/ f1)
                                  val pa0_1_3 = SC.LeftOr(emptySeq +< (f1 \/ f1) +> f1, Seq(0, 0), Seq(f1, f1))
                                  val pa0_1_4 = SC.RightImplies(emptySeq +> ((f1 \/ f1) ==> f1), 3, f1 \/ f1, f1)
                                  val pa0_1_5 = SC.RightIff(emptySeq +> ((f1 \/ f1) <=> f1), 2, 4, (f1 \/ f1), f1)
                                  val r = SCProof(pa0_0_0, pa0_1_1, pa0_1_2, pa0_1_3, pa0_1_4, pa0_1_5)
                                  r
                                }
                              ) //   |- (((z=x)∨(z=x))↔(z=x))
                              val pa0_1 = SC.RightSubstEq(
                                emptySeq +< (pxy === pxy1) +< (x === y) +> ((f1 \/ f1) <=> (z === x1) \/ (z === y1)),
                                -1,
                                List((x, y)),
                                LambdaTermFormula(Seq(g), (f1 \/ (z === g)) <=> ((z === x1) \/ (z === y1)))
                              ) //  ({x,y}={x',y'}) y=x|- (z=x)\/(z=x) <=> (z=x' \/ z=y')
                              val pa0_2 = SC.RightSubstIff(
                                emptySeq +< (pxy === pxy1) +< (x === y) +< (f1 <=> (f1 \/ f1)) +> (f1 <=> ((z === x1) \/ (z === y1))),
                                1,
                                List((f1, f1 \/ f1)),
                                LambdaFormulaFormula(Seq(h), h <=> ((z === x1) \/ (z === y1)))
                              )
                              val pa0_3 =
                                SC.Cut(emptySeq +< (pxy === pxy1) +< (x === y) +> (f1 <=> ((z === x1) \/ (z === y1))), 0, 2, f1 <=> (f1 \/ f1)) //  (x=y), ({x,y}={x',y'}) |- ((z=x)↔((z=x')∨(z=y')))
                              val pa0_4 = SC.RightForall(emptySeq +< (pxy === pxy1) +< (x === y) +> forall(z, f1 <=> ((z === x1) \/ (z === y1))), 3, f1 <=> ((z === x1) \/ (z === y1)), z)
                              val ra0_0 = instantiateForall(SCProof(IndexedSeq(pa0_0, pa0_1, pa0_2, pa0_3, pa0_4), IndexedSeq(pa0_m1.bot)), y1) //  (x=y), ({x,y}={x',y'}) |- ((y'=x)↔((y'=x')∨(y'=y')))
                              ra0_0
                            },
                            IndexedSeq(-1)
                          ) //  ({x,y}={x',y'}) y=x|- ((y'=x)↔((y'=x')∨(y'=y')))
                          val pa1 = SC.SCSubproof(
                            {
                              val pa1_0 = SC.RightRefl(emptySeq +> (y1 === y1), y1 === y1)
                              val pa1_1 = SC.RightOr(emptySeq +> ((y1 === y1) \/ (y1 === x1)), 0, y1 === y1, y1 === x1)
                              SCProof(pa1_0, pa1_1)
                            }
                          ) //  |- (y'=x' \/ y'=y')
                          val ra3 = byEquiv(pa0.bot.right.head, pa1.bot.right.head)(pa0, pa1) // ({x,y}={x',y'}) y=x|- ((y'=x)
                          val pal = SC.RightSubstEq(emptySeq ++< pa0.bot +> (y1 === y), ra3.length - 1, List((x, y)), LambdaTermFormula(Seq(g), y1 === g))
                          SCProof(ra3.steps, IndexedSeq(pam1.bot)).appended(pal) // (x=y), ({x,y}={x',y'}) |- (y'=y)
                        },
                        IndexedSeq(-1)
                      ) //  (x=y), ({x,y}={x',y'}) |- (y'=y)
                      ,
                      SC.SCSubproof(
                        {
                          val pbm1 = pcm1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                          val pb0_0 = SC.SCSubproof(
                            {
                              val pb0_0 = SC.RightForall(emptySeq ++< pcm1.bot +> forall(z, pcm1.bot.right.head), -1, pcm1.bot.right.head, z)
                              instantiateForall(SCProof(IndexedSeq(pb0_0), IndexedSeq(pcm1.bot)), y)
                            },
                            IndexedSeq(-1)
                          ) //  ({x,y}={x',y'}) |- (((y=x)∨(y=y))↔((y=x')∨(y=y')))
                          val pb0_1 = SC.SCSubproof(
                            {
                              val pa1_0 = SC.RightRefl(emptySeq +> (y === y), y === y)
                              val pa1_1 = SC.RightOr(emptySeq +> ((y === y) \/ (y === x)), 0, y === y, y === x)
                              SCProof(pa1_0, pa1_1)
                            }
                          ) //  |- (y=x)∨(y=y)
                          val rb0 = byEquiv(pb0_0.bot.right.head, pb0_1.bot.right.head)(pb0_0, pb0_1) //  ({x,y}={x',y'}) |- (y=x')∨(y=y')
                          val pb1 =
                            SC.RightSubstEq(emptySeq ++< rb0.conclusion +< (x === x1) +> ((y === x) \/ (y === y1)), rb0.length - 1, List((x, x1)), LambdaTermFormula(Seq(g), (y === g) \/ (y === y1)))
                          val rb1 = destructRightOr(
                            rb0.appended(pb1), //  ({x,y}={x',y'}) , x=x'|- (y=x)∨(y=y')
                            y === x,
                            y === y1
                          )
                          val rb2 = rb1.appended(SC.LeftNot(rb1.conclusion +< !(y === x) -> (y === x), rb1.length - 1, y === x)) //  (x=x'), ({x,y}={x',y'}), ¬(y=x) |- (y=y')
                          SCProof(rb2.steps, IndexedSeq(pbm1.bot))

                        },
                        IndexedSeq(-1)
                      ) //  ({x,y}={x',y'}), x=x', !y=x |- y=y'
                    ).steps,
                    IndexedSeq(pcm1.bot)
                  ),
                  IndexedSeq(-1)
                ) // (x=x'), ({x,y}={x',y'}) |- (y'=y)
                val pc1 = SC.RightRefl(emptySeq +> (x === x), x === x)
                val pc2 = SC.RightAnd(emptySeq ++< pc0.bot +> ((y1 === y) /\ (x === x)), Seq(0, 1), Seq(y1 === y, x === x)) // ({x,y}={x',y'}), x=x' |- (x=x /\ y=y')
                val pc3 =
                  SC.RightSubstEq(emptySeq ++< pc2.bot +> ((y1 === y) /\ (x1 === x)), 2, List((x, x1)), LambdaTermFormula(Seq(g), (y1 === y) /\ (g === x))) // ({x,y}={x',y'}), x=x' |- (x=x' /\ y=y')
                val pc4 = SC.RightOr(
                  emptySeq ++< pc3.bot +> (pc3.bot.right.head \/ ((x === y1) /\ (y === x1))),
                  3,
                  pc3.bot.right.head,
                  (x === y1) /\ (y === x1)
                ) //  ({x,y}={x',y'}), x=x' |- (x=x' /\ y=y')\/(x=y' /\ y=x')
                val r = SCProof(IndexedSeq(pc0, pc1, pc2, pc3, pc4), IndexedSeq(pcm1.bot))
                r
              },
              IndexedSeq(-1)
            ) //  ({x,y}={x',y'}), x=x' |- (x=x' /\ y=y')\/(x=y' /\ y=x')
            ,
            SC.SCSubproof(
              {
                val pdm1 = p0
                val pd0 = SC.SCSubproof(
                  {
                    val pd0_m1 = pdm1
                    val pd0_0 = SC.SCSubproof {
                      val ex1x1 = x1 === x1
                      val pd0_0_0 = SC.RightRefl(emptySeq +> ex1x1, ex1x1) //  |- x'=x'
                      val pd0_0_1 = SC.RightOr(emptySeq +> (ex1x1 \/ (x1 === y1)), 0, ex1x1, x1 === y1) //  |- (x'=x' \/ x'=y')
                      SCProof(IndexedSeq(pd0_0_0, pd0_0_1))
                    } //  |- (x'=x' \/ x'=y')
                    val pd0_1 = SC.SCSubproof(
                      {
                        val pd0_1_m1 = pd0_m1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                        val pd0_1_0 = SC.RightForall(emptySeq ++< pd0_1_m1.bot +> forall(z, pd0_1_m1.bot.right.head), -1, pd0_1_m1.bot.right.head, z)
                        val rd0_1_1 = instantiateForall(SCProof(IndexedSeq(pd0_1_0), IndexedSeq(pd0_m1.bot)), x1) //  ({x,y}={x',y'}) |- (x'=x \/ x'=y) <=> (x'=x' \/ x'=y')
                        rd0_1_1
                      },
                      IndexedSeq(-1)
                    ) //  ({x,y}={x',y'}) |- (x'=x \/ x'=y) <=> (x'=x' \/ x'=y')
                    val pd0_2 = SC.RightSubstIff(
                      pd0_1.bot.right |- ((x1 === x) \/ (x1 === y)),
                      0,
                      List(((x1 === x) \/ (x1 === y), (x1 === x1) \/ (x1 === y1))),
                      LambdaFormulaFormula(Seq(h), h)
                    ) // (x'=x \/ x'=y) <=> (x'=x' \/ x'=y') |- (x'=x \/ x'=y)
                    val pd0_3 = SC.Cut(pd0_1.bot.left |- pd0_2.bot.right, 1, 2, pd0_1.bot.right.head) //  ({x,y}={x',y'}) |- (x=x' \/ y=x')
                    destructRightOr(SCProof(IndexedSeq(pd0_0, pd0_1, pd0_2, pd0_3), IndexedSeq(pd0_m1.bot)), x === x1, y === x1) //  ({x,y}={x',y'}) |- x=x',  y=x'
                  },
                  IndexedSeq(-1)
                ) //  ({x,y}={x',y'}) |- x=x',  y=x' --
                val pd1 = SC.SCSubproof(
                  {
                    val pd1_m1 = pdm1
                    val pd1_0 = SC.SCSubproof {
                      val exx = x === x
                      val pd1_0_0 = SC.RightRefl(emptySeq +> exx, exx) //  |- x=x
                      val pd1_0_1 = SC.RightOr(emptySeq +> (exx \/ (x === y)), 0, exx, x === y) //  |- (x=x \/ x=y)
                      SCProof(IndexedSeq(pd1_0_0, pd1_0_1))
                    } //  |- (x=x \/ x=y)
                    val pd1_1 = SC.SCSubproof(
                      {
                        val pd1_1_m1 = pd1_m1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                        val pd1_1_0 = SC.RightForall(emptySeq ++< pd1_1_m1.bot +> forall(z, pd1_1_m1.bot.right.head), -1, pd1_1_m1.bot.right.head, z)
                        val rd1_1_1 = instantiateForall(SCProof(IndexedSeq(pd1_1_0), IndexedSeq(pd1_m1.bot)), x) //  ({x,y}={x',y'}) |- (x=x \/ x=y) <=> (x=x' \/ x=y')
                        rd1_1_1
                      },
                      IndexedSeq(-1)
                    ) //  //  ({x,y}={x',y'}) |- (x=x \/ x=y) <=> (x=x' \/ x=y')
                    val rd1_2 = byEquiv(pd1_1.bot.right.head, pd1_0.bot.right.head)(pd1_1, pd1_0)
                    val pd1_3 = SC.SCSubproof(SCProof(rd1_2.steps, IndexedSeq(pd1_m1.bot)), IndexedSeq(-1)) //  //  ({x,y}={x',y'}) |- x=x' \/ x=y'
                    destructRightOr(SCProof(IndexedSeq(pd1_0, pd1_1, pd1_3), IndexedSeq(pd1_m1.bot)), x === x1, x === y1) //  ({x,y}={x',y'}) |- x=x',  x=y'
                  },
                  IndexedSeq(-1)
                ) //  ({x,y}={x',y'}) |- x=x',  x=y' --
                val pd2 = SC.RightAnd(emptySeq ++< pd1.bot +> (x === x1) +> ((x === y1) /\ (y === x1)), Seq(0, 1), Seq(x === y1, y === x1)) //  ({x,y}={x',y'})  |- x=x', (x=y' /\ y=x') ---
                val pd3 = SC.LeftNot(emptySeq ++< pd2.bot +< !(x === x1) +> ((x === y1) /\ (y === x1)), 2, x === x1) //  ({x,y}={x',y'}), !x===x1 |- (x=y' /\ y=x')
                val pd4 = SC.RightOr(
                  emptySeq ++< pd3.bot +> (pd3.bot.right.head \/ ((x === x1) /\ (y === y1))),
                  3,
                  pd3.bot.right.head,
                  (x === x1) /\ (y === y1)
                ) //  ({x,y}={x',y'}), !x===x1 |- (x=x' /\ y=y')\/(x=y' /\ y=x')
                SCProof(IndexedSeq(pd0, pd1, pd2, pd3, pd4), IndexedSeq(pdm1.bot))
              },
              IndexedSeq(-1)
            ) //  ({x,y}={x',y'}), !x=x' |- (x=x' /\ y=y')\/(x=y' /\ y=x')
          ).steps,
          IndexedSeq(p0.bot)
        ),
        IndexedSeq(0)
      ) //  ({x,y}={x',y'}) |- (x=x' /\ y=y')\/(x=y' /\ y=x')

      val p2 = SC.RightImplies(emptySeq +> (p1.bot.left.head ==> p1.bot.right.head), 1, p1.bot.left.head, p1.bot.right.head) //   |- ({x,y}={x',y'}) ==> (x=x' /\ y=y')\/(x=y' /\ y=x')
      generalizeToForall(SCProof(IndexedSeq(p0, p1, p2), IndexedSeq(() |- pairAxiom)), x, y, x1, y1)
    } using ax"pairAxiom"
  thm"unorderedPair_deconstruction".show

  THEOREM("noUniversalSet") of "∀'x. elem('x, 'z) ⊢ " PROOF2 {
    val x = VariableLabel("x")
    val y = VariableLabel("y")
    val z = VariableLabel("z")
    val h = VariableFormulaLabel("h")
    val sPhi = SchematicPredicateLabel("P", 2)
    // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,y) /\ sPhi(x,z)))))
    val i1 = () |- comprehensionSchema
    val i2 = thm"russelParadox" // forall(x1, in(x1,y) <=> !in(x1, x1)) |- ()
    val p0 = SC.InstPredSchema(() |- forall(z, exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))), -1, Map(sPhi -> LambdaTermFormula(Seq(x, z), !in(x, x))))
    val s0 = SC.SCSubproof(instantiateForall(SCProof(IndexedSeq(p0), IndexedSeq(i1)), z), Seq(-1)) // exists(y1, forall(x1, in(x1,y1) <=> (in(x1,z1) /\ !in(x1, x1))))
    val s1 = hypothesis(in(x, y) <=> (in(x, z) /\ !in(x, x))) // in(x,y) <=> (in(x,z) /\ in(x, x)) |- in(x,y) <=> (in(x,z) /\ in(x, x))
    val s2 = SC.RightSubstIff(
      (in(x, z) <=> True, in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> (True /\ !in(x, x)),
      1,
      List((in(x, z), And())),
      LambdaFormulaFormula(Seq(h), in(x, y) <=> (h /\ !in(x, x)))
    ) // in(x1,y1) <=> (in(x1,z1) /\ in(x1, x1)) |- in(x,y) <=> (True /\ in(x1, x1))
    val s3 = SC.Rewrite((in(x, z), in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> !in(x, x), 2)
    val s4 = SC.LeftForall((forall(x, in(x, z)), in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> !in(x, x), 3, in(x, z), x, x)
    val s5 = SC.LeftForall((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- in(x, y) <=> !in(x, x), 4, in(x, y) <=> (in(x, z) /\ !in(x, x)), x, x)
    val s6 = SC.RightForall((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- forall(x, in(x, y) <=> !in(x, x)), 5, in(x, y) <=> !in(x, x), x)
    val s7 = SC.InstFunSchema(forall(x, in(x, y) <=> !in(x, x)) |- (), -2, Map(y -> LambdaTermTerm(Nil, y)))
    val s8 = SC.Cut((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- (), 6, 7, forall(x, in(x, y) <=> !in(x, x)))
    val s9 = SC.LeftExists((forall(x, in(x, z)), exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))) |- (), 8, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))), y)
    val s10 = SC.Cut(forall(x, in(x, z)) |- (), 0, 9, exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))))
    SCProof(steps(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10), imports(i1, i2))
  } using (ax"comprehensionSchema", thm"russelParadox")
  show

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  val oPair: ConstantFunctionLabel = DEFINE("", x, y) as unorderedPair(unorderedPair(x, y), unorderedPair(x, x))
  show

}
