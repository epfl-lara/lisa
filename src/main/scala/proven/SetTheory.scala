package proven

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory
import lisa.settheory.AxiomaticSetTheory.*
import utilities.Helpers.{*, given}
import proven.tactics.Destructors.*
import proven.tactics.ProofTactics.*

object SetTheory extends MainLibrary {

  THEOREM("russelParadox") of "∀x. (x ∈ ?y) ↔ ¬(x ∈ x) ⊢" PROOF {
    val y = SchematicFunctionLabel("y", 0)
    val x_ = VariableLabel("x")
    val contra = in(y, y) <=> !in(y, y)
    val s0 = Hypothesis(contra |- contra, contra)
    val s1 = LeftForall(forall(x_, in(x_, y) <=> !in(x_, x_)) |- contra, 0, in(x_, y) <=> !in(x_, x_), x_, y)
    val s2 = Rewrite(forall(x_, in(x_, y) <=> !in(x_, x_)) |- (), 1)
    Proof(s0, s1, s2)
  } using ()
  thm"russelParadox".show

  THEOREM("unorderedPair_symmetry") of
    "⊢ ∀y, x. {x, y} = {y, x}" PROOF {
    val x = VariableLabel("x")
    val y = VariableLabel("y")
    val z = VariableLabel("z")
    val h = SchematicPredicateLabel("h", 0)
    val fin = SCSubproof({
      val pr0 = SCSubproof({
        val pairSame11 = instantiateForall(new Proof(steps(), imports(ax"pairAxiom")), pairAxiom, x)
        val pairSame12 = instantiateForall(pairSame11, pairSame11.conclusion.right.head, y)
        instantiateForall(pairSame12, pairSame12.conclusion.right.head, z)
      }, Seq(-1))
      val pr1 = SCSubproof({
        val pairSame21 = instantiateForall(new Proof(steps(), imports(ax"pairAxiom")), pairAxiom, y)
        val pairSame22 = instantiateForall(pairSame21, pairSame21.conclusion.right.head, x)
        instantiateForall(pairSame22, pairSame22.conclusion.right.head, z)
      }, Seq(-1))
      val pr2 = RightSubstIff(
        Sequent(pr1.bot.right, Set(in(z, pair(x, y)) <=> in(z, pair(y, x)))),
        0,
        List(((x === z) \/ (y === z), in(z, pair(y, x)))),
        LambdaFormulaFormula(Seq(h), in(z, pair(x, y)) <=> h())
      )
      val pr3 = Cut(Sequent(pr1.bot.left, pr2.bot.right), 1, 2, pr2.bot.left.head)
      val pr4 = RightForall(Sequent(Set(), Set(forall(z, pr2.bot.right.head))), 3, pr2.bot.right.head, z)
      Proof(steps(pr0, pr1, pr2, pr3, pr4), imports(ax"pairAxiom"))
    }, Seq(-2))
    val pairExt = SCSubproof({
      val pairExt1 = instantiateForall(Proof(steps(), imports(ax"extensionalityAxiom")), ax"extensionalityAxiom", pair(x, y))
      instantiateForall(pairExt1, pairExt1.conclusion.right.head, pair(y, x))
    }, Seq(-1))
    val fin2 = byEquiv(
      pairExt.bot.right.head,
      fin.bot.right.head
    )(pairExt, fin)
    val fin3 = generalizeToForall(fin2, fin2.conclusion.right.head, x)
    val fin4 = generalizeToForall(fin3, fin3.conclusion.right.head, y)
    fin4.copy(imports = imports(ax"extensionalityAxiom", ax"pairAxiom"))
  } using (ax"extensionalityAxiom", AxiomaticSetTheory.pairAxiom)
  show

  //This proof is old and very unoptimised
  THEOREM("unorderedPair_deconstruction") of
    "⊢ ∀x, y, x', y'. ({x, y} = {x', y'}) ⇒ (y' = y) ∧ (x' = x) ∨ (x = y') ∧ (y = x')" PROOF {
    val x = VariableLabel("x")
    val y = VariableLabel("y")
    val x1 = VariableLabel("x'")
    val y1 = VariableLabel("y'")
    val z = VariableLabel("z")
    val g = SchematicFunctionLabel("g", 0)
    val h = SchematicPredicateLabel("h", 0)
    val pxy = pair(x, y)
    val pxy1 = pair(x1, y1)
    val p0 = SCSubproof(
      {
        val p0 = SCSubproof(
          {
            val zf = in(z, pxy)
            val p1_0 = hypothesis(zf)
            val p1_1 = RightImplies(emptySeq +> (zf ==> zf), 0, zf, zf)
            val p1_2 = RightIff(emptySeq +> (zf <=> zf), 1, 1, zf, zf) //  |- (z in {x,y} <=> z in {x,y})
            val p1_3 = RightSubstEq(emptySeq +< (pxy === pxy1) +> (zf <=> in(z, pxy1)), 2, List((pxy, pxy1)), LambdaTermFormula(Seq(g), zf <=> in(z, g())))
            Proof(IndexedSeq(p1_0, p1_1, p1_2, p1_3), IndexedSeq(() |- pairAxiom))
          },
          Seq(-1),
          display = true
        ) //  ({x,y}={x',y'}) |- ((z∈{x,y})↔(z∈{x',y'}))
        val p1 = SCSubproof(
          {
            val p1_0 = Rewrite(() |- pairAxiom, -1) //  |- ∀∀∀((z$1∈{x$3,y$2})↔((x$3=z$1)∨(y$2=z$1)))
            val p1_1 = instantiateForall(Proof(IndexedSeq(p1_0), IndexedSeq(() |- pairAxiom)), x, y, z)
            p1_1
          },
          Seq(-1),
          display = true
        ) //  |- (z in {x,y}) <=> (z=x \/ z=y)
        val p2 = SCSubproof(
          {
            val p2_0 = Rewrite(() |- pairAxiom, -1) //  |- ∀∀∀((z$1∈{x$3,y$2})↔((x$3=z$1)∨(y$2=z$1)))
            val p2_1 = instantiateForall(Proof(IndexedSeq(p2_0), IndexedSeq(() |- pairAxiom)), x1, y1, z)
            p2_1
          },
          Seq(-1),
        ) //  |- (z in {x',y'}) <=> (z=x' \/ z=y')
        val p3 = RightSubstEq(
          emptySeq +< (pxy === pxy1) +> (in(z, pxy1) <=> ((z === x) \/ (z === y))),
          1,
          List((pxy, pxy1)),
          LambdaTermFormula(Seq(g), in(z, g()) <=> ((z === x) \/ (z === y)))
        ) //   ({x,y}={x',y'}) |- ((z∈{x',y'})↔((z=x)∨(z=y)))
        val p4 = RightSubstIff(
          emptySeq +< p3.bot.left.head +< p2.bot.right.head +> (((z === x) \/ (z === y)) <=> ((z === x1) \/ (z === y1))),
          3,
          List(((z === x1) \/ (z === y1), in(z, pxy1))),
          LambdaFormulaFormula(Seq(h), h() <=> ((z === x) \/ (z === y)))
        ) //  ((z∈{x',y'})↔((x'=z)∨(y'=z))), ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
        val p5 = Cut(emptySeq ++< p3.bot ++> p4.bot, 2, 4, p2.bot.right.head)
        Proof(IndexedSeq(p0, p1, p2, p3, p4, p5), IndexedSeq(() |- pairAxiom))
      },
      Seq(-1)
    ) //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))

    val p1 = SCSubproof(
      Proof(
        byCase(x === x1)(
          SCSubproof(
            {
              val pcm1 = p0
              val pc0 = SCSubproof(
                Proof(
                  byCase(y === x)(
                    SCSubproof(
                      {
                        val pam1 = pcm1
                        val pa0 = SCSubproof(
                          {
                            val f1 = z === x
                            val pa0_m1 = pcm1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                            val pa0_0 = SCSubproof(
                              {
                                val pa0_0_0 = hypothesis(f1)
                                val pa0_1_1 = RightOr(emptySeq +< f1 +> (f1 \/ f1), 0, f1, f1)
                                val pa0_1_2 = RightImplies(emptySeq +> (f1 ==> (f1 \/ f1)), 1, f1, f1 \/ f1)
                                val pa0_1_3 = LeftOr(emptySeq +< (f1 \/ f1) +> f1, Seq(0, 0), Seq(f1, f1))
                                val pa0_1_4 = RightImplies(emptySeq +> ((f1 \/ f1) ==> f1), 3, f1 \/ f1, f1)
                                val pa0_1_5 = RightIff(emptySeq +> ((f1 \/ f1) <=> f1), 2, 4, (f1 \/ f1), f1)
                                val r = Proof(pa0_0_0, pa0_1_1, pa0_1_2, pa0_1_3, pa0_1_4, pa0_1_5)
                                r
                              },
                              display = false
                            ) //   |- (((z=x)∨(z=x))↔(z=x))
                            val pa0_1 = RightSubstEq(
                              emptySeq +< (pxy === pxy1) +< (x === y) +> ((f1 \/ f1) <=> (z === x1) \/ (z === y1)),
                              -1,
                              List((x, y)),
                              LambdaTermFormula(Seq(g), (f1 \/ (z === g())) <=> ((z === x1) \/ (z === y1)))
                            ) //  ({x,y}={x',y'}) y=x|- (z=x)\/(z=x) <=> (z=x' \/ z=y')
                            val pa0_2 = RightSubstIff(
                              emptySeq +< (pxy === pxy1) +< (x === y) +< (f1 <=> (f1 \/ f1)) +> (f1 <=> ((z === x1) \/ (z === y1))),
                              1,
                              List((f1, f1 \/ f1)),
                              LambdaFormulaFormula(Seq(h), h() <=> ((z === x1) \/ (z === y1)))
                            )
                            val pa0_3 =
                              Cut(emptySeq +< (pxy === pxy1) +< (x === y) +> (f1 <=> ((z === x1) \/ (z === y1))), 0, 2, f1 <=> (f1 \/ f1)) //  (x=y), ({x,y}={x',y'}) |- ((z=x)↔((z=x')∨(z=y')))
                            val pa0_4 = RightForall(emptySeq +< (pxy === pxy1) +< (x === y) +> forall(z, f1 <=> ((z === x1) \/ (z === y1))), 3, f1 <=> ((z === x1) \/ (z === y1)), z)
                            val ra0_0 = instantiateForall(Proof(IndexedSeq(pa0_0, pa0_1, pa0_2, pa0_3, pa0_4), IndexedSeq(pa0_m1.bot)), y1) //  (x=y), ({x,y}={x',y'}) |- ((y'=x)↔((y'=x')∨(y'=y')))
                            ra0_0
                          },
                          IndexedSeq(-1)
                        ) //  ({x,y}={x',y'}) y=x|- ((y'=x)↔((y'=x')∨(y'=y')))
                        val pa1 = SCSubproof(
                          {
                            val pa1_0 = RightRefl(emptySeq +> (y1 === y1), y1 === y1)
                            val pa1_1 = RightOr(emptySeq +> ((y1 === y1) \/ (y1 === x1)), 0, y1 === y1, y1 === x1)
                            Proof(pa1_0, pa1_1)
                          },
                          display = false
                        ) //  |- (y'=x' \/ y'=y')
                        val ra3 = byEquiv(pa0.bot.right.head, pa1.bot.right.head)(pa0, pa1) // ({x,y}={x',y'}) y=x|- ((y'=x)
                        val pal = RightSubstEq(emptySeq ++< pa0.bot +> (y1 === y), ra3.length - 1, List((x, y)), LambdaTermFormula(Seq(g), y1 === g()))
                        Proof(ra3.steps, IndexedSeq(pam1.bot)).appended(pal) // (x=y), ({x,y}={x',y'}) |- (y'=y)
                      },
                      IndexedSeq(-1)
                    ) //  (x=y), ({x,y}={x',y'}) |- (y'=y)
                    ,
                    SCSubproof(
                      {
                        val pbm1 = pcm1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                        val pb0_0 = SCSubproof(
                          {
                            val pb0_0 = RightForall(emptySeq ++< pcm1.bot +> forall(z, pcm1.bot.right.head), -1, pcm1.bot.right.head, z)
                            instantiateForall(Proof(IndexedSeq(pb0_0), IndexedSeq(pcm1.bot)), y)
                          },
                          IndexedSeq(-1)
                        ) //  ({x,y}={x',y'}) |- (((y=x)∨(y=y))↔((y=x')∨(y=y')))
                        val pb0_1 = SCSubproof(
                          {
                            val pa1_0 = RightRefl(emptySeq +> (y === y), y === y)
                            val pa1_1 = RightOr(emptySeq +> ((y === y) \/ (y === x)), 0, y === y, y === x)
                            Proof(pa1_0, pa1_1)
                          },
                          display = false
                        ) //  |- (y=x)∨(y=y)
                        val rb0 = byEquiv(pb0_0.bot.right.head, pb0_1.bot.right.head)(pb0_0, pb0_1) //  ({x,y}={x',y'}) |- (y=x')∨(y=y')
                        val pb1 =
                          RightSubstEq(emptySeq ++< rb0.conclusion +< (x === x1) +> ((y === x) \/ (y === y1)), rb0.length - 1, List((x, x1)), LambdaTermFormula(Seq(g), (y === g()) \/ (y === y1)))
                        val rb1 = destructRightOr(
                          rb0.appended(pb1), //  ({x,y}={x',y'}) , x=x'|- (y=x)∨(y=y')
                          y === x,
                          y === y1
                        )
                        val rb2 = rb1.appended(LeftNot(rb1.conclusion +< !(y === x) -> (y === x), rb1.length - 1, y === x)) //  (x=x'), ({x,y}={x',y'}), ¬(y=x) |- (y=y')
                        Proof(rb2.steps, IndexedSeq(pbm1.bot))

                      },
                      IndexedSeq(-1)
                    ) //  ({x,y}={x',y'}), x=x', !y=x |- y=y'
                  ).steps,
                  IndexedSeq(pcm1.bot)
                ),
                IndexedSeq(-1)
              ) // (x=x'), ({x,y}={x',y'}) |- (y'=y)
              val pc1 = RightRefl(emptySeq +> (x === x), x === x)
              val pc2 = RightAnd(emptySeq ++< pc0.bot +> ((y1 === y) /\ (x === x)), Seq(0, 1), Seq(y1 === y, x === x)) // ({x,y}={x',y'}), x=x' |- (x=x /\ y=y')
              val pc3 =
                RightSubstEq(emptySeq ++< pc2.bot +> ((y1 === y) /\ (x1 === x)), 2, List((x, x1)), LambdaTermFormula(Seq(g), (y1 === y) /\ (g() === x))) // ({x,y}={x',y'}), x=x' |- (x=x' /\ y=y')
              val pc4 = RightOr(
                emptySeq ++< pc3.bot +> (pc3.bot.right.head \/ ((x === y1) /\ (y === x1))),
                3,
                pc3.bot.right.head,
                (x === y1) /\ (y === x1)
              ) //  ({x,y}={x',y'}), x=x' |- (x=x' /\ y=y')\/(x=y' /\ y=x')
              val r = Proof(IndexedSeq(pc0, pc1, pc2, pc3, pc4), IndexedSeq(pcm1.bot))
              r
            },
            IndexedSeq(-1)
          ) //  ({x,y}={x',y'}), x=x' |- (x=x' /\ y=y')\/(x=y' /\ y=x')
          ,
          SCSubproof(
            {
              val pdm1 = p0
              val pd0 = SCSubproof(
                {
                  val pd0_m1 = pdm1
                  val pd0_0 = SCSubproof {
                    val ex1x1 = x1 === x1
                    val pd0_0_0 = RightRefl(emptySeq +> ex1x1, ex1x1) //  |- x'=x'
                    val pd0_0_1 = RightOr(emptySeq +> (ex1x1 \/ (x1 === y1)), 0, ex1x1, x1 === y1) //  |- (x'=x' \/ x'=y')
                    Proof(IndexedSeq(pd0_0_0, pd0_0_1))
                  } //  |- (x'=x' \/ x'=y')
                  val pd0_1 = SCSubproof(
                    {
                      val pd0_1_m1 = pd0_m1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                      val pd0_1_0 = RightForall(emptySeq ++< pd0_1_m1.bot +> forall(z, pd0_1_m1.bot.right.head), -1, pd0_1_m1.bot.right.head, z)
                      val rd0_1_1 = instantiateForall(Proof(IndexedSeq(pd0_1_0), IndexedSeq(pd0_m1.bot)), x1) //  ({x,y}={x',y'}) |- (x'=x \/ x'=y) <=> (x'=x' \/ x'=y')
                      rd0_1_1
                    },
                    IndexedSeq(-1)
                  ) //  ({x,y}={x',y'}) |- (x'=x \/ x'=y) <=> (x'=x' \/ x'=y')
                  val pd0_2 = RightSubstIff(
                    pd0_1.bot.right |- ((x1 === x) \/ (x1 === y)),
                    0,
                    List(((x1 === x) \/ (x1 === y), (x1 === x1) \/ (x1 === y1))),
                    LambdaFormulaFormula(Seq(h), h())
                  ) // (x'=x \/ x'=y) <=> (x'=x' \/ x'=y') |- (x'=x \/ x'=y)
                  val pd0_3 = Cut(pd0_1.bot.left |- pd0_2.bot.right, 1, 2, pd0_1.bot.right.head) //  ({x,y}={x',y'}) |- (x=x' \/ y=x')
                  destructRightOr(Proof(IndexedSeq(pd0_0, pd0_1, pd0_2, pd0_3), IndexedSeq(pd0_m1.bot)), x === x1, y === x1) //  ({x,y}={x',y'}) |- x=x',  y=x'
                },
                IndexedSeq(-1)
              ) //  ({x,y}={x',y'}) |- x=x',  y=x' --
              val pd1 = SCSubproof(
                {
                  val pd1_m1 = pdm1
                  val pd1_0 = SCSubproof {
                    val exx = x === x
                    val pd1_0_0 = RightRefl(emptySeq +> exx, exx) //  |- x=x
                    val pd1_0_1 = RightOr(emptySeq +> (exx \/ (x === y)), 0, exx, x === y) //  |- (x=x \/ x=y)
                    Proof(IndexedSeq(pd1_0_0, pd1_0_1))
                  } //  |- (x=x \/ x=y)
                  val pd1_1 = SCSubproof(
                    {
                      val pd1_1_m1 = pd1_m1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                      val pd1_1_0 = RightForall(emptySeq ++< pd1_1_m1.bot +> forall(z, pd1_1_m1.bot.right.head), -1, pd1_1_m1.bot.right.head, z)
                      val rd1_1_1 = instantiateForall(Proof(IndexedSeq(pd1_1_0), IndexedSeq(pd1_m1.bot)), x) //  ({x,y}={x',y'}) |- (x=x \/ x=y) <=> (x=x' \/ x=y')
                      rd1_1_1
                    },
                    IndexedSeq(-1)
                  ) //  //  ({x,y}={x',y'}) |- (x=x \/ x=y) <=> (x=x' \/ x=y')
                  val rd1_2 = byEquiv(pd1_1.bot.right.head, pd1_0.bot.right.head)(pd1_1, pd1_0)
                  val pd1_3 = SCSubproof(Proof(rd1_2.steps, IndexedSeq(pd1_m1.bot)), IndexedSeq(-1)) //  //  ({x,y}={x',y'}) |- x=x' \/ x=y'
                  destructRightOr(Proof(IndexedSeq(pd1_0, pd1_1, pd1_3), IndexedSeq(pd1_m1.bot)), x === x1, x === y1) //  ({x,y}={x',y'}) |- x=x',  x=y'
                },
                IndexedSeq(-1)
              ) //  ({x,y}={x',y'}) |- x=x',  x=y' --
              val pd2 = RightAnd(emptySeq ++< pd1.bot +> (x === x1) +> ((x === y1) /\ (y === x1)), Seq(0, 1), Seq(x === y1, y === x1)) //  ({x,y}={x',y'})  |- x=x', (x=y' /\ y=x') ---
              val pd3 = LeftNot(emptySeq ++< pd2.bot +< !(x === x1) +> ((x === y1) /\ (y === x1)), 2, x === x1) //  ({x,y}={x',y'}), !x===x1 |- (x=y' /\ y=x')
              val pd4 = RightOr(
                emptySeq ++< pd3.bot +> (pd3.bot.right.head \/ ((x === x1) /\ (y === y1))),
                3,
                pd3.bot.right.head,
                (x === x1) /\ (y === y1)
              ) //  ({x,y}={x',y'}), !x===x1 |- (x=x' /\ y=y')\/(x=y' /\ y=x')
              Proof(IndexedSeq(pd0, pd1, pd2, pd3, pd4), IndexedSeq(pdm1.bot))
            },
            IndexedSeq(-1)
          ) //  ({x,y}={x',y'}), !x=x' |- (x=x' /\ y=y')\/(x=y' /\ y=x')
        ).steps,
        IndexedSeq(p0.bot)
      ),
      IndexedSeq(0)
    ) //  ({x,y}={x',y'}) |- (x=x' /\ y=y')\/(x=y' /\ y=x')

    val p2 = RightImplies(emptySeq +> (p1.bot.left.head ==> p1.bot.right.head), 1, p1.bot.left.head, p1.bot.right.head) //   |- ({x,y}={x',y'}) ==> (x=x' /\ y=y')\/(x=y' /\ y=x')
    generalizeToForall(Proof(IndexedSeq(p0, p1, p2), IndexedSeq(() |- pairAxiom)), x, y, x1, y1)
  } using ax"pairAxiom"
  thm"unorderedPair_deconstruction".show

  THEOREM("noUniversalSet") of "∀x. x ∈ ?z ⊢" PROOF {
    val x = SchematicFunctionLabel("x", 0)
    val z = SchematicFunctionLabel("z", 0)
    val x1 = VariableLabel("x")
    val y1 = VariableLabel("y")
    val z1 = VariableLabel("z")
    val h = SchematicPredicateLabel("h", 0)
    val sPhi = SchematicPredicateLabel("P", 2)
    // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,y) /\ sPhi(x,z)))))
    val i1 = () |- comprehensionSchema
    val i2 = thm"russelParadox" // forall(x1, in(x1,y) <=> !in(x1, x1)) |- ()
    val p0 = InstPredSchema(() |- forall(z1, exists(y1, forall(x1, in(x1, y1) <=> (in(x1, z1) /\ !in(x1, x1))))), -1, Map(sPhi -> LambdaTermFormula(Seq(x, z), !in(x(), x()))))
    val s0 = SCSubproof(instantiateForall(Proof(IndexedSeq(p0), IndexedSeq(i1)), z), Seq(-1)) // exists(y1, forall(x1, in(x1,y1) <=> (in(x1,z1) /\ !in(x1, x1))))
    val s1 = hypothesis(in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1))) // in(x,y) <=> (in(x,z) /\ in(x, x)) |- in(x,y) <=> (in(x,z) /\ in(x, x))
    val s2 = RightSubstIff(
      (in(x1, z) <=> And(), in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1))) |- in(x1, y1) <=> (And() /\ !in(x1, x1)),
      1,
      List((in(x1, z), And())),
      LambdaFormulaFormula(Seq(h), in(x1, y1) <=> (h() /\ !in(x1, x1)))
    ) // in(x1,y1) <=> (in(x1,z1) /\ in(x1, x1)) |- in(x,y) <=> (And() /\ in(x1, x1))
    val s3 = Rewrite((in(x1, z), in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1))) |- in(x1, y1) <=> !in(x1, x1), 2)
    val s4 = LeftForall((forall(x1, in(x1, z)), in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1))) |- in(x1, y1) <=> !in(x1, x1), 3, in(x1, z), x1, x1)
    val s5 = LeftForall((forall(x1, in(x1, z)), forall(x1, in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1)))) |- in(x1, y1) <=> !in(x1, x1), 4, in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1)), x1, x1)
    val s6 = RightForall((forall(x1, in(x1, z)), forall(x1, in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1)))) |- forall(x1, in(x1, y1) <=> !in(x1, x1)), 5, in(x1, y1) <=> !in(x1, x1), x1)
    val s7 = InstFunSchema(forall(x1, in(x1, y1) <=> !in(x1, x1)) |- (), -2, Map(SchematicFunctionLabel("y", 0) -> LambdaTermTerm(Nil, y1)))
    val s8 = Cut((forall(x1, in(x1, z)), forall(x1, in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1)))) |- (), 6, 7, forall(x1, in(x1, y1) <=> !in(x1, x1)))
    val s9 = LeftExists((forall(x1, in(x1, z)), exists(y1, forall(x1, in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1))))) |- (), 8, forall(x1, in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1))), y1)
    val s10 = Cut(forall(x1, in(x1, z)) |- (), 0, 9, exists(y1, forall(x1, in(x1, y1) <=> (in(x1, z) /\ !in(x1, x1)))))
    Proof(steps(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10), imports(i1, i2))
  } using (ax"comprehensionSchema", thm"russelParadox")
  show

  private val sx = SchematicFunctionLabel("x", 0)
  private val sy = SchematicFunctionLabel("y", 0)
  val oPair: ConstantFunctionLabel = DEFINE("", sx, sy) as pair(pair(sx, sy), pair(sx, sx))
  show

  THEOREM("functionalMapping") of
    "∀a. (a ∈ ?A) ⇒ ∃!x. ?phi(x, a) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ ?A) ∧ ?phi(x, a)" PROOF {
    val a = VariableLabel("a")
    val b = VariableLabel("b")
    val x = VariableLabel("x")
    val y = VariableLabel("y")
    val z = VariableLabel("z")
    val a1 = SchematicFunctionLabel("a", 0)
    val b1 = SchematicFunctionLabel("b", 0)
    val x1 = SchematicFunctionLabel("x", 0)
    val y1 = SchematicFunctionLabel("y", 0)
    val z1 = SchematicFunctionLabel("z", 0)
    val f = SchematicFunctionLabel("f", 0)
    val h = SchematicPredicateLabel("h", 0)
    val A = SchematicFunctionLabel("A", 0)()
    val X = VariableLabel("X")
    val B = VariableLabel("B")
    val B1 = VariableLabel("B1")
    val phi = SchematicPredicateLabel("phi", 2)
    val sPhi = SchematicPredicateLabel("P", 2)
    val sPsi = SchematicPredicateLabel("P", 3)

    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> H)
    val s0 = hypothesis(H) // () |- existsOne(x, phi(x, a)))
    val s1 = Weakening((H, in(a, A)) |- existsOne(x, phi(x, a)), 0)
    val s2 = Rewrite((H) |- in(a, A) ==> existsOne(x, phi(x, a)), 1)
    // val s3 = RightForall((H) |- forall(a, in(a, A) ==> existsOne(x, phi(x, a))), 2, in(a, A) ==> existsOne(x, phi(x, a)), a) // () |- ∀a∈A. ∃!x. phi(x, a)
    val s3 = hypothesis(H1)
    val i1 = () |- replacementSchema
    val p0 = InstPredSchema(
      () |- instantiatePredicateSchemas(replacementSchema, Map(sPsi -> LambdaTermFormula(Seq(y1, a1, x1), phi(x1, a1)))),
      -1,
      Map(sPsi -> LambdaTermFormula(Seq(y1, a1, x1), phi(x1, a1)))
    )
    val p1 = instantiateForall(Proof(steps(p0), imports(i1)), A)
    val s4 = SCSubproof(p1, Seq(-1)) //
    val s5 = Rewrite(s3.bot.right.head |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 4)
    val s6 = Cut((H1) |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 3, 5, s3.bot.right.head) // ⊢ ∃B. ∀x. (x ∈ A) ⇒ ∃y. (y ∈ B) ∧ (y = (x, b))

    val i2 = () |- comprehensionSchema // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,z) /\ sPhi(x,z)))))
    val q0 = InstPredSchema(
      () |- instantiatePredicateSchemas(comprehensionSchema, Map(sPhi -> LambdaTermFormula(Seq(x1, z1), exists(a, in(a, A) /\ phi(x1, a))))),
      -1,
      Map(sPhi -> LambdaTermFormula(Seq(x1, z1), exists(a, in(a, A) /\ phi(x1, a))))
    )
    val q1 = instantiateForall(Proof(steps(q0), imports(i2)), B)
    val s7 = SCSubproof(q1, Seq(-2)) // ∃y. ∀x. (x ∈ y) ↔ (x ∈ B) ∧ ∃a. a ∈ A /\ x = (a, b)      := exists(y, F(y) )
    Proof(steps(s0, s1, s2, s3, s4, s5, s6, s7), imports(i1, i2))
    val s8 = SCSubproof({
      val y1 = VariableLabel("y1")
      val f = SchematicFunctionLabel("f", 0)
      val s0 = hypothesis(in(y1, B))
      val s1 = RightSubstEq((in(y1, B), x === y1) |- in(x, B), 0, List((x, y1)), LambdaTermFormula(Seq(f), in(f(), B)))
      val s2 = LeftSubstIff(Set(in(y1, B), (x === y1) <=> phi(x, a), phi(x, a)) |- in(x, B), 1, List(((x === y1), phi(x, a))), LambdaFormulaFormula(Seq(h), h()))
      val s3 = LeftSubstEq(Set(y === y1, in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B), 2, List((y, y1)), LambdaTermFormula(Seq(f), (x === f()) <=> phi(x, a)))
      val s4 = LeftSubstIff(Set((y === y1) <=> phi(y1, a), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B), 3, List((phi(y1, a), y1 === y)), LambdaFormulaFormula(Seq(h), h()))
      val s5 = LeftForall(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B), 4, (y === x) <=> phi(x, a), x, y1)
      val s6 = LeftForall(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B), 5, (x === y) <=> phi(x, a), x, x)
      val s7 = LeftExists(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B), 6, forall(x, (y === x) <=> phi(x, a)), y)
      val s8 = Rewrite(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a) /\ in(y1, B), phi(x, a)) |- in(x, B), 7)
      val s9 = LeftExists(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), exists(y1, phi(y1, a) /\ in(y1, B)), phi(x, a)) |- in(x, B), 8, phi(y1, a) /\ in(y1, B), y1)
      val s10 = Rewrite(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), And() ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a)) |- in(x, B), 9)
      val s11 = LeftSubstIff(
        Set(exists(y, forall(x, (y === x) <=> phi(x, a))), in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a), in(a, A)) |- in(x, B),
        10,
        List((And(), in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, phi(y, a) /\ in(y, B)))
      )
      val s12 = LeftForall(
        Set(exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B),
        11,
        in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)),
        a,
        a
      )
      val s13 = LeftSubstIff(
        Set(in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B),
        12,
        List((And(), in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, forall(x, (y === x) <=> phi(x, a))))
      )
      val s14 = LeftForall(
        Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B),
        13,
        in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))),
        a,
        a
      )
      val s15 = Rewrite(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a) /\ in(a, A)) |- in(x, B), 14)
      val s16 = LeftExists(
        Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B),
        15,
        phi(x, a) /\ in(a, A),
        a
      )
      val truc = forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)))
      val s17 = Rewrite(Set(forall(a, in(a, A) ==> existsOne(x, phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B), 16)
      Proof(steps(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17))
      // goal H, ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), ∃a. a ∈ A ∧ phi(x, a) |- (x ∈ B)
      // redGoal ∀a.(a ∈ A) => ∃!x. phi(x, a), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), ∃a. a ∈ A ∧ phi(x, a) |- (x ∈ B)    s17
      // redGoal ∀a.(a ∈ A) => ∃y. ∀x. (x=y) ↔ phi(x, a), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), ∃a. a ∈ A ∧ phi(x, a) |- (x ∈ B)    s16
      // redGoal ∀a.(a ∈ A) => ∃y. ∀x. (x=y) ↔ phi(x, a), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), a ∈ A ∧ phi(x, a) |- (x ∈ B)    s15
      // redGoal ∀a.(a ∈ A) => ∃y. ∀x. (x=y) ↔ phi(x, a), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s14
      // redGoal (a ∈ A) => ∃y. ∀x. (x=y) ↔ phi(x, a), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s13
      // redGoal ∃y. ∀x. (x=y) ↔ phi(x, a), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s12
      // redGoal ∃y. ∀x. (x=y) ↔ phi(x, a), (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s11
      // redGoal ∃y. ∀x. (x=y) ↔ phi(x, a), (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), a ∈ A <=> T,  phi(x, a) |- (x ∈ B)    s11
      // redGoal ∃y. ∀x. (x=y) ↔ phi(x, a), T ⇒ ∃y. y ∈ B ∧ phi(y, a), a ∈ A <=> T,  phi(x, a) |- (x ∈ B)    s10
      // redGoal ∃y. ∀x. (x=y) ↔ phi(x, a), ∃y1. y1 ∈ B ∧ phi(y1, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s9
      // redGoal ∃y. ∀x. (x=y) ↔ phi(x, a), y1 ∈ B ∧ phi(y1, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s8
      // redGoal ∃y. ∀x. (x=y) ↔ phi(x, a), y1 ∈ B, phi(y1, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s7
      // redGoal ∀x. (x=y) ↔ phi(x, a), y1 ∈ B, phi(y1, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s6
      // redGoal (x=y) ↔ phi(x, a), ∀x. (x=y) ↔ phi(x, a), y1 ∈ B, phi(y1, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s5
      // redGoal (x=y) ↔ phi(x, a), (y1=y) ↔ phi(y1, a), y1 ∈ B, phi(y1, a), a ∈ A,  phi(x, a) |- (x ∈ B)    s4
      // redGoal (x=y) ↔ phi(x, a), (y1=y) ↔ phi(y1, a), y1 ∈ B, (y1=y), a ∈ A,  phi(x, a) |- (x ∈ B)     s3
      // redGoal (x=y1) ↔ phi(x, a), (y1=y) ↔ phi(y1, a), y1 ∈ B, (y1=y), a ∈ A,  phi(x, a) |- (x ∈ B)     s2
      // redGoal (x=y1) ↔ phi(x, a), (y1=y) ↔ phi(y1, a), y1 ∈ B, (y1=y), a ∈ A,  x=y1 |- (x ∈ B)     s1
      // redGoal (x=y1) ↔ phi(x, a), (y1=y) ↔ phi(y1, a), y1 ∈ B, (y1=y), a ∈ A,  x=y1 |- (y1 ∈ B)     s0

    }) // H, ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), ∃a. a ∈ A ∧ phi(x, a) |- (x ∈ B)

    val G = forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a))))
    val F = forall(x, iff(in(x, B1), in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))))
    val s9 = SCSubproof({
      val p0 = instantiateForall(Proof(hypothesis(F)), x)
      val left = in(x, B1)
      val right = in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))
      val p1 = p0.withNewSteps(Vector(Rewrite(F |- (left ==> right) /\ (right ==> left), p0.length - 1)))
      val p2 = destructRightAnd(p1, (right ==> left), (left ==> right)) // F |- in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a))) => in(x, B1)
      val p3 = p2.withNewSteps(Vector(Rewrite(Set(F, in(x, B), exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1), p2.length - 1)))
      p3
    }) // have F, (x ∈ B),  ∃a. a ∈ A ∧ x = (a, b) |- (x ∈ B1)
    val s10 = Cut(Set(F, G, H1, exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1), 8, 9, in(x, B)) // redGoal F, ∃a. a ∈ A ∧ x = (a, b), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ y = (a, b) |- (x ∈ B1)
    val s11 = Rewrite(Set(H1, G, F) |- exists(a, in(a, A) /\ (phi(x, a))) ==> in(x, B1), 10) // F |- ∃a. a ∈ A ∧ x = (a, b) => (x ∈ B1)   --- half
    val s12 = SCSubproof({
      val p0 = instantiateForall(Proof(hypothesis(F)), x)
      val left = in(x, B1)
      val right = in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))
      val p1 = p0.withNewSteps(Vector(Rewrite(F |- (left ==> right) /\ (right ==> left), p0.length - 1)))
      val p2 = destructRightAnd(p1, (left ==> right), (right ==> left)) // F |- in(x, B1) => in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a))) =>
      val p3 = p2.withNewSteps(Vector(Rewrite(Set(F, in(x, B1)) |- exists(a, in(a, A) /\ (phi(x, a))) /\ in(x, B), p2.length - 1)))
      val p4 = destructRightAnd(p3, exists(a, in(a, A) /\ (phi(x, a))), in(x, B))
      val p5 = p4.withNewSteps(Vector(Rewrite(F |- in(x, B1) ==> exists(a, in(a, A) /\ (phi(x, a))), p4.length - 1)))
      p5
    }) // have F |- (x ∈ B1) ⇒ ∃a. a ∈ A ∧ x = (a, b)    --- other half
    val s13 = RightIff((H1, G, F) |- in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))), 11, 12, in(x, B1), exists(a, in(a, A) /\ (phi(x, a)))) // have F |- (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
    val s14 =
      RightForall((H1, G, F) |- forall(x, in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a)))), 13, in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))), x) // G, F |- ∀x. (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)

    val i3 = () |- extensionalityAxiom
    val s15 = SCSubproof(
      {
        val i1 = s13.bot // G, F |- (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
        val i2 = () |- extensionalityAxiom
        val t0 = RightSubstIff(
          Set(H1, G, F, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, X) <=> in(x, B1),
          -1,
          List((in(x, X), exists(a, in(a, A) /\ (phi(x, a))))),
          LambdaFormulaFormula(Seq(h), h() <=> in(x, B1))
        ) // redGoal2  F, (z ∈ X) <=> ∃a. a ∈ A ∧ z = (a, b) |- (z ∈ X) <=> (z ∈ B1)
        val t1 = LeftForall(
          Set(H1, G, F, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) |- in(x, X) <=> in(x, B1),
          0,
          in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))),
          x,
          x
        ) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- (z ∈ X) <=> (z ∈ B1)
        val t2 = RightForall(t1.bot.left |- forall(x, in(x, X) <=> in(x, B1)), 1, in(x, X) <=> in(x, B1), x) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- ∀z. (z ∈ X) <=> (z ∈ B1)
        val t3 =
          SCSubproof(instantiateForall(Proof(steps(Rewrite(() |- extensionalityAxiom, -1)), imports(() |- extensionalityAxiom)), X, B1), Vector(-2)) // (∀z. (z ∈ X) <=> (z ∈ B1)) <=> (X === B1)))
        val t4 = RightSubstIff(
          t1.bot.left ++ t3.bot.right |- X === B1,
          2,
          List((X === B1, forall(z, in(z, X) <=> in(z, B1)))),
          LambdaFormulaFormula(Seq(h), h())
        ) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)], (∀z. (z ∈ X) <=> (z ∈ B1)) <=> (X === B1))) |- X=B1
        val t5 = Cut(t1.bot.left |- X === B1, 3, 4, t3.bot.right.head) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- X=B1
        val t6 = Rewrite(Set(H1, G, F) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) ==> (X === B1), 5) //  F |- [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] ==> X=B1
        val i3 = s14.bot // F |- ∀x. (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
        val t7 = RightSubstEq(
          Set(H1, G, F, X === B1) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
          -3,
          List((X, B1)),
          LambdaTermFormula(Seq(f), forall(x, in(x, f()) <=> exists(a, in(a, A) /\ phi(x, a))))
        ) // redGoal1 F, X=B1 |- [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
        val t8 = Rewrite(
          Set(H1, G, F) |- X === B1 ==> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
          7
        ) // redGoal1 F |- X=B1 ==> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]      -------second half with t6
        val t9 = RightIff(
          Set(H1, G, F) |- (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
          6,
          8,
          X === B1,
          forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))
        ) // goal  F |- X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]

        Proof(steps(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9), imports(i1, i2, i3))
      },
      Vector(13, -3, 14)
    ) // goal  F |- X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s16 = RightForall(
      (H1, G, F) |- forall(X, (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))),
      15,
      (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
      X
    ) // goal  F |- ∀X. X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s17 = RightExists(
      (H1, G, F) |- exists(y, forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))),
      16,
      forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))),
      y,
      B1
    )
    val s18 = LeftExists((exists(B1, F), G, H1) |- s17.bot.right, 17, F, B1) //  ∃B1. F |- ∃B1. ∀X. X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s19 = Rewrite(s18.bot.left |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))), 18) //  ∃B1. F |- ∃!X. [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s20 = Cut((G, H1) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))), 7, 19, exists(B1, F))
    val s21 = LeftExists((H1, exists(B, G)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))), 20, G, B)
    val s22 = Cut(H1 |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ phi(x, a)))), 6, 21, exists(B, G))
    val res = steps(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22)
    Proof(res, imports(i1, i2, i3))
  } using (ax"replacementSchema", ax"comprehensionSchema", ax"extensionalityAxiom")
  show

  THEOREM("lemmaLayeredTwoArgumentsMap") of
    "∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)" PROOF {
    val a = VariableLabel("a")
    val b = VariableLabel("b")
    val x = VariableLabel("x")
    val x1 = VariableLabel("x1")
    val y = VariableLabel("y")
    val z = VariableLabel("z")
    val a_ = SchematicFunctionLabel("a", 0)
    val b_ = SchematicFunctionLabel("b", 0)
    val x_ = SchematicFunctionLabel("x", 0)
    val x1_ = SchematicFunctionLabel("x1", 0)
    val y_ = SchematicFunctionLabel("y", 0)
    val z_ = SchematicFunctionLabel("z", 0)
    val f = SchematicFunctionLabel("f", 0)
    val h = SchematicPredicateLabel("h", 0)
    val A = SchematicFunctionLabel("A", 0)()
    val X = VariableLabel("X")
    val B = SchematicFunctionLabel("B", 0)()
    val B1 = VariableLabel("B1")
    val phi = SchematicPredicateLabel("phi", 2)
    val psi = SchematicPredicateLabel("psi", 3)
    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> H)
    val i1 = thm"functionalMapping"
    val H2 = instantiatePredicateSchemas(H1, Map(phi -> LambdaTermFormula(Seq(x_, a_), psi(x_, a_, b))))
    val s0 = InstPredSchema((H2) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))), -1, Map(phi -> LambdaTermFormula(Seq(x_, a_), psi(x_, a_, b))))
    val s1 = Weakening((H2, in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))), 0)
    val s2 =
      LeftSubstIff((in(b, B) ==> H2, in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))), 1, List((in(b, B), And())), LambdaFormulaFormula(Seq(h), h() ==> H2))
    val s3 = LeftForall((forall(b, in(b, B) ==> H2), in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))), 2, in(b, B) ==> H2, b, b)
    val s4 = Rewrite(forall(b, in(b, B) ==> H2) |- in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))), 3)
    val s5 = RightForall(
      forall(b, in(b, B) ==> H2) |- forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))),
      4,
      in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))),
      b
    )
    val s6 = InstFunSchema(
      forall(b, in(b, B) ==> existsOne(X, phi(X, b))) |- instantiateFunctionSchemas(i1.right.head, Map(SchematicFunctionLabel("A", 0) -> LambdaTermTerm(Nil, B))),
      -1,
      Map(SchematicFunctionLabel("A", 0) -> LambdaTermTerm(Nil, B))
    )
    val s7 = InstPredSchema(
      forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) |- existsOne(
        X,
        forall(x, in(x, X) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
      ),
      6,
      Map(phi -> LambdaTermFormula(Seq(y_, b_), forall(x, in(x, y_) <=> exists(a, in(a, A) /\ psi(x, a, b_)))))
    )
    val s8 = Cut(
      forall(b, in(b, B) ==> H2) |- existsOne(X, forall(x, in(x, X) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))),
      5,
      7,
      forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))))
    )
    Proof(Vector(s0, s1, s2, s3, s4, s5, s6, s7, s8), Vector(i1))
    // have ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s0
    // have (b ∈ B), ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s1
    // have (b ∈ B), (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s2
    // have (b ∈ B), ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s3
    // have ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢  (b ∈ B) ⇒ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s4
    // have ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢  ∀b. (b ∈ B) ⇒ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s5
    // by thmMapFunctional have ∀b. (b ∈ B) ⇒ ∃!x. ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)        phi(x, b) = ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)    s6
    // have ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b)    |-    ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)   s7

  } using (thm"functionalMapping")
  show

  THEOREM("applyFunctionToUniqueObject") of
    "∃!x. ?phi(x) ⊢ ∃!z. ∃x. (z = ?F(x)) ∧ ?phi(x)" PROOF {
    val x = VariableLabel("x")
    val x1 = VariableLabel("x1")
    val z = VariableLabel("z")
    val z1 = VariableLabel("z1")
    val F = SchematicFunctionLabel("F", 1)
    val f = SchematicFunctionLabel("f", 0)
    val phi = SchematicPredicateLabel("phi", 1)
    val g = SchematicPredicateLabel("g", 0)

    val g2 = SCSubproof({
      val s0 = hypothesis(F(x1) === z)
      val s1 = LeftSubstEq((x === x1, F(x) === z) |- F(x1) === z, 0, List((x, x1)), LambdaTermFormula(Seq(f), F(f()) === z))
      val s2 = LeftSubstIff(Set(phi(x) <=> (x === x1), phi(x), F(x) === z) |- F(x1) === z, 1, List((x === x1, phi(x))), LambdaFormulaFormula(Seq(g), g()))
      val s3 = LeftForall(Set(forall(x, phi(x) <=> (x === x1)), phi(x), F(x) === z) |- F(x1) === z, 2, phi(x) <=> (x === x1), x, x)
      val s4 = Rewrite(Set(forall(x, phi(x) <=> (x === x1)), phi(x) /\ (F(x) === z)) |- F(x1) === z, 3)
      val s5 = LeftExists(Set(forall(x, phi(x) <=> (x === x1)), exists(x, phi(x) /\ (F(x) === z))) |- F(x1) === z, 4, phi(x) /\ (F(x) === z), x)
      val s6 = Rewrite(forall(x, phi(x) <=> (x === x1)) |- exists(x, phi(x) /\ (F(x) === z)) ==> (F(x1) === z), 5)
      Proof(steps(s0, s1, s2, s3, s4, s5, s6))
    }) // redGoal2 ∀x. x=x1 <=> phi(x)   ⊢   ∃x. z=F(x) /\ phi(x) ==> F(x1)=z  g2.s5

    val g1 = SCSubproof({
      val s0 = hypothesis(phi(x1))
      val s1 = LeftForall(forall(x, (x === x1) <=> phi(x)) |- phi(x1), 0, (x === x1) <=> phi(x), x, x1)
      val s2 = hypothesis(z === F(x1))
      val s3 = RightAnd((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- (z === F(x1)) /\ phi(x1), Seq(2, 1), Seq(z === F(x1), phi(x1)))
      val s4 = RightExists((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- exists(x, (z === F(x)) /\ phi(x)), 3, (z === F(x)) /\ phi(x), x, x1)
      val s5 = Rewrite(forall(x, (x === x1) <=> phi(x)) |- z === F(x1) ==> exists(x, (z === F(x)) /\ phi(x)), 4)
      Proof(steps(s0, s1, s2, s3, s4, s5))
    })

    val s0 = g1
    val s1 = g2
    val s2 = RightIff(forall(x, (x === x1) <=> phi(x)) |- (z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x)), 0, 1, z === F(x1), exists(x, (z === F(x)) /\ phi(x)))
    val s3 = RightForall(forall(x, (x === x1) <=> phi(x)) |- forall(z, (z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x))), 2, (z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x)), z)
    val s4 = RightExists(
      forall(x, (x === x1) <=> phi(x)) |- exists(z1, forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x)))),
      3,
      forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x))),
      z1,
      F(x1)
    )
    val s5 = LeftExists(exists(x1, forall(x, (x === x1) <=> phi(x))) |- exists(z1, forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x)))), 4, forall(x, (x === x1) <=> phi(x)), x1)
    val s6 = Rewrite(existsOne(x, phi(x)) |- existsOne(z, exists(x, (z === F(x)) /\ phi(x))), 5) // goal ∃!x. phi(x)   ⊢   ∃!z. ∃x. z=F(x) /\ phi(x)
    Proof(Vector(s0, s1, s2, s3, s4, s5, s6))
  } using ()
  show

  THEOREM("mapTwoArguments") of
    "∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!z. ∃x. (z = U(x)) ∧ ∀x_0. (x_0 ∈ x) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x_0) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)" PROOF {
    val a = VariableLabel("a")
    val b = VariableLabel("b")
    val x = VariableLabel("x")
    val x1 = VariableLabel("x1")
    val x_ = SchematicFunctionLabel("x", 0)
    val y_ = SchematicFunctionLabel("y", 0)
    val F = SchematicFunctionLabel("F", 1)
    val A = SchematicFunctionLabel("A", 0)()
    val B = SchematicFunctionLabel("B", 0)()
    val phi = SchematicPredicateLabel("phi", 1)
    val psi = SchematicPredicateLabel("psi", 3)

    val i1 = thm"lemmaLayeredTwoArgumentsMap"
    val i2 = thm"applyFunctionToUniqueObject"
    val rPhi = forall(x, in(x, y_) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
    val seq0 = instantiatePredicateSchemaInSequent(i2, Map(phi -> LambdaTermFormula(Seq(y_), rPhi)))
    val s0 = InstPredSchema(seq0, -2, Map(phi -> LambdaTermFormula(Seq(y_), rPhi))) // val s0 = InstPredSchema(instantiatePredicateSchemaInSequent(i2, phi, rPhi, Seq(X)), -2, phi, rPhi, Seq(X))
    val seq1 = instantiateFunctionSchemaInSequent(seq0, Map(F -> LambdaTermTerm(Seq(x_), union(x_))))
    val s1 = InstFunSchema(seq1, 0, Map(F -> LambdaTermTerm(Seq(x_), union(x_))))
    val s2 = Cut(i1.left |- seq1.right, -1, 1, seq1.left.head)
    Proof(steps(s0, s1, s2), imports(i1, i2))
  } using (thm"lemmaLayeredTwoArgumentsMap", thm"applyFunctionToUniqueObject")
  show



  val A = SchematicFunctionLabel("A", 0)
  val B = SchematicFunctionLabel("B", 0)
  private val sz = SchematicFunctionLabel("z", 0)
  val cartesianProduct: ConstantFunctionLabel =
    DEFINE("cartProd", A, B) asThe sz suchThat {
      val a = VariableLabel("a")
      val b = VariableLabel("b")
      val x = VariableLabel("x")
      val x0 = VariableLabel("x0")
      val x1 = VariableLabel("x1")
      val A = SchematicFunctionLabel("A", 0)()
      val B = SchematicFunctionLabel("B", 0)()
      exists(x, (sz===union(x)) /\ forall(x0, in(x0, x) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x0) <=> exists(a, in(a, A) /\ (x1 === oPair(a, b)))))))
    } PROOF {
      def makeFunctional(t: Term): Proof = {
        val x = VariableLabel(freshId(t.freeVariables.map(_.id), "x"))
        val y = VariableLabel(freshId(t.freeVariables.map(_.id), "y"))
        val s0 = RightRefl(() |- t === t, t === t)
        val s1 = Rewrite(() |- (x === t) <=> (x === t), 0)
        val s2 = RightForall(() |- forall(x, (x === t) <=> (x === t)), 1, (x === t) <=> (x === t), x)
        val s3 = RightExists(() |- exists(y, forall(x, (x === y) <=> (x === t))), 2, forall(x, (x === y) <=> (x === t)), y, t)
        val s4 = Rewrite(() |- existsOne(x, x === t), 3)
        Proof(s0, s1, s2, s3, s4)
      }
      val a = VariableLabel("a")
      val b = VariableLabel("b")
      val x = VariableLabel("x")
      val a_ = SchematicFunctionLabel("a", 0)
      val b_ = SchematicFunctionLabel("b", 0)
      val x_ = SchematicFunctionLabel("x", 0)
      val x1 = VariableLabel("x1")
      val F = SchematicFunctionLabel("F", 1)
      val A = SchematicFunctionLabel("A", 0)()
      val X = VariableLabel("X")
      val B = SchematicFunctionLabel("B", 0)()
      val phi = SchematicPredicateLabel("phi", 1)
      val psi = SchematicPredicateLabel("psi", 3)

      val i1 = thm"mapTwoArguments" // ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!z. ∃x. (z = U(x)) ∧ ∀x_0. (x_0 ∈ x) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x_0) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)

      val s0 = SCSubproof({
        val s0 = SCSubproof(makeFunctional(oPair(a, b)))
        val s1 = Weakening((in(b, B), in(a, A)) |- s0.bot.right, 0)
        val s2 = Rewrite(in(b, B) |- in(a, A) ==> s0.bot.right.head, 1)
        val s3 = RightForall(in(b, B) |- forall(a, in(a, A) ==> s0.bot.right.head), 2, in(a, A) ==> s0.bot.right.head, a)
        val s4 = Rewrite(() |- in(b, B) ==> forall(a, in(a, A) ==> s0.bot.right.head), 3)
        val s5 = RightForall(() |- forall(b, in(b, B) ==> forall(a, in(a, A) ==> s0.bot.right.head)), 4, in(b, B) ==> forall(a, in(a, A) ==> s0.bot.right.head), b)
        Proof(steps(s0, s1, s2, s3, s4, s5))
      }) // ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. x= (a, b)

      val s1 = InstPredSchema(
        instantiatePredicateSchemaInSequent(i1, Map(psi -> LambdaTermFormula(Seq(x_, a_, b_), x_ === oPair(a_, b_)))),
        -1,
        Map(psi -> LambdaTermFormula(Seq(x_, a_, b_), x_ === oPair(a_, b_)))
      )
      val s2 = Cut(() |- s1.bot.right, 0, 1, s1.bot.left.head)
      Proof(steps(s0, s1, s2), imports(i1))
    } using (thm"mapTwoArguments")
  show

}
