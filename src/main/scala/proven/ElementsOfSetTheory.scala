package proven
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.KernelHelpers.{*, given}
import lisa.kernel.Printer
import proven.tactics.ProofTactics.*
import proven.tactics.Destructors.*
import lisa.settheory.AxiomaticSetTheory.*

import scala.collection.immutable.SortedSet
import lisa.kernel.proof.{SCProof, SCProofChecker}
import lisa.settheory.AxiomaticSetTheory
import proven.ElementsOfSetTheory.theory

import scala.collection.immutable

/**
 * Some proofs in set theory. See it as a proof of concept.
 */
object ElementsOfSetTheory {

  val theory = AxiomaticSetTheory.runningSetTheory
  def axiom(f: Formula): theory.Axiom = theory.getAxiom(f).get

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  private val x1 = VariableLabel("x'")
  private val y1 = VariableLabel("y'")
  private val z = VariableLabel("z")
  private val g = SchematicFunctionLabel("g", 0)
  private val h = SchematicPredicateLabel("h", 0)

  val oPair: ConstantFunctionLabel = ConstantFunctionLabel("ordered_pair", 2)
  val oPairFirstElement: ConstantFunctionLabel = ConstantFunctionLabel("ordered_pair_first_element", 1)
  val oPairSecondElement: ConstantFunctionLabel = ConstantFunctionLabel("ordered_pair_second_element", 1)

  val proofUnorderedPairSymmetry: SCProof = {
    val imps: IndexedSeq[Sequent] = IndexedSeq(() |- extensionalityAxiom, () |- pairAxiom)
    val s0 = Rewrite(() |- extensionalityAxiom, -1)
    val pairExt1 = instantiateForall(new SCProof(IndexedSeq(s0), imps), extensionalityAxiom, pair(x, y))
    val pairExt2 = instantiateForall(pairExt1, pairExt1.conclusion.right.head, pair(y, x))
    val t0 = Rewrite(() |- pairAxiom, -2)
    val pairSame11 = instantiateForall(new SCProof(IndexedSeq(t0), imps), pairAxiom, x)
    val pairSame12 = instantiateForall(pairSame11, pairSame11.conclusion.right.head, y)
    val pairSame13 = instantiateForall(pairSame12, pairSame12.conclusion.right.head, z)

    val pairSame21 = instantiateForall(new SCProof(IndexedSeq(t0), imps), pairAxiom, y)
    val pairSame22 = instantiateForall(pairSame21, pairSame21.conclusion.right.head, x)
    val pairSame23 = instantiateForall(pairSame22, pairSame22.conclusion.right.head, z)
    val condsymor = ((y === z) \/ (x === z)) <=> ((x === z) \/ (y === z))
    val pairSame24 = pairSame23 // + st1

    val pr0 = SCSubproof(pairSame13, Seq(-1, -2))
    val pr1 = SCSubproof(pairSame23, Seq(-1, -2))
    val pr2 = RightSubstIff(
      Sequent(pr1.bot.right, Set(in(z, pair(x, y)) <=> in(z, pair(y, x)))),
      0,
      List(((x === z) \/ (y === z), in(z, pair(y, x)))),
      LambdaFormulaFormula(Seq(h), in(z, pair(x, y)) <=> h())
    )
    val pr3 = Cut(Sequent(pr1.bot.left, pr2.bot.right), 1, 2, pr2.bot.left.head)
    // val pr4 = LeftAxiom(Sequent(Set(), pr2.bot.right), 3, pr1.bot.left.head, "")
    val pr4 = RightForall(Sequent(Set(), Set(forall(z, pr2.bot.right.head))), 3, pr2.bot.right.head, z)
    val fin = SCProof(IndexedSeq(pr0, pr1, pr2, pr3, pr4), imps)
    val fin2 = byEquiv(pairExt2.conclusion.right.head, fin.conclusion.right.head)(SCSubproof(pairExt2, Seq(-1, -2)), SCSubproof(fin, Seq(-1, -2)))
    val fin3 = generalizeToForall(fin2, fin2.conclusion.right.head, x)
    val fin4 = generalizeToForall(fin3, fin3.conclusion.right.head, y)
    fin4.copy(imports = imps)
  } //   |- ∀∀({x$1,y$2}={y$2,x$1})
  val thm_proofUnorderedPairSymmetry: theory.Theorem = theory.proofToTheorem("proofUnorderedPairSymmetry", proofUnorderedPairSymmetry, Seq(axiom(extensionalityAxiom), axiom(pairAxiom))).get

  val proofUnorderedPairDeconstruction: SCProof = {
    val pxy = pair(x, y)
    val pxy1 = pair(x1, y1)
    val zexy = (z === x) \/ (z === y)
    val p0 = SCSubproof(
      {
        val p0 = SCSubproof(
          {
            val zf = in(z, pxy)
            val p1_0 = hypothesis(zf)
            val p1_1 = RightImplies(emptySeq +> (zf ==> zf), 0, zf, zf)
            val p1_2 = RightIff(emptySeq +> (zf <=> zf), 1, 1, zf, zf) //  |- (z in {x,y} <=> z in {x,y})
            val p1_3 = RightSubstEq(emptySeq +< (pxy === pxy1) +> (zf <=> in(z, pxy1)), 2, List((pxy, pxy1)), LambdaTermFormula(Seq(g), zf <=> in(z, g())))
            SCProof(IndexedSeq(p1_0, p1_1, p1_2, p1_3), IndexedSeq(() |- pairAxiom))
          },
          Seq(-1),
          display = true
        ) //  ({x,y}={x',y'}) |- ((z∈{x,y})↔(z∈{x',y'}))
        val p1 = SCSubproof(
          {
            val p1_0 = Rewrite(() |- pairAxiom, -1) //  |- ∀∀∀((z$1∈{x$3,y$2})↔((x$3=z$1)∨(y$2=z$1)))
            val p1_1 = instantiateForall(SCProof(IndexedSeq(p1_0), IndexedSeq(() |- pairAxiom)), x, y, z)
            p1_1
          },
          Seq(-1),
          display = true
        ) //  |- (z in {x,y}) <=> (z=x \/ z=y)
        val p2 = SCSubproof(
          {
            val p2_0 = Rewrite(() |- pairAxiom, -1) //  |- ∀∀∀((z$1∈{x$3,y$2})↔((x$3=z$1)∨(y$2=z$1)))
            val p2_1 = instantiateForall(SCProof(IndexedSeq(p2_0), IndexedSeq(() |- pairAxiom)), x1, y1, z)
            p2_1
          },
          Seq(-1),
          display = true
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
        SCProof(IndexedSeq(p0, p1, p2, p3, p4, p5), IndexedSeq(() |- pairAxiom))
      },
      Seq(-1)
    ) //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))

    val p1 = SCSubproof(
      SCProof(
        byCase(x === x1)(
          SCSubproof(
            {
              val pcm1 = p0
              val pc0 = SCSubproof(
                SCProof(
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
                                val r = SCProof(pa0_0_0, pa0_1_1, pa0_1_2, pa0_1_3, pa0_1_4, pa0_1_5)
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
                            val ra0_0 = instantiateForall(SCProof(IndexedSeq(pa0_0, pa0_1, pa0_2, pa0_3, pa0_4), IndexedSeq(pa0_m1.bot)), y1) //  (x=y), ({x,y}={x',y'}) |- ((y'=x)↔((y'=x')∨(y'=y')))
                            ra0_0
                          },
                          IndexedSeq(-1)
                        ) //  ({x,y}={x',y'}) y=x|- ((y'=x)↔((y'=x')∨(y'=y')))
                        val pa1 = SCSubproof(
                          {
                            val pa1_0 = RightRefl(emptySeq +> (y1 === y1), y1 === y1)
                            val pa1_1 = RightOr(emptySeq +> ((y1 === y1) \/ (y1 === x1)), 0, y1 === y1, y1 === x1)
                            SCProof(pa1_0, pa1_1)
                          },
                          display = false
                        ) //  |- (y'=x' \/ y'=y')
                        val ra3 = byEquiv(pa0.bot.right.head, pa1.bot.right.head)(pa0, pa1) // ({x,y}={x',y'}) y=x|- ((y'=x)
                        val pal = RightSubstEq(emptySeq ++< pa0.bot +> (y1 === y), ra3.length - 1, List((x, y)), LambdaTermFormula(Seq(g), y1 === g()))
                        SCProof(ra3.steps, IndexedSeq(pam1.bot)) appended pal // (x=y), ({x,y}={x',y'}) |- (y'=y)
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
                            instantiateForall(SCProof(IndexedSeq(pb0_0), IndexedSeq(pcm1.bot)), y)
                          },
                          IndexedSeq(-1)
                        ) //  ({x,y}={x',y'}) |- (((y=x)∨(y=y))↔((y=x')∨(y=y')))
                        val pb0_1 = SCSubproof(
                          {
                            val pa1_0 = RightRefl(emptySeq +> (y === y), y === y)
                            val pa1_1 = RightOr(emptySeq +> ((y === y) \/ (y === x)), 0, y === y, y === x)
                            SCProof(pa1_0, pa1_1)
                          },
                          display = false
                        ) //  |- (y=x)∨(y=y)
                        val rb0 = byEquiv(pb0_0.bot.right.head, pb0_1.bot.right.head)(pb0_0, pb0_1) //  ({x,y}={x',y'}) |- (y=x')∨(y=y')
                        val pb1 =
                          RightSubstEq(emptySeq ++< rb0.conclusion +< (x === x1) +> ((y === x) \/ (y === y1)), rb0.length - 1, List((x, x1)), LambdaTermFormula(Seq(g), (y === g()) \/ (y === y1)))
                        val rb1 = destructRightOr(
                          rb0 appended pb1, //  ({x,y}={x',y'}) , x=x'|- (y=x)∨(y=y')
                          y === x,
                          y === y1
                        )
                        val rb2 = rb1 appended LeftNot(rb1.conclusion +< !(y === x) -> (y === x), rb1.length - 1, y === x) //  (x=x'), ({x,y}={x',y'}), ¬(y=x) |- (y=y')
                        SCProof(rb2.steps, IndexedSeq(pbm1.bot))

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
              val r = SCProof(IndexedSeq(pc0, pc1, pc2, pc3, pc4), IndexedSeq(pcm1.bot))
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
                    SCProof(IndexedSeq(pd0_0_0, pd0_0_1))
                  } //  |- (x'=x' \/ x'=y')
                  val pd0_1 = SCSubproof(
                    {
                      val pd0_1_m1 = pd0_m1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                      val pd0_1_0 = RightForall(emptySeq ++< pd0_1_m1.bot +> forall(z, pd0_1_m1.bot.right.head), -1, pd0_1_m1.bot.right.head, z)
                      val rd0_1_1 = instantiateForall(SCProof(IndexedSeq(pd0_1_0), IndexedSeq(pd0_m1.bot)), x1) //  ({x,y}={x',y'}) |- (x'=x \/ x'=y) <=> (x'=x' \/ x'=y')
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
                  destructRightOr(SCProof(IndexedSeq(pd0_0, pd0_1, pd0_2, pd0_3), IndexedSeq(pd0_m1.bot)), x === x1, y === x1) //  ({x,y}={x',y'}) |- x=x',  y=x'
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
                    SCProof(IndexedSeq(pd1_0_0, pd1_0_1))
                  } //  |- (x=x \/ x=y)
                  val pd1_1 = SCSubproof(
                    {
                      val pd1_1_m1 = pd1_m1 //  ({x,y}={x',y'}) |- (((z=x)∨(z=y))↔((z=x')∨(z=y')))
                      val pd1_1_0 = RightForall(emptySeq ++< pd1_1_m1.bot +> forall(z, pd1_1_m1.bot.right.head), -1, pd1_1_m1.bot.right.head, z)
                      val rd1_1_1 = instantiateForall(SCProof(IndexedSeq(pd1_1_0), IndexedSeq(pd1_m1.bot)), x) //  ({x,y}={x',y'}) |- (x=x \/ x=y) <=> (x=x' \/ x=y')
                      rd1_1_1
                    },
                    IndexedSeq(-1)
                  ) //  //  ({x,y}={x',y'}) |- (x=x \/ x=y) <=> (x=x' \/ x=y')
                  val rd1_2 = byEquiv(pd1_1.bot.right.head, pd1_0.bot.right.head)(pd1_1, pd1_0)
                  val pd1_3 = SCSubproof(SCProof(rd1_2.steps, IndexedSeq(pd1_m1.bot)), IndexedSeq(-1)) //  //  ({x,y}={x',y'}) |- x=x' \/ x=y'
                  destructRightOr(SCProof(IndexedSeq(pd1_0, pd1_1, pd1_3), IndexedSeq(pd1_m1.bot)), x === x1, x === y1) //  ({x,y}={x',y'}) |- x=x',  x=y'
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
              SCProof(IndexedSeq(pd0, pd1, pd2, pd3, pd4), IndexedSeq(pdm1.bot))
            },
            IndexedSeq(-1)
          ) //  ({x,y}={x',y'}), !x=x' |- (x=x' /\ y=y')\/(x=y' /\ y=x')
        ).steps,
        IndexedSeq(p0.bot)
      ),
      IndexedSeq(0)
    ) //  ({x,y}={x',y'}) |- (x=x' /\ y=y')\/(x=y' /\ y=x')

    val p2 = RightImplies(emptySeq +> (p1.bot.left.head ==> p1.bot.right.head), 1, p1.bot.left.head, p1.bot.right.head) //   |- ({x,y}={x',y'}) ==> (x=x' /\ y=y')\/(x=y' /\ y=x')
    generalizeToForall(SCProof(IndexedSeq(p0, p1, p2), IndexedSeq(() |- pairAxiom)), x, y, x1, y1)
  } // |- ∀∀∀∀(({x$4,y$3}={x'$2,y'$1})⇒(((y'$1=y$3)∧(x'$2=x$4))∨((x$4=y'$1)∧(y$3=x'$2))))

  val thm_proofUnorderedPairDeconstruction = theory.proofToTheorem("proofUnorderedPairDeconstruction", proofUnorderedPairDeconstruction, Seq(axiom(pairAxiom))).get

  // i2, i1, p0, p1, p2, p3

  val orderedPairDefinition: SCProof = simpleFunctionDefinition(pair(pair(x, y), pair(x, x)), Seq(x, y))

  val def_oPair = theory.makeFunctionDefinition(orderedPairDefinition, Nil, oPair, Seq(x, y), x1, x1 === pair(pair(x, y), pair(x, x)))

  /*
  val proofOrderedPairDeconstruction: SCProof = {

    val opairxy = pair(pair(x, y), pair(x, x))
    val opairxx = pair(pair(x, x), pair(x, x))
    val opairxy1 = pair(pair(x1, y1), pair(x1, x1))
    val opairxx1 = pair(pair(x1, x1), pair(x1, x1))
    val pairxy = pair(x, y)
    val pairxx = pair(x, x)
    val pairxy1 = pair(x1, y1)
    val pairxx1 = pair(x1, x1)


    val p0 = SCSubproof(orderedPairDefinition, display = false)
    val p1 = SCSubproof(proofUnorderedPairDeconstruction) //  |- ∀∀∀∀(({x$4,y$3}={x'$2,y'$1})⇒(((y'$1=y$3)∧(x'$2=x$4))∨((x$4=y'$1)∧(y$3=x'$2))))

    val p2: SCSubproof = SCSubproof(SCProof(byCase(x === y)(
      {
        val p2_0 = SCSubproof(SCProof({
          val pa2_0 = SCSubproof({
            val p2_0_0 = UseFunctionDefinition(emptySeq +> (oPair(x, y) === opairxy), oPair, Seq(x, y)) // |- (x, y) === {{x,y}, {x,x}}
            val p2_0_1 = RightSubstEq(emptySeq +< (x === y) +> (oPair(x, y) === opairxx),
              0, x, y, oPair(x, y) === pair(pair(x, z), pair(x, x)), z) // (x=y) |- ((x,y)={{x,x},{x,x}})
            val p2_0_2 = UseFunctionDefinition(emptySeq +> (oPair(x1, y1) === opairxy1), oPair, Seq(x1, y1)) // |- (x1, y1) === {{x1,y1}, {x1,x1}}
            val p2_0_3 = RightSubstEq(emptySeq +< (oPair(x, y) === oPair(x1, y1)) +< (x === y) +> (oPair(x1, y1) === pair(pair(x, x), pair(x, x))),
              1, oPair(x, y), oPair(x1, y1), z === pair(pair(x, x), pair(x, x)), z) // (x=y), (x1,y1)=(x,y) |- ((x1,y1)={{x,x},{x,x}})
            val p2_0_4 = RightSubstEq(emptySeq +< (oPair(x, y) === oPair(x1, y1)) +< (x === y) +< (opairxy1 === oPair(x1, y1)) +> (pair(pair(x, x), pair(x, x)) === pair(pair(x1, y1), pair(x1, x1))),
              3, opairxy1, oPair(x1, y1), z === pair(pair(x, x), pair(x, x)), z) // (x=y), (x1,y1)=(x,y), (x1,y1)={{x1,y1}, {x1,x1}} |- {{x1,y1}, {x1,x1}}={{x,x},{x,x}})
            val p2_0_5 = Cut(emptySeq +< (oPair(x, y) === oPair(x1, y1)) +< (x === y) +> (pair(pair(x, x), pair(x, x)) === pair(pair(x1, y1), pair(x1, x1))),
              2, 4, opairxy1 === oPair(x1, y1))
            SCProof(IndexedSeq(p2_0_0, p2_0_1, p2_0_2, p2_0_3, p2_0_4, p2_0_5), IndexedSeq(p0))
          }, IndexedSeq(-1)) // ((x,y)=(x',y')), (x=y) |- ({{x,x},{x,x}}={{x',y'},{x',x'}})
          val pa2_1 = SCSubproof({
            instantiateForall(SCProof(IndexedSeq(), IndexedSeq(p1)), pairxx, pairxx, pairxy1, pairxx1)
          }, IndexedSeq(-2)) //  ({{x,x},{x,x}}={{x',y'},{x',x'}})⇒((({x',x'}={x,x})∧({x',y'}={x,x}))∨(({x,x}={x',x'})∧({x,x}={x',y'}))))
          val pr2_0 = modusPonens(pa2_0.bot.right.head)(pa2_0, pa2_1) //   ((x,y)=(x',y')), (x=y) |- ((({x',x'}={x,x})∧({x',y'}={x,x}))∨(({x,x}={x',x'})∧({x,x}={x',y'})))
          val f = (pairxx === pairxx1) /\ (pairxx === pairxy1)
          destructRightAnd(destructRightOr(pr2_0, f, f), pairxx === pairxy1, pairxx === pairxx1) //   ((x,y)=(x',y')), (x=y) |- {x',y'}={x,x}
        }.steps, IndexedSeq(p0, p1)), IndexedSeq(-1, -2)) //   ((x,y)=(x',y')), (x=y) |- {x',y'}={x,x}
        val p2_1 = SCSubproof({
          val pr2_1_0 = instantiateForall(SCProof(IndexedSeq(), IndexedSeq(p1)), x, x, x1, y1) //   (({x,x}={x',y'})⇒(((y'=x)∧(x'=x))∨((x=y')∧(x=x'))))
          val f = (y1 === x) /\ (x1 === x)
          val pr2_1_1 = destructRightImplies(pr2_1_0, pairxx === pairxy1, f \/ f) //   (({x,x}={x',y'}) |- (((y'=x)∧(x'=x))∨((x=y')∧(x=x'))))
          val pr2_1_2 = destructRightOr(pr2_1_1, f, f)
          pr2_1_2
        }, IndexedSeq(-2)) //   {x',y'}={x,x}, x=y |- x=x' /\ x=y'
        val p2_2 = Cut(emptySeq ++< p2_0.bot ++> p2_1.bot, 0, 1, p2_0.bot.right.head) //   ((x,y)=(x',y')), x=y |- x=x' /\ x=y'
        val p2_3 = RightSubstEq(emptySeq +< (oPair(x, y) === oPair(x1, y1)) +< (x === y) +> ((x === x1) /\ (y === y1)), 2, x, y, (x === x1) /\ (z === y1), z)

        SCSubproof(SCProof(IndexedSeq(p2_0, p2_1, p2_2, p2_3), IndexedSeq(p0, p1)), IndexedSeq(-1, -2))
      } //   ((x,y)=(x',y')), x=y |- x=x' /\ y=y'
      ,
      {
        val pa2_0: SCSubproof = SCSubproof({
          val p2_0_0 = UseFunctionDefinition(emptySeq +> (oPair(x, y) === opairxy), oPair, Seq(x, y)) // |- (x, y) === {{x,y}, {x,x}}
          val p2_0_1 = UseFunctionDefinition(emptySeq +> (oPair(x1, y1) === opairxy1), oPair, Seq(x1, y1)) // |- (x1, y1) === {{x1,y1}, {x1,x1}}
          val p2_0_2 = RightSubstEq(emptySeq +< (oPair(x, y) === oPair(x1, y1)) +> (oPair(x1, y1) === pair(pair(x, y), pair(x, x))),
            0, oPair(x, y), oPair(x1, y1), z === pair(pair(x, y), pair(x, x)), z) //  (x1,y1)=(x,y) |- ((x1,y1)={{x,y},{x,x}})

          val p2_0_3 = RightSubstEq(emptySeq +< (oPair(x, y) === oPair(x1, y1)) +< (opairxy1 === oPair(x1, y1)) +> (pair(pair(x, y), pair(x, x)) === pair(pair(x1, y1), pair(x1, x1))),
            2, opairxy1, oPair(x1, y1), z === pair(pair(x, y), pair(x, x)), z) //  (x1,y1)=(x,y), (x1,y1)={{x1,y1}, {x1,x1}} |- {{x1,y1}, {x1,x1}}={{x,y},{x,x}})

          val p2_0_4 = Cut(emptySeq +< (oPair(x, y) === oPair(x1, y1)) +> (pair(pair(x, y), pair(x, x)) === pair(pair(x1, y1), pair(x1, x1))),
            1, 3, opairxy1 === oPair(x1, y1))
          SCProof(IndexedSeq(p2_0_0, p2_0_1, p2_0_2, p2_0_3, p2_0_4), IndexedSeq(p0))
        }, IndexedSeq(-1)) // ((x,y)=(x',y')) |- ({{x,y},{x,x}}={{x',y'},{x',x'}})
        val pa2_1 = SCSubproof({
          instantiateForall(SCProof(IndexedSeq(), IndexedSeq(p1)), pairxy, pairxx, pairxy1, pairxx1)
        }, IndexedSeq(-2)) //  ({{x,y},{x,x}}={{x',y'},{x',x'}})  => ((({x',x'}={x,y})∧({x',y'}={x,x}))∨(({x,x}={x',x'})∧({x,y}={x',y'})))
        val pr2_0 = SCProof(modusPonens(pa2_0.bot.right.head)(pa2_0, pa2_1).steps, IndexedSeq(p0, p1)) // ((x,y)=(x',y')) |- (({x',x'}={x,y})∧({x',y'}={x,x}))∨(({x,x}={x',x'})∧({x,y}={x',y'}))
        val (f, g) = pr2_0.conclusion.right.head match {
          case BinaryConnectorFormula(`or`, l, r) => (l, r)
        }
        val pr2_1: SCProof = destructRightOr(pr2_0, f, g) // ((x,y)=(x',y')) |- (({x',x'}={x,y})∧({x',y'}={x,x})), (({x,x}={x',x'})∧({x,y}={x',y'}))

        val pb2_0 = SCSubproof({
          val prb2_0_0 = instantiateForall(SCProof(IndexedSeq(), IndexedSeq(p1)), x, y, x1, x1) //  |- (({x,y}={x',x'}) ⇒ (((x'=y)∧(x'=x))∨((x=x')∧(y=x'))))
          val f = (x1 === y) /\ (x1 === x)
          val prb2_0_1 = destructRightImplies(prb2_0_0, pairxy === pairxx1, f \/ f) //  (({x,y}={x',x'}) |- ((x'=y)∧(x'=x))∨((x=x')∧(y=x')))
          val pb3_0_0 = SCSubproof(destructRightOr(prb2_0_1, f, f), IndexedSeq(-1)) //  (({x,y}={x',x'}) |- (x'=y)∧(x'=x)
          val pb3_0_1 = SCSubproof(destructRightAnd(SCProof(IndexedSeq(), IndexedSeq(pb3_0_0)), x1 === y, x1 === x), IndexedSeq(0)) //  (({x,y}={x',x'}) |- x'=y
          val pb3_0_2 = SCSubproof(destructRightAnd(SCProof(IndexedSeq(), IndexedSeq(pb3_0_0)), x1 === x, x1 === y), IndexedSeq(0)) //  (({x,y}={x',x'}) |- x'=x
          val pb3_0_3 = RightSubstEq(emptySeq +< (pairxy === pairxx1) +< (x1 === y) +> (y === x), 2, x1, y, z === x, z) //  (({x,y}={x',x'}), x'=y |- y=x
          val pb3_0_4 = Cut(emptySeq +< (pairxy === pairxx1) +> (y === x), 1, 3, x1 === y) // {x',x'}={x,y} |- x=y
          SCProof(IndexedSeq(pb3_0_0, pb3_0_1, pb3_0_2, pb3_0_3, pb3_0_4), IndexedSeq(p1))
        }, IndexedSeq(-2)) // {x',x'}={x,y} |- x=y
        val pb2_1 = SCSubproof(destructRightAnd(pr2_1, pairxx1 === pairxy, pairxx === pairxy1), IndexedSeq(-1, -2)) // ((x,y)=(x',y')) |- (({x',x'}={x,y}), (({x,x}={x',x'})∧({x,y}={x',y'}))

        val pb2_2 = Cut(pb2_1.bot -> pb2_0.bot.left.head +> (x === y), 1, 0, pb2_0.bot.left.head) // ((x,y)=(x',y')) |- x=y, (({x,x}={x',x'})∧({x,y}={x',y'}))
        val pc2_0 = SCSubproof(SCProof(IndexedSeq(pb2_0, pb2_1, pb2_2), IndexedSeq(p0, p1)), IndexedSeq(-1, -2)) // ((x,y)=(x',y')) |- x=y, (({x,x}={x',x'})∧({x,y}={x',y'}))

        val pc2_1 = SCSubproof({
          val pc2_1_0 = SCSubproof(destructRightAnd(SCProof(IndexedSeq(), IndexedSeq(pc2_0)), pairxy === pairxy1, pairxx === pairxx1), IndexedSeq(-2)) // ((x,y)=(x',y')) |- x=y, {x,y}={x',y'}
          val pc2_1_1 = SCSubproof(instantiateForall(SCProof(IndexedSeq(), IndexedSeq(p1)), x, y, x1, y1), IndexedSeq(-1)) //   (({x,y}={x',y'})⇒(((y'=y)∧(x'=x))∨((x=y')∧(y=x'))))
          val prc2_1_2 = modusPonens(pairxy === pairxy1)(pc2_1_0, pc2_1_1) // ((x,y)=(x',y')) |- x=y, (((y'=y)∧(x'=x))∨((x=y')∧(y=x'))))
          val f = (y1 === y) /\ (x1 === x)
          val g = (y1 === x) /\ (x1 === y)
          val prc2_1_3 = destructRightOr(prc2_1_2, f, g) // ((x,y)=(x',y')) |- x=y, ((y'=x)∧(x'=y)), ((y=y')∧(x=x')))
          val prc2_1_4 = destructRightAnd(prc2_1_3, x1 === y, y1 === x) // ((x,y)=(x',y')) |- x=y, (x'=y), ((y=y')∧(x=x')))
          SCProof(prc2_1_4.steps, IndexedSeq(p1, pc2_0))
        }, IndexedSeq(-2, 0)) // ((x,y)=(x',y')) |- x=y, (x'=y), ((y=y')∧(x=x')))
        val pc2_2 = SCSubproof({
          val pc2_2_0 = SCSubproof(destructRightAnd(SCProof(IndexedSeq(), IndexedSeq(pc2_0)), pairxx === pairxx1, pairxy === pairxy1), IndexedSeq(-2)) // ((x,y)=(x',y')) |- x=y, {x,x}={x',x'}
          val pc2_2_1 = SCSubproof(instantiateForall(SCProof(IndexedSeq(), IndexedSeq(p1)), x, x, x1, x1), IndexedSeq(-1)) //   (({x,x}={x',x'})⇒(((x'=x)∧(x'=x))∨((x=x')∧(x=x'))))
          val prc2_2_2 = modusPonens(pairxx === pairxx1)(pc2_2_0, pc2_2_1) // ((x,y)=(x',y')) |- x=y, (((x'=x)∧(x'=x))∨((x=x')∧(x=x'))))
          val f = (x === x1) /\ (x1 === x)
          val prc2_2_3 = destructRightOr(prc2_2_2, f, f) // ((x,y)=(x',y')) |- x=y, ((x'=x)∧(x'=x))
          val prc2_2_4 = destructRightAnd(prc2_2_3, x === x1, x === x1) // ((x,y)=(x',y')) |- x=y, x'=x
          SCProof(prc2_2_4.steps, IndexedSeq(p1, pc2_0))
        }, IndexedSeq(-2, 0)) // ((x,y)=(x',y')) |- x=y, x'=x

        val pc2_3 = RightSubstEq(pc2_1.bot -> (x1 === y) +> (x === y) +< (x1 === x), 1, x, x1, z === y, z) // ((x,y)=(x',y')), x=x' |- x=y, ((y=y')∧(x=x')))
        val pc2_4 = Cut(pc2_3.bot -< (x === x1), 2, 3, x === x1) // ((x,y)=(x',y')) |- x=y, ((y=y')∧(x=x')))
        val pc2_5 = LeftNot(pc2_4.bot +< !(x === y) -> (x === y), 4, x === y) // ((x,y)=(x',y')), !x=y |-  ((y=y')∧(x=x')))
        SCSubproof(SCProof(IndexedSeq(pc2_0, pc2_1, pc2_2, pc2_3, pc2_4, pc2_5), IndexedSeq(p0, p1)), IndexedSeq(-1, -2))
      } //   ((x,y)=(x',y')), !x=y |- x=x' /\ y=y'
    ).steps, IndexedSeq(p0, p1)), IndexedSeq(0, 1)) //   ((x,y)=(x',y')) |- x=x' /\ y=y'
    SCProof(p0, p1, p2)

    ???
  } // |- (x,y)=(x', y')  ===>  x=x' /\ y=y'
   */
}
