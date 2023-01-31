package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.prooflib.BasicStepTactic.InstFunSchema
import lisa.prooflib.Library
import lisa.prooflib.SimpleDeducedSteps
import lisa.utils.KernelHelpers.<=>
import lisa.utils.Printer

import scala.collection.immutable

object SetTheory extends lisa.Main {

  val x: VariableLabel = variable
  val y: VariableLabel = variable
  val z: VariableLabel = variable
  val h: VariableFormulaLabel = formulaVariable

  val russelParadox = makeTHM("∀'x. elem('x, 'y) ↔ ¬elem('x, 'x) ⊢") {
    have(in(y, y) <=> !in(y, y) |- ()) by Restate
    andThen(forall(x, in(x, y) <=> !in(x, x)) |- ()) by LeftForall(y)
  }
  show

  val unorderedPair_symmetry = makeTHM(() |- forall(y, forall(x, unorderedPair(x, y) === unorderedPair(y, x)))) {

    val objectiveA: Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))
    val objectiveB: Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x))

    val part1 = have(objectiveA) subproof {
      val pr0 = have(() |- in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z)) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), y), y -> LambdaTermTerm(Seq(), x)))(pairAxiom)
      val pr1 = have(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z) |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by
        RightSubstIff(List((in(z, unorderedPair(y, x)), (x === z) \/ (y === z))), LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h))(pairAxiom)
      have(() |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by Cut.withParameters(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z))(pr0, pr1)
      andThen(objectiveA) by RightForall
    }

    val part2 = have(objectiveB) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), unorderedPair(x, y)), y -> LambdaTermTerm(Seq(), unorderedPair(y, x))))(extensionalityAxiom)

    val fin = have(objectiveB.right |- unorderedPair(x, y) === unorderedPair(y, x)) by RightSubstIff(
      List((forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))), unorderedPair(x, y) === unorderedPair(y, x))),
      LambdaFormulaFormula(Seq(h), h)
    )(part1)
    have(() |- unorderedPair(x, y) === unorderedPair(y, x)) by Cut(part2, fin)
    andThen(() |- forall(y, forall(x, unorderedPair(x, y) === unorderedPair(y, x)))) by GeneralizeToForallNoForm(x, y)
  }
  show

  val unorderedPair_deconstruction = makeTHM("⊢ ∀'x. ∀'y. ∀ 'x1. ∀ 'y1. unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⇒ 'y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1") {
    val x1 = variable
    val y1 = variable
    val g = variable
    val pxy = unorderedPair(x, y)
    val pxy1 = unorderedPair(x1, y1)
    val p0 = have(emptySeq +< (unorderedPair(x, y) === unorderedPair(x1, y1)) +> (((z === x) \/ (z === y)) <=> ((z === x1) \/ (z === y1)))) subproof {
      val p2 = have(() |- in(z, unorderedPair(x1, y1)) <=> (x1 === z) \/ (y1 === z)) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), x1), y -> LambdaTermTerm(Seq(), y1)))(pairAxiom)
      val p3 = have((pxy === pxy1) |- (in(z, unorderedPair(x1, y1)) <=> (x === z) \/ (y === z))) by RightSubstEq(List((pxy, pxy1)), LambdaTermFormula(Seq(g), in(z, g) <=> ((x === z) \/ (y === z))))(
        pairAxiom
      )
      val p4 = andThen(emptySeq +< p3.bot.left.head +< p2.bot.right.head +> (((z === x) \/ (z === y)) <=> ((z === x1) \/ (z === y1)))) by RightSubstIff(
        List(((z === x1) \/ (z === y1), in(z, pxy1))),
        LambdaFormulaFormula(Seq(h), h <=> ((z === x) \/ (z === y)))
      )
      have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ 'z = 'x ∨ 'z = 'y ⇔ 'z = 'x1 ∨ 'z = 'y1") by Cut(p2, p4)
    }
    val aaa = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1 ⊢ 'y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1") subproof {
      val pc0 = have("('x = 'x1); (unorderedPair('x, 'y) = unorderedPair('x1, 'y1)) |- ('y1='y)") by ByCase(y === x)(
        have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'y ⊢ 'y1 = 'y") subproof {
          val f1 = z === x
          val pa0_0 = have(emptySeq +> ((f1 \/ f1) <=> f1)) by Trivial
          have(emptySeq +< (pxy === pxy1) +< (x === y) +> ((f1 \/ f1) <=> (z === x1) \/ (z === y1))) by RightSubstEq(
            List((x, y)),
            LambdaTermFormula(Seq(g), (f1 \/ (z === g)) <=> ((z === x1) \/ (z === y1)))
          )(p0) //  ({x,y}={x',y'}) y=x|- (z=x)\/(z=x) <=> (z=x' \/ z=y')
          val pa0_2 = andThen(emptySeq +< (pxy === pxy1) +< (x === y) +< (f1 <=> (f1 \/ f1)) +> (f1 <=> ((z === x1) \/ (z === y1)))) by RightSubstIff(
            List((f1, f1 \/ f1)),
            LambdaFormulaFormula(Seq(h), h <=> ((z === x1) \/ (z === y1)))
          )
          have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'y ⊢ 'z = 'x ⇔ 'z = 'x1 ∨ 'z = 'y1") by Cut.withParameters(f1 <=> (f1 \/ f1))(pa0_0, pa0_2)
          val pa0 = andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'y ⊢ 'y1 = 'x ⇔ 'y1 = 'x1 ∨ 'y1 = 'y1") by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), y1)))

          have(emptySeq +> (y1 === y1)) by RightRefl
          andThen(emptySeq +> ((y1 === y1) \/ (y1 === x1))) by RightOr
          val fin = andThen(emptySeq +< pa0.bot.right.last +> (y1 === x)) by RightSubstIff(
            List(((y1 === x), ((y1 === y1) \/ (y1 === x1)))),
            LambdaFormulaFormula(Seq(h), h)
          )
          have("(unorderedPair('x, 'y) = unorderedPair('x1, 'y1)) ; 'y = 'x |- ('y1= 'x)") by Cut(pa0, fin)
          andThen(emptySeq ++< pa0.bot +> (y1 === y)) by RightSubstEq(List((x, y)), LambdaTermFormula(Seq(g), y1 === g))

        } //  (x=y), ({x,y}={x',y'}) |- (y'=y)
        ,
        have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1; ¬('y = 'x) ⊢ 'y = 'y1") subproof {
          val pb0_0 =
            have(emptySeq +< (pxy === pxy1) +> (((y === x) \/ (y === y)) <=> ((y === x1) \/ (y === y1)))) by InstFunSchema(Map[SchematicTermLabel, LambdaTermTerm](z -> LambdaTermTerm(Seq(), y)))(p0)
          have(emptySeq +> (y === y)) by RightRefl
          val pb0_1 = andThen(emptySeq +> ((y === y) \/ (y === x))) by RightOr
          val tocut = andThen(emptySeq +< pb0_0.bot.right.last +> ((y === x1) \/ (y === y1))) by RightSubstIff(
            List((((y === x1) \/ (y === y1)), ((y === x) \/ (y === y)))),
            LambdaFormulaFormula(Seq(h), h)
          )
          have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ 'y = 'x1 ∨ 'y = 'y1") by Cut(pb0_0, tocut) //  ({x,y}={x',y'}) |- (y=x')∨(y=y')
          andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1 ⊢ 'y = 'x ∨ 'y = 'y1") by RightSubstEq(List((x, x1)), LambdaTermFormula(Seq(g), (y === g) \/ (y === y1)))
          val rb1 = andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1; ('y = 'x) ⊢ 'y = 'y1") by destructRightOr(y === x, y === y1)
          andThen(rb1.bot +< !(y === x) -> (y === x)) by LeftNot //  (x=x'), ({x,y}={x',y'}), ¬(y=x) |- (y=y')
        }
      ) //
      val pc1 = have(emptySeq +> (x === x)) by RightRefl
      val pc2 = have(emptySeq ++< pc0.bot +> ((y1 === y) /\ (x === x))) by RightAnd(pc0, pc1) // ({x,y}={x',y'}), x=x' |- (x=x /\ y=y')
      val pc3 = andThen(emptySeq ++< pc2.bot +> ((y1 === y) /\ (x1 === x))) by RightSubstEq(List((x, x1)), LambdaTermFormula(Seq(g), (y1 === y) /\ (g === x)))
      andThen(emptySeq ++< pc3.bot +> (pc3.bot.right.head \/ ((x === y1) /\ (y === x1)))) by RightOr
    }
    val bbb = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); ¬('x = 'x1) ⊢ 'x = 'y1 ∧ 'y = 'x1 ∨ 'x = 'x1 ∧ 'y = 'y1") subproof {
      val pd0 = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1);  ('y='x1)") subproof {
        val ex1x1 = x1 === x1

        have(emptySeq +> (ex1x1)) by RightRefl
        val pd0_0 = andThen(emptySeq +> (ex1x1 \/ (x1 === y1))) by RightOr
        val pd0_1 = have(emptySeq +< (pxy === pxy1) +> (((x1 === x) \/ (x1 === y)) <=> ((x1 === x1) \/ (x1 === y1)))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), x1)))(p0)
        val pd0_2 = have(pd0_1.bot.right |- ((x1 === x) \/ (x1 === y))) by RightSubstIff(List(((x1 === x) \/ (x1 === y), (x1 === x1) \/ (x1 === y1))), LambdaFormulaFormula(Seq(h), h))(pd0_0)
        have(pd0_1.bot.left |- pd0_2.bot.right) by Cut(pd0_1, pd0_2) //  ({x,y}={x',y'}) |- (x=x' \/ y=x')
        andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1);  ('y='x1)") by destructRightOr(x === x1, y === x1) //  ({x,y}={x',y'}) |- x=x',  y=x'
      } //  ({x,y}={x',y'}) |- x=x',  y=x' --

      val pd1 = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1);  ('x='y1)") subproof {

        val exx = x === x

        val pd1_1 = have(emptySeq +< (pxy === pxy1) +> (((x === x) \/ (x === y)) <=> ((x === x1) \/ (x === y1)))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), x)))(p0)
        have(emptySeq +> exx) by RightRefl
        val pd1_0 = andThen(emptySeq +> (exx \/ (x === y))) by RightOr
        val tocut = andThen(emptySeq +< pd1_1.bot.right.last +> ((x === x1) \/ (x === y1))) by RightSubstIff(
          List((((x === x) \/ (x === y)), ((x === x1) \/ (x === y1)))),
          LambdaFormulaFormula(Seq(h), h)
        )
        have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1) ∨ ('x='y1)") by Cut(pd1_1, tocut)
        andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1); ('x='y1)") by destructRightOr(x === x1, x === y1) //  ({x,y}={x',y'}) |- x=x',  x=y'
      }
      val pd2 = have(emptySeq ++< pd1.bot +> (x === x1) +> ((x === y1) /\ (y === x1))) by RightAnd(pd0, pd1) //  ({x,y}={x',y'})  |- x=x', (x=y' /\ y=x') ---
      val pd3 = andThen(emptySeq ++< pd2.bot +< !(x === x1) +> ((x === y1) /\ (y === x1))) by LeftNot //  ({x,y}={x',y'}), !x===x1 |- (x=y' /\ y=x')
      andThen(emptySeq ++< pd3.bot +> (pd3.bot.right.head \/ ((x === x1) /\ (y === y1)))) by Trivial
    }
    val p1 = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1)") by ByCase(x === x1)(aaa, bbb) //  ({x,y}={x',y'}) |- (x=x' /\ y=y')\/(x=y' /\ y=x')
    andThen(emptySeq +> (p1.bot.left.head ==> p1.bot.right.head)) by RightImplies //   |- ({x,y}={x',y'}) ==> (x=x' /\ y=y')\/(x=y' /\ y=x')
    andThen("⊢ ∀'x. ∀'y. ∀ 'x1. ∀ 'y1. unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⇒ 'y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1") by GeneralizeToForallNoForm(x, y, x1, y1)
  }
  show

  val noUniversalSet = makeTHM("∀'x. elem('x, 'z) ⊢ ") {

    val P: SchematicPredicateLabel = predicate(2)
    have(in(x, y) <=> (in(x, z) /\ !in(x, x)) |- in(x, y) <=> (in(x, z) /\ !in(x, x))) by Hypothesis // in(x,y) <=> (in(x,z) /\ in(x, x)) |- in(x,y) <=> (in(x,z) /\ in(x, x))
    andThen((in(x, z) <=> True, in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> (True /\ !in(x, x))) by RightSubstIff(
      List((in(x, z), And())),
      LambdaFormulaFormula(Seq(h), in(x, y) <=> (h /\ !in(x, x)))
    ) // in(x1,y1) <=> (in(x1,z1) /\ in(x1, x1)) |- in(x,y) <=> (True /\ in(x1, x1))
    andThen((in(x, z), in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> !in(x, x)) by Rewrite
    andThen((forall(x, in(x, z)), in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> !in(x, x)) by LeftForall(x)
    andThen((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- in(x, y) <=> !in(x, x)) by LeftForall(x)
    val s6 = andThen((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- forall(x, in(x, y) <=> !in(x, x))) by RightForall
    val s7 = have(forall(x, in(x, y) <=> !in(x, x)) |- ()) by InstFunSchema(Map(y -> LambdaTermTerm(Nil, y)))(thm"russelParadox")
    have((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- ()) by Cut(s6, s7)
    val s9 = andThen((forall(x, in(x, z)), exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))) |- ()) by LeftExists
    val s10 = have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))) by InstPredSchema(Map(P -> LambdaTermFormula(Seq(x, z), !in(x, x))))(comprehensionSchema)

    have(forall(x, in(x, z)) |- ()) by Cut(s10, s9)
  }
  show

}
