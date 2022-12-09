package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.utils.Helpers.<=>
import lisa.utils.Library
import lisa.utils.Printer
import lisa.utils.tactics.BasicStepTactic.InstFunSchema
import lisa.utils.tactics.SimpleDeducedSteps
object ProofTest extends lisa.Main {


  val x: VariableLabel = variable
  val y: VariableLabel = variable
  val z: VariableLabel = variable
  val h: VariableFormulaLabel = formulaVariable

  val russelParadox =  makeTHM("∀'x. elem('x, 'y) ↔ ¬elem('x, 'x) ⊢") {
    have(in(y, y) <=> !in(y, y) |- ()) by Restate
    andThen(forall(x, in(x, y) <=> !in(x, x)) |- ()) by LeftForall.withParameters(in(x, y) <=> !in(x, x), x, y)
  }
  show

  val unorderedPair_symmetry = makeTHM(() |- forall(y, forall(x, unorderedPair(x, y) === unorderedPair(y, x)))) {

      val objectiveA : Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))
      val objectiveB : Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x))

      val part1 = have(objectiveA) subproof {
          val pr0 = have(() |- in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z)) by InstFunSchema(Map(
            x -> LambdaTermTerm(Seq(), y),
            y -> LambdaTermTerm(Seq(), x)))(ax"pairAxiom")
          val pr1 = have(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z) |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by
            RightSubstIff(List((in(z, unorderedPair(y, x)), (x === z) \/ (y === z))),
              LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h))(ax"pairAxiom")
          have(() |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by Cut.withParameters(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z))(pr0, pr1)
          andThen(objectiveA) by RightForall.withParameters(in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)), z)
      }

    val part2 = have(objectiveB) by InstFunSchema(Map(
      x -> LambdaTermTerm(Seq(), unorderedPair(x, y)),
      y -> LambdaTermTerm(Seq(), unorderedPair(y, x))))(ax"extensionalityAxiom")

      have(() |- unorderedPair(x, y) === unorderedPair(y, x)) by ByEquiv(objectiveB.right.head, objectiveA.right.head)(part1, part2)
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
      val p2 = have(() |- in(z, unorderedPair(x1, y1)) <=> (x1 === z) \/ (y1 === z)) by InstFunSchema(Map(
        x -> LambdaTermTerm(Seq(), x1),
        y -> LambdaTermTerm(Seq(), y1)))(ax"pairAxiom")
      val p3 = have((pxy === pxy1) |- (in(z, unorderedPair(x1, y1)) <=> (x === z) \/ (y === z))) by RightSubstEq(List((pxy, pxy1)), LambdaTermFormula(Seq(g), in(z, g) <=> ((x === z) \/ (y === z))))(ax"pairAxiom")
      val p4 = andThen(emptySeq +< p3.bot.left.head +< p2.bot.right.head +> (((z === x) \/ (z === y)) <=> ((z === x1) \/ (z === y1)))) by RightSubstIff(List(((z === x1) \/ (z === y1), in(z, pxy1))),
        LambdaFormulaFormula(Seq(h), h <=> ((z === x) \/ (z === y))))
      have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ 'z = 'x ∨ 'z = 'y ⇔ 'z = 'x1 ∨ 'z = 'y1") by Cut.withParameters(p2.bot.right.head)(p2, p4)
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
          val pa0_2 = andThen(emptySeq +< (pxy === pxy1) +< (x === y) +< (f1 <=> (f1 \/ f1)) +> (f1 <=> ((z === x1) \/ (z === y1))))  by RightSubstIff(
            List((f1, f1 \/ f1)),
            LambdaFormulaFormula(Seq(h), h <=> ((z === x1) \/ (z === y1)))
          )
          have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'y ⊢ 'z = 'x ⇔ 'z = 'x1 ∨ 'z = 'y1") by Cut.withParameters(f1 <=> (f1 \/ f1))(pa0_0, pa0_2)
          val pa0 = andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'y ⊢ 'y1 = 'x ⇔ 'y1 = 'x1 ∨ 'y1 = 'y1") by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), y1)))

          have(emptySeq +> (y1 === y1)) by RightRefl.withParameters(y1 === y1)
          val pa1 = andThen(emptySeq +> ((y1 === y1) \/ (y1 === x1))) by RightOr.withParameters(y1 === y1, y1 === x1)
          have("(unorderedPair('x, 'y) = unorderedPair('x1, 'y1)) ; 'y = 'x |- ('y1= 'x)") by ByEquiv(pa0.bot.right.head, pa1.bot.right.head)(pa1, pa0) // ({x,y}={x',y'}) y=x|- ((y'=x)
          andThen(emptySeq ++< pa0.bot +> (y1 === y)) by RightSubstEq(List((x, y)), LambdaTermFormula(Seq(g), y1 === g))

        } //  (x=y), ({x,y}={x',y'}) |- (y'=y)
        ,
        have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1; ¬('y = 'x) ⊢ 'y = 'y1") subproof {
          val pb0_0 = have(emptySeq +< (pxy === pxy1) +> (((y === x) \/ (y === y)) <=> ((y === x1) \/ (y === y1)))) by InstFunSchema(Map[SchematicTermLabel, LambdaTermTerm](
            z -> LambdaTermTerm(Seq(), y)))(p0)
          have(emptySeq +> (y === y)) by RightRefl.withParameters(y === y)
          val pb0_1 = andThen(emptySeq +> ((y === y) \/ (y === x))) by RightOr.withParameters(y === y, y === x)
          have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ 'y = 'x1 ∨ 'y = 'y1") by ByEquiv(pb0_0.bot.right.head, pb0_1.bot.right.head)(pb0_1, pb0_0) //  ({x,y}={x',y'}) |- (y=x')∨(y=y')
          andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1 ⊢ 'y = 'x ∨ 'y = 'y1") by RightSubstEq(List((x, x1)), LambdaTermFormula(Seq(g), (y === g) \/ (y === y1)))
          val rb1 = andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1; ('y = 'x) ⊢ 'y = 'y1") by destructRightOr(y === x, y === y1)
          andThen(rb1.bot +< !(y === x) -> (y === x)) by LeftNot.withParameters(y === x) //  (x=x'), ({x,y}={x',y'}), ¬(y=x) |- (y=y')
        }
      ) //
      val pc1 = have(emptySeq +> (x === x)) by RightRefl.withParameters(x === x)
      val pc2 = have(emptySeq ++< pc0.bot +> ((y1 === y) /\ (x === x))) by RightAnd(Seq(pc0, pc1)) // ({x,y}={x',y'}), x=x' |- (x=x /\ y=y')
      val pc3 = andThen(emptySeq ++< pc2.bot +> ((y1 === y) /\ (x1 === x))) by RightSubstEq(List((x, x1)), LambdaTermFormula(Seq(g), (y1 === y) /\ (g === x)))
      andThen(emptySeq ++< pc3.bot +> (pc3.bot.right.head \/ ((x === y1) /\ (y === x1)))) by RightOr.withParameters(pc3.bot.right.head, (x === y1) /\ (y === x1))
    }
    val bbb = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); ¬('x = 'x1) ⊢ 'x = 'y1 ∧ 'y = 'x1 ∨ 'x = 'x1 ∧ 'y = 'y1") subproof {
      val pd0 = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1);  ('y='x1)") subproof {
        val ex1x1 = x1 === x1

        have(emptySeq +> (ex1x1)) by RightRefl.withParameters(ex1x1)
        val pd0_0 = andThen(emptySeq +> (ex1x1 \/ (x1 === y1))) by RightOr.withParameters(ex1x1, x1 === y1)
        val pd0_1 = have(emptySeq +< (pxy === pxy1) +> (((x1 === x) \/ (x1 === y)) <=> ((x1 === x1) \/ (x1 === y1)))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), x1)))(p0)
        val pd0_2 = have(pd0_1.bot.right |- ((x1 === x) \/ (x1 === y))) by RightSubstIff(List(((x1 === x) \/ (x1 === y), (x1 === x1) \/ (x1 === y1))), LambdaFormulaFormula(Seq(h), h))(pd0_0)
        have(pd0_1.bot.left |- pd0_2.bot.right) by Cut.withParameters(pd0_1.bot.right.head)(pd0_1, pd0_2) //  ({x,y}={x',y'}) |- (x=x' \/ y=x')
        andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1);  ('y='x1)") by destructRightOr(x === x1, y === x1) //  ({x,y}={x',y'}) |- x=x',  y=x'
      } //  ({x,y}={x',y'}) |- x=x',  y=x' --

      val pd1 = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1);  ('x='y1)") subproof {

        val exx = x === x

        have(emptySeq +> exx) by RightRefl.withParameters(exx)
        val pd1_0 = andThen(emptySeq +> (exx \/ (x === y))) by RightOr.withParameters(exx, x === y)
        val pd1_1 = have(emptySeq +< (pxy === pxy1) +> (((x === x) \/ (x === y)) <=> ((x === x1) \/ (x === y1)))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), x)))(p0)
        have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1) ∨ ('x='y1)") by ByEquiv(pd1_1.bot.right.head, pd1_0.bot.right.head)(pd1_0, pd1_1)
        andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('x='x1); ('x='y1)") by destructRightOr(x === x1, x === y1) //  ({x,y}={x',y'}) |- x=x',  x=y'
      }
      val pd2 = have(emptySeq ++< pd1.bot +> (x === x1) +> ((x === y1) /\ (y === x1))) by RightAnd.withParameters(Seq(x === y1, y === x1))(Seq(pd0, pd1)) //  ({x,y}={x',y'})  |- x=x', (x=y' /\ y=x') ---
      val pd3 = andThen(emptySeq ++< pd2.bot +< !(x === x1) +> ((x === y1) /\ (y === x1))) by LeftNot.withParameters(x === x1) //  ({x,y}={x',y'}), !x===x1 |- (x=y' /\ y=x')
      andThen(emptySeq ++< pd3.bot +> (pd3.bot.right.head \/ ((x === x1) /\ (y === y1)))) by Trivial
    }

    val p1 = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1)") by ByCase(x === x1)(aaa, bbb)//  ({x,y}={x',y'}) |- (x=x' /\ y=y')\/(x=y' /\ y=x')
    andThen(emptySeq +> (p1.bot.left.head ==> p1.bot.right.head)) by RightImplies.withParameters(p1.bot.left.head, p1.bot.right.head) //   |- ({x,y}={x',y'}) ==> (x=x' /\ y=y')\/(x=y' /\ y=x')
    andThen("⊢ ∀'x. ∀'y. ∀ 'x1. ∀ 'y1. unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⇒ 'y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1") by GeneralizeToForallNoForm(x, y, x1, y1)
  }
  show

  val noUniversalSet = makeTHM("∀'x. elem('x, 'z) ⊢ ") {

    val P: SchematicPredicateLabel  = predicate(2)
    // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,y) /\ sPhi(x,z)))))
    // forall(x1, in(x1,y) <=> !in(x1, x1)) |- ()
    have(in(x, y) <=> (in(x, z) /\ !in(x, x)) |- in(x, y) <=> (in(x, z) /\ !in(x, x))) by Hypothesis// in(x,y) <=> (in(x,z) /\ in(x, x)) |- in(x,y) <=> (in(x,z) /\ in(x, x))
    andThen((in(x, z) <=> True, in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> (True /\ !in(x, x))) by RightSubstIff(
      List((in(x, z), And())),
      LambdaFormulaFormula(Seq(h), in(x, y) <=> (h /\ !in(x, x)))
    ) // in(x1,y1) <=> (in(x1,z1) /\ in(x1, x1)) |- in(x,y) <=> (True /\ in(x1, x1))
    andThen((in(x, z), in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> !in(x, x)) by Restate
    andThen((forall(x, in(x, z)), in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> !in(x, x)) by LeftForall.withParameters(in(x, z), x, x)
    andThen((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- in(x, y) <=> !in(x, x)) by LeftForall.withParameters(in(x, y) <=> (in(x, z) /\ !in(x, x)), x, x)
    val s6 = andThen((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- forall(x, in(x, y) <=> !in(x, x))) by RightForall.withParameters(in(x, y) <=> !in(x, x), x)
    val s7 = have(forall(x, in(x, y) <=> !in(x, x)) |- ()) by InstFunSchema(Map(y -> LambdaTermTerm(Nil, y)))( thm"russelParadox")
    have((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- ()) by Cut.withParameters(forall(x, in(x, y) <=> !in(x, x)))(s6, s7)
    val s9 = andThen((forall(x, in(x, z)), exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))) |- ()) by LeftExists.withParameters(forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))), y)
    val s10 = have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))) by InstPredSchema(Map(P -> LambdaTermFormula(Seq(x, z), !in(x, x))))(ax"comprehensionSchema")

    have(forall(x, in(x, z)) |- ()) by Cut.withParameters(exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))))(s10, s9)
  }
  show


  val functionalMapping = makeTHM("∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'phi('x, 'a)) ⊢ ∃! 'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'a. elem('a, 'A) ∧ 'phi('x, 'a))") {
    val a: VariableLabel = variable
    val f = variable
    val A = variable
    val X = variable
    val B = variable
    val B1 = variable
    val phi: SchematicPredicateLabel = predicate(2)
    val P: SchematicPredicateLabel = predicate(2)
    val P2: SchematicPredicateLabel = predicate(3)

    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> H)

    //  final val comprehensionSchema: Formula = exists(y, forall(x, in(x, y) <=> (in(x, z) /\ sPhi(x, z))))
    have((H) |- in(a, A) ==> existsOne(x, phi(x, a))) by Trivial
    val s3 = have(H1 |- H1) by Hypothesis
    val p0 = have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ phi(x, z))))) by InstPredSchema(
      Map(P -> LambdaTermFormula(Seq(x, z), phi(x, z))))(ax"comprehensionSchema")
    val s4 = andThen(() |- exists(y, forall(x, in(x, y) <=> (in(x, A) /\ phi(x, A))))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), A)))
    val s5 = andThen(H1 |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x)))))) by Trivial
    val s6 = have((H1) |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ phi(y, x))))) by Cut.withParameters(H1)(s3, s5) // ⊢ ∃B. ∀x. (x ∈ A) ⇒ ∃y. (y ∈ B) ∧ (y = (x, b))
    val q0 = have(() |-  exists(y, forall(x, in(x, y) <=> (in(x, z) /\ exists(a, in(a, A) /\ phi(x, a)))))) by InstPredSchema(
      Map(P -> LambdaTermFormula(Seq(x, z), exists(a, in(a, A) /\ phi(x, a))))
    )(ax"comprehensionSchema")
    val s7 = andThen(() |- exists(y, forall(x, in(x, y) <=> (in(x, A) /\ exists(a, in(a, A) /\ phi(x, a)))))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), A)))

    val s8 = have(Set(forall(a, in(a, A) ==> existsOne(x, phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)) subproof {
      val y1 = variable
      have(in(y1, B) |- in(y1, B)) by Hypothesis
      andThen((in(y1, B), x === y1) |- in(x, B)) by RightSubstEq(List((x, y1)), LambdaTermFormula(Seq(f), in(f, B)))
      andThen(Set(in(y1, B), (x === y1) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftSubstIff(List(((x === y1), phi(x, a))), LambdaFormulaFormula(Seq(h), h()))
      andThen(Set(y === y1, in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftSubstEq(List((y, y1)), LambdaTermFormula(Seq(f), (x === f) <=> phi(x, a)))
      andThen(Set((y === y1) <=> phi(y1, a), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftSubstIff(List((phi(y1, a), y1 === y)), LambdaFormulaFormula(Seq(h), h()))
      andThen(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftForall.withParameters((y === x) <=> phi(x, a), x, y1)
      andThen(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B)) by LeftForall.withParameters((x === y) <=> phi(x, a), x, x)
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B)) by LeftExists.withParameters(forall(x, (y === x) <=> phi(x, a)), y)
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a) /\ in(y1, B), phi(x, a)) |- in(x, B)) by Restate
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), exists(y1, phi(y1, a) /\ in(y1, B)), phi(x, a)) |- in(x, B)) by LeftExists.withParameters(phi(y1, a) /\ in(y1, B), y1)
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), True ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a)) |- in(x, B)) by Restate
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a), in(a, A)) |- in(x, B)) by LeftSubstIff(
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, phi(y, a) /\ in(y, B))))
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftForall.withParameters(
        in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)), a, a)
      andThen(Set(in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftSubstIff(
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, forall(x, (y === x) <=> phi(x, a)))))
      andThen(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftForall.withParameters(
        in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), a, a)

      andThen(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a) /\ in(a, A)) |- in(x, B)) by Restate
      andThen(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)) by LeftExists.withParameters(
        phi(x, a) /\ in(a, A), a)
      andThen(Set(forall(a, in(a, A) ==> existsOne(x, phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)) by Restate
    }


  }
  /*
   THEOREM("functionalMapping") of
  "∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'phi('x, 'a)) ⊢ ∃! 'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'a. elem('a, 'A) ∧ 'phi('x, 'a))" PROOF2 {
    val a = VariableLabel("a")
    val x = VariableLabel("x")
    val y = VariableLabel("y")
    val z = VariableLabel("z")
    val f = VariableLabel("f")
    val h = VariableFormulaLabel("h")
    val A = VariableLabel("A")
    val X = VariableLabel("X")
    val B = VariableLabel("B")
    val B1 = VariableLabel("B1")
    val phi = SchematicPredicateLabel("phi", 2)
    val sPhi = SchematicPredicateLabel("P", 2)
    val sPsi = SchematicPredicateLabel("P", 3)

    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> H)

    val s2 = SC.Rewrite((H) |- in(a, A) ==> existsOne(x, phi(x, a)), 1)
    val s3 = hypothesis(H1)
    val i1 = () |- replacementSchema
    val p0 = SC.InstPredSchema(
      () |- instantiatePredicateSchemas(replacementSchema, Map(sPsi -> LambdaTermFormula(Seq(y, a, x), phi(x, a)))),
      -1,
      Map(sPsi -> LambdaTermFormula(Seq(y, a, x), phi(x, a)))
    )
    val p1 = instantiateForall(SCProof(steps(p0), imports(i1)), A)
    val s4 = SC.SCSubproof(p1, Seq(-1)) //
    val s5 = SC.Rewrite(s3.bot.right.head |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 4)
    val s6 = SC.Cut((H1) |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 3, 5, s3.bot.right.head) // ⊢ ∃B. ∀x. (x ∈ A) ⇒ ∃y. (y ∈ B) ∧ (y = (x, b))

    val i2 = () |- comprehensionSchema // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,z) /\ sPhi(x,z)))))
    val q0 = SC.InstPredSchema(
      () |- instantiatePredicateSchemas(comprehensionSchema, Map(sPhi -> LambdaTermFormula(Seq(x, z), exists(a, in(a, A) /\ phi(x, a))))),
      -1,
      Map(sPhi -> LambdaTermFormula(Seq(x, z), exists(a, in(a, A) /\ phi(x, a))))
    )
    val q1 = instantiateForall(SCProof(steps(q0), imports(i2)), B)
    val s7 = SC.SCSubproof(q1, Seq(-2)) // ∃y. ∀x. (x ∈ y) ↔ (x ∈ B) ∧ ∃a. a ∈ A /\ x = (a, b)      := exists(y, F(y) )
    SCProof(steps(s0, s1, s2, s3, s4, s5, s6, s7), imports(i1, i2))
    val s8 = SC.SCSubproof({
      val y1 = VariableLabel("y1")
      val s0 = hypothesis(in(y1, B))
      val s1 = SC.RightSubstEq((in(y1, B), x === y1) |- in(x, B), 0, List((x, y1)), LambdaTermFormula(Seq(f), in(f, B)))
      val s2 = SC.LeftSubstIff(Set(in(y1, B), (x === y1) <=> phi(x, a), phi(x, a)) |- in(x, B), 1, List(((x === y1), phi(x, a))), LambdaFormulaFormula(Seq(h), h()))
      val s3 = SC.LeftSubstEq(Set(y === y1, in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B), 2, List((y, y1)), LambdaTermFormula(Seq(f), (x === f) <=> phi(x, a)))
      val s4 =
        SC.LeftSubstIff(Set((y === y1) <=> phi(y1, a), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B), 3, List((phi(y1, a), y1 === y)), LambdaFormulaFormula(Seq(h), h()))
      val s5 = SC.LeftForall(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B), 4, (y === x) <=> phi(x, a), x, y1)
      val s6 = SC.LeftForall(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B), 5, (x === y) <=> phi(x, a), x, x)
      val s7 = SC.LeftExists(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B), 6, forall(x, (y === x) <=> phi(x, a)), y)
      val s8 = SC.Rewrite(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a) /\ in(y1, B), phi(x, a)) |- in(x, B), 7)
      val s9 = SC.LeftExists(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), exists(y1, phi(y1, a) /\ in(y1, B)), phi(x, a)) |- in(x, B), 8, phi(y1, a) /\ in(y1, B), y1)
      val s10 = SC.Rewrite(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), True ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a)) |- in(x, B), 9)
      val s11 = SC.LeftSubstIff(
        Set(exists(y, forall(x, (y === x) <=> phi(x, a))), in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a), in(a, A)) |- in(x, B),
        10,
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, phi(y, a) /\ in(y, B)))
      )
      val s12 = SC.LeftForall(
        Set(exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B),
        11,
        in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)),
        a,
        a
      )
      val s13 = SC.LeftSubstIff(
        Set(in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B),
        12,
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, forall(x, (y === x) <=> phi(x, a))))
      )
      val s14 = SC.LeftForall(
        Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B),
        13,
        in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))),
        a,
        a
      )
      val s15 =
        SC.Rewrite(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a) /\ in(a, A)) |- in(x, B), 14)
      val s16 = SC.LeftExists(
        Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B),
        15,
        phi(x, a) /\ in(a, A),
        a
      )
      val truc = forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)))
      val s17 = SC.Rewrite(Set(forall(a, in(a, A) ==> existsOne(x, phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B), 16)
      SCProof(steps(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17))
    }) // H, ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ phi(y, a), ∃a. a ∈ A ∧ phi(x, a) |- (x ∈ B)

    val G = forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a))))
    val F = forall(x, iff(in(x, B1), in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))))
    val s9 = SC.SCSubproof({
      val p0 = instantiateForall(SCProof(hypothesis(F)), x)
      val left = in(x, B1)
      val right = in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))
      val p1 = p0.withNewSteps(Vector(SC.Rewrite(F |- (left ==> right) /\ (right ==> left), p0.length - 1)))
      val p2 = destructRightAnd(p1, (right ==> left), (left ==> right)) // F |- in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a))) => in(x, B1)
      val p3 = p2.withNewSteps(Vector(SC.Rewrite(Set(F, in(x, B), exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1), p2.length - 1)))
      p3
    }) // have F, (x ∈ B),  ∃a. a ∈ A ∧ x = (a, b) |- (x ∈ B1)
    val s10 = SC.Cut(Set(F, G, H1, exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1), 8, 9, in(x, B)) // redGoal F, ∃a. a ∈ A ∧ x = (a, b), ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ y = (a, b) |- (x ∈ B1)
    val s11 = SC.Rewrite(Set(H1, G, F) |- exists(a, in(a, A) /\ (phi(x, a))) ==> in(x, B1), 10) // F |- ∃a. a ∈ A ∧ x = (a, b) => (x ∈ B1)   --- half
    val s12 = SC.SCSubproof({
      val p0 = instantiateForall(SCProof(hypothesis(F)), x)
      val left = in(x, B1)
      val right = in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))
      val p1 = p0.withNewSteps(Vector(SC.Rewrite(F |- (left ==> right) /\ (right ==> left), p0.length - 1)))
      val p2 = destructRightAnd(p1, (left ==> right), (right ==> left)) // F |- in(x, B1) => in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a))) =>
      val p3 = p2.withNewSteps(Vector(SC.Rewrite(Set(F, in(x, B1)) |- exists(a, in(a, A) /\ (phi(x, a))) /\ in(x, B), p2.length - 1)))
      val p4 = destructRightAnd(p3, exists(a, in(a, A) /\ (phi(x, a))), in(x, B))
      val p5 = p4.withNewSteps(Vector(SC.Rewrite(F |- in(x, B1) ==> exists(a, in(a, A) /\ (phi(x, a))), p4.length - 1)))
      p5
    }) // have F |- (x ∈ B1) ⇒ ∃a. a ∈ A ∧ x = (a, b)    --- other half
    val s13 = SC.RightIff((H1, G, F) |- in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))), 11, 12, in(x, B1), exists(a, in(a, A) /\ (phi(x, a)))) // have F |- (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
    val s14 =
      SC.RightForall(
        (H1, G, F) |- forall(x, in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a)))),
        13,
        in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))),
        x
      ) // G, F |- ∀x. (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)

    val i3 = () |- extensionalityAxiom
    val s15 = SC.SCSubproof(
      {
        val i1 = s13.bot // G, F |- (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
        val i2 = () |- extensionalityAxiom
        val t0 = SC.RightSubstIff(
          Set(H1, G, F, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, X) <=> in(x, B1),
          -1,
          List((in(x, X), exists(a, in(a, A) /\ (phi(x, a))))),
          LambdaFormulaFormula(Seq(h), h() <=> in(x, B1))
        ) // redGoal2  F, (z ∈ X) <=> ∃a. a ∈ A ∧ z = (a, b) |- (z ∈ X) <=> (z ∈ B1)
        val t1 = SC.LeftForall(
          Set(H1, G, F, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) |- in(x, X) <=> in(x, B1),
          0,
          in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))),
          x,
          x
        ) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- (z ∈ X) <=> (z ∈ B1)
        val t2 = SC.RightForall(t1.bot.left |- forall(x, in(x, X) <=> in(x, B1)), 1, in(x, X) <=> in(x, B1), x) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- ∀z. (z ∈ X) <=> (z ∈ B1)
        val t3 =
          SC.SCSubproof(
            instantiateForall(SCProof(steps(SC.Rewrite(() |- extensionalityAxiom, -1)), imports(() |- extensionalityAxiom)), X, B1),
            Vector(-2)
          ) // (∀z. (z ∈ X) <=> (z ∈ B1)) <=> (X === B1)))
        val t4 = SC.RightSubstIff(
          t1.bot.left ++ t3.bot.right |- X === B1,
          2,
          List((X === B1, forall(z, in(z, X) <=> in(z, B1)))),
          LambdaFormulaFormula(Seq(h), h())
        ) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)], (∀z. (z ∈ X) <=> (z ∈ B1)) <=> (X === B1))) |- X=B1
        val t5 = SC.Cut(t1.bot.left |- X === B1, 3, 4, t3.bot.right.head) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- X=B1
        val t6 = SC.Rewrite(Set(H1, G, F) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) ==> (X === B1), 5) //  F |- [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] ==> X=B1
        val i3 = s14.bot // F |- ∀x. (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
        val t7 = SC.RightSubstEq(
          Set(H1, G, F, X === B1) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
          -3,
          List((X, B1)),
          LambdaTermFormula(Seq(f), forall(x, in(x, f) <=> exists(a, in(a, A) /\ phi(x, a))))
        ) // redGoal1 F, X=B1 |- [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
        val t8 = SC.Rewrite(
          Set(H1, G, F) |- X === B1 ==> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
          7
        ) // redGoal1 F |- X=B1 ==> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]      -------second half with t6
        val t9 = SC.RightIff(
          Set(H1, G, F) |- (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
          6,
          8,
          X === B1,
          forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))
        ) // goal  F |- X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]

        SCProof(steps(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9), imports(i1, i2, i3))
      },
      Vector(13, -3, 14)
    ) // goal  F |- X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s16 = SC.RightForall(
      (H1, G, F) |- forall(X, (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))),
      15,
      (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
      X
    ) // goal  F |- ∀X. X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s17 = SC.RightExists(
      (H1, G, F) |- exists(y, forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))),
      16,
      forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))),
      y,
      B1
    )
    val s18 = SC.LeftExists((exists(B1, F), G, H1) |- s17.bot.right, 17, F, B1) //  ∃B1. F |- ∃B1. ∀X. X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s19 = SC.Rewrite(s18.bot.left |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))), 18) //  ∃B1. F |- ∃!X. [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s20 = SC.Cut((G, H1) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))), 7, 19, exists(B1, F))
    val s21 = SC.LeftExists((H1, exists(B, G)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))), 20, G, B)
    val s22 = SC.Cut(H1 |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ phi(x, a)))), 6, 21, exists(B, G))
    val res = steps(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22)
    SCProof(res, imports(i1, i2, i3))
  } using (ax"replacementSchema", ax"comprehensionSchema", ax"extensionalityAxiom")
show
   */
}