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

  val russelParadox = makeTHM("∀'x. elem('x, 'y) ↔ ¬elem('x, 'x) ⊢") {
    have(in(y, y) <=> !in(y, y) |- ()) by Restate
    andThen(forall(x, in(x, y) <=> !in(x, x)) |- ()) by LeftForall.withParameters(in(x, y) <=> !in(x, x), x, y)
  }
  show

  val unorderedPair_symmetry = makeTHM(() |- forall(y, forall(x, unorderedPair(x, y) === unorderedPair(y, x)))) {

    val objectiveA: Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))
    val objectiveB: Sequent = () |- forall(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) <=> (unorderedPair(x, y) === unorderedPair(y, x))

    val part1 = have(objectiveA) subproof {
      val pr0 = have(() |- in(z, unorderedPair(y, x)) <=> (y === z) \/ (x === z)) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), y), y -> LambdaTermTerm(Seq(), x)))(ax"pairAxiom")
      val pr1 = have(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z) |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by
        RightSubstIff(List((in(z, unorderedPair(y, x)), (x === z) \/ (y === z))), LambdaFormulaFormula(Seq(h), in(z, unorderedPair(x, y)) <=> h))(ax"pairAxiom")
      have(() |- in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x))) by Cut.withParameters(in(z, unorderedPair(y, x)) <=> (x === z) \/ (y === z))(pr0, pr1)
      andThen(objectiveA) by RightForall.withParameters(in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)), z)
    }

    val part2 = have(objectiveB) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), unorderedPair(x, y)), y -> LambdaTermTerm(Seq(), unorderedPair(y, x))))(ax"extensionalityAxiom")

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
      val p2 = have(() |- in(z, unorderedPair(x1, y1)) <=> (x1 === z) \/ (y1 === z)) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), x1), y -> LambdaTermTerm(Seq(), y1)))(ax"pairAxiom")
      val p3 = have((pxy === pxy1) |- (in(z, unorderedPair(x1, y1)) <=> (x === z) \/ (y === z))) by RightSubstEq(List((pxy, pxy1)), LambdaTermFormula(Seq(g), in(z, g) <=> ((x === z) \/ (y === z))))(
        ax"pairAxiom"
      )
      val p4 = andThen(emptySeq +< p3.bot.left.head +< p2.bot.right.head +> (((z === x) \/ (z === y)) <=> ((z === x1) \/ (z === y1)))) by RightSubstIff(
        List(((z === x1) \/ (z === y1), in(z, pxy1))),
        LambdaFormulaFormula(Seq(h), h <=> ((z === x) \/ (z === y)))
      )
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
          val pa0_2 = andThen(emptySeq +< (pxy === pxy1) +< (x === y) +< (f1 <=> (f1 \/ f1)) +> (f1 <=> ((z === x1) \/ (z === y1)))) by RightSubstIff(
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
          val pb0_0 =
            have(emptySeq +< (pxy === pxy1) +> (((y === x) \/ (y === y)) <=> ((y === x1) \/ (y === y1)))) by InstFunSchema(Map[SchematicTermLabel, LambdaTermTerm](z -> LambdaTermTerm(Seq(), y)))(p0)
          have(emptySeq +> (y === y)) by RightRefl.withParameters(y === y)
          val pb0_1 = andThen(emptySeq +> ((y === y) \/ (y === x))) by RightOr.withParameters(y === y, y === x)
          have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ 'y = 'x1 ∨ 'y = 'y1") by ByEquiv(pb0_0.bot.right.head, pb0_1.bot.right.head)(pb0_1, pb0_0) //  ({x,y}={x',y'}) |- (y=x')∨(y=y')
          andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1 ⊢ 'y = 'x ∨ 'y = 'y1") by RightSubstEq(List((x, x1)), LambdaTermFormula(Seq(g), (y === g) \/ (y === y1)))
          val rb1 = andThen("unorderedPair('x, 'y) = unorderedPair('x1, 'y1); 'x = 'x1; ('y = 'x) ⊢ 'y = 'y1") by destructRightOr(y === x, y === y1)
          andThen(rb1.bot +< !(y === x) -> (y === x)) by LeftNot.withParameters(y === x) //  (x=x'), ({x,y}={x',y'}), ¬(y=x) |- (y=y')
        }
      ) //
      val pc1 = have(emptySeq +> (x === x)) by RightRefl.withParameters(x === x)
      val pc2 = have(emptySeq ++< pc0.bot +> ((y1 === y) /\ (x === x))) by RightAnd(pc0, pc1) // ({x,y}={x',y'}), x=x' |- (x=x /\ y=y')
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
      val pd2 = have(emptySeq ++< pd1.bot +> (x === x1) +> ((x === y1) /\ (y === x1))) by RightAnd.withParameters(x === y1, y === x1)(pd0, pd1) //  ({x,y}={x',y'})  |- x=x', (x=y' /\ y=x') ---
      val pd3 = andThen(emptySeq ++< pd2.bot +< !(x === x1) +> ((x === y1) /\ (y === x1))) by LeftNot.withParameters(x === x1) //  ({x,y}={x',y'}), !x===x1 |- (x=y' /\ y=x')
      andThen(emptySeq ++< pd3.bot +> (pd3.bot.right.head \/ ((x === x1) /\ (y === y1)))) by Trivial
    }

    val p1 = have("unorderedPair('x, 'y) = unorderedPair('x1, 'y1) ⊢ ('y1 = 'y ∧ 'x1 = 'x ∨ 'x = 'y1 ∧ 'y = 'x1)") by ByCase(x === x1)(aaa, bbb) //  ({x,y}={x',y'}) |- (x=x' /\ y=y')\/(x=y' /\ y=x')
    andThen(emptySeq +> (p1.bot.left.head ==> p1.bot.right.head)) by RightImplies.withParameters(p1.bot.left.head, p1.bot.right.head) //   |- ({x,y}={x',y'}) ==> (x=x' /\ y=y')\/(x=y' /\ y=x')
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
    andThen((forall(x, in(x, z)), in(x, y) <=> (in(x, z) /\ !in(x, x))) |- in(x, y) <=> !in(x, x)) by LeftForall.withParameters(in(x, z), x, x)
    andThen((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- in(x, y) <=> !in(x, x)) by LeftForall.withParameters(in(x, y) <=> (in(x, z) /\ !in(x, x)), x, x)
    val s6 = andThen((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- forall(x, in(x, y) <=> !in(x, x))) by RightForall.withParameters(in(x, y) <=> !in(x, x), x)
    val s7 = have(forall(x, in(x, y) <=> !in(x, x)) |- ()) by InstFunSchema(Map(y -> LambdaTermTerm(Nil, y)))(thm"russelParadox")
    have((forall(x, in(x, z)), forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))) |- ()) by Cut.withParameters(forall(x, in(x, y) <=> !in(x, x)))(s6, s7)
    val s9 = andThen((forall(x, in(x, z)), exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))) |- ()) by LeftExists.withParameters(forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))), y)
    val s10 = have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x))))) by InstPredSchema(Map(P -> LambdaTermFormula(Seq(x, z), !in(x, x))))(ax"comprehensionSchema")

    have(forall(x, in(x, z)) |- ()) by Cut.withParameters(exists(y, forall(x, in(x, y) <=> (in(x, z) /\ !in(x, x)))))(s10, s9)
  }
  show

  val functionalMapping = makeTHM("∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'phi('x, 'a)) ⊢ ∃! 'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'a. elem('a, 'A) ∧ 'phi('x, 'a))") {
    val a: VariableLabel = VariableLabel("a")
    val b: VariableLabel = variable

    val f = variable
    val A = variable
    val X = variable
    val B = variable
    val B1 = variable
    val phi: SchematicPredicateLabel = predicate(2)
    val P: SchematicPredicateLabel = predicate(2)
    val P2 = SchematicPredicateLabel("P", 3)

    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> existsOne(x, phi(x, a)))

    have((H) |- in(a, A) ==> existsOne(x, phi(x, a))) by Trivial
    val s3 = have(H1 |- H1) by Hypothesis
    val s = instantiatePredicateSchemas(ax"replacementSchema", Map(P2 -> LambdaTermFormula(Seq(a, x, y), phi(x, a))))
    val p0 = have(" ⊢ (∀'x. elem('x, 'A) ⇒ (∃!'y. 'phi('y, 'x))) ⇒ (∃'B. ∀'x. elem('x, 'A) ⇒ (∃'y. elem('y, 'B) ∧ 'phi('y, 'x)))") by InstPredSchema(
      Map(P2 -> LambdaTermFormula(Seq(a, x, y), phi(y, x)))
    )(ax"replacementSchema")

    val s5 = andThen("(∀'x. elem('x, 'A) ⇒ (∃!'y. 'phi('y, 'x))) ⊢ (∃'B. ∀'x. elem('x, 'A) ⇒ (∃'y. elem('y, 'B) ∧ 'phi('y, 'x)))") by Rewrite
    val s6 = andThen(H1 |- exists(B, forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a)))))) by InstFunSchema(
      Map(
        x -> LambdaTermTerm(Nil, a),
        y -> LambdaTermTerm(Nil, x)
      )
    )
    // have((H1) |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x)))) ))by Cut.withParameters(H1)(s3, s5) // ⊢ ∃B. ∀x. (x ∈ A) ⇒ ∃y. (y ∈ B) ∧ (y = (x, b))
    // val s6 = andThen(H1 |- exists(B, forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a)))))) by RightExists.withParameters(forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a)))), B, B)
    val q0 = have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ exists(a, in(a, A) /\ phi(x, a)))))) by InstPredSchema(
      Map(P -> LambdaTermFormula(Seq(x, z), exists(a, in(a, A) /\ phi(x, a))))
    )(ax"comprehensionSchema")
    val s7 = andThen(() |- exists(y, forall(x, in(x, y) <=> (in(x, B) /\ exists(a, in(a, A) /\ phi(x, a)))))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), B)))

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
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a) /\ in(y1, B), phi(x, a)) |- in(x, B)) by Rewrite
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), exists(y1, phi(y1, a) /\ in(y1, B)), phi(x, a)) |- in(x, B)) by LeftExists.withParameters(phi(y1, a) /\ in(y1, B), y1)
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), True ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a)) |- in(x, B)) by Rewrite
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a), in(a, A)) |- in(x, B)) by LeftSubstIff(
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, phi(y, a) /\ in(y, B)))
      )
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftForall.withParameters(
        in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)),
        a,
        a
      )
      andThen(Set(in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftSubstIff(
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, forall(x, (y === x) <=> phi(x, a))))
      )
      andThen(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftForall
        .withParameters(in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), a, a)

      andThen(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a) /\ in(a, A)) |- in(x, B)) by Rewrite
      andThen(
        Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)
      ) by LeftExists.withParameters(phi(x, a) /\ in(a, A), a)

      andThen(Set(forall(a, in(a, A) ==> existsOne(x, phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)) by Rewrite
    }
    val G = forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a))))
    val F = forall(x, iff(in(x, B1), in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))))
    val left = in(x, B1)
    val right = in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))

    val s9 = have(Set(F, in(x, B), exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1)) subproof {
      val p0 = have(F |- F) by Hypothesis
      andThen("") by InstantiateForall(x)
      andThen(F |- (left ==> right) /\ (right ==> left)) by Rewrite
      andThen(F |- (right ==> left)) by destructRightAnd((right ==> left), (left ==> right)) // F |- in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a))) => in(x, B1)
      andThen(Set(F, in(x, B), exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1)) by Rewrite
    }
    have((s8.bot.left ++ s9.bot.left.filterNot(isSame(_, in(x, B)))) |- in(x, B1)) by Cut.withParameters(in(x, B))(s8, s9)
    val s11 = andThen(Set(H1, G, F) |- exists(a, in(a, A) /\ (phi(x, a))) ==> in(x, B1)) by Rewrite // F |- ∃a. a ∈ A ∧ x = (a, b) => (x ∈ B1)   --- half

    val s12 = have(F |- (in(x, B1) ==> exists(a, in(a, A) /\ (phi(x, a))))) subproof {
      val p0 = have(F |- F) by Hypothesis
      andThen("") by InstantiateForall(x: Term)
      andThen(F |- (left ==> right) /\ (right ==> left)) by Rewrite
      andThen(F |- (left ==> right)) by destructRightAnd((left ==> right), (right ==> left))
      andThen(Set(F, in(x, B1)) |- exists(a, in(a, A) /\ (phi(x, a))) /\ in(x, B)) by Rewrite
      andThen(Set(F, in(x, B1)) |- exists(a, in(a, A) /\ (phi(x, a)))) by destructRightAnd(exists(a, in(a, A) /\ (phi(x, a))), in(x, B))
      andThen(F |- (in(x, B1) ==> exists(a, in(a, A) /\ (phi(x, a))))) by Rewrite
    }
    val s13 =
      have((H1, G, F) |- in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a)))) by RightIff
        .withParameters(in(x, B1), exists(a, in(a, A) /\ (phi(x, a))))(s11, s12) // have F |- (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
    val s14 = andThen((H1, G, F) |- forall(x, in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))))) by RightForall.withParameters(in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))), x)
    have(Set(H1, G, F) |- (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) subproof {
      val left = Set(H1, G, F, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))
      have(Set(H1, G, F, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, X) <=> in(x, B1)) by RightSubstIff(
        List((in(x, X), exists(a, in(a, A) /\ (phi(x, a))))),
        LambdaFormulaFormula(Seq(h), h() <=> in(x, B1))
      )(s13)
      andThen(left |- in(x, X) <=> in(x, B1)) by LeftForall.withParameters(in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))), x, x)
      val t2 =
        andThen(left |- forall(x, in(x, X) <=> in(x, B1))) by RightForall.withParameters(in(x, X) <=> in(x, B1), x) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- ∀z. (z ∈ X) <=> (z ∈ B1)

      val t3 = have(forall(z, in(z, X) <=> in(z, B1)) <=> (X === B1)) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), X), y -> LambdaTermTerm(Seq(), B1)))(ax"extensionalityAxiom")
      val t4 = have(left ++ t3.bot.right |- X === B1) by RightSubstIff(List((X === B1, forall(z, in(z, X) <=> in(z, B1)))), LambdaFormulaFormula(Seq(h), h()))(t2)
      have((left |- X === B1)) by Cut.withParameters(t3.bot.right.head)(t3, t4)
      val t6 = andThen(Set(H1, G, F) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) ==> (X === B1)) by Rewrite
      have(Set(H1, G, F, X === B1) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) by RightSubstEq(
        List((X: Term, B1: Term)),
        LambdaTermFormula(Seq(f), forall(x, in(x, f) <=> exists(a, in(a, A) /\ phi(x, a))))
      )(s14)
      val t8 = andThen(Set(H1, G, F) |- X === B1 ==> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) by Rewrite
      have(Set(H1, G, F) |- (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) by RightIff.withParameters(
        X === B1,
        forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))
      )(t6, t8)
    }

    andThen((H1, G, F) |- forall(X, (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by RightForall.withParameters(
      (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
      X
    )
    val s17 = andThen((H1, G, F) |- exists(y, forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))))) by RightExists.withParameters(
      forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))),
      y,
      B1
    )
    val s18 = andThen((exists(B1, F), G, H1) |- s17.bot.right) by LeftExists.withParameters(F, B1) //  ∃B1. F |- ∃B1. ∀X. X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s19 = andThen(s18.bot.left |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by Rewrite
    val s20 = have(() |- exists(B1, F)) by InstFunSchema(Map(y -> LambdaTermTerm(Seq(), B1)))(s7)
    have((G, H1) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by Cut.withParameters(exists(B1, F))(s20, s19)
    val s21 = andThen((H1, exists(B, G)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by LeftExists.withParameters(G, B)
    have(H1 |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ phi(x, a))))) by Cut.withParameters(exists(B, G))(s6, s21)
    andThen("∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'phi('x, 'a)) ⊢ ∃! 'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'a. elem('a, 'A) ∧ 'phi('x, 'a))") by Rewrite
  }
  show

  val lemmaLayeredTwoArgumentsMap = makeTHM(
    "∀ 'b. elem('b, 'B) ⇒ (∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'psi('x, 'a, 'b))) ⊢ ∃!'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'b. elem('b, 'B) ∧ (∀ 'x1. elem('x1, 'x) ↔ (∃ 'a. elem('a, 'A) ∧ 'psi('x1, 'a, 'b))))"
  ) {
    val a = variable
    val b = variable
    val x1 = variable
    val f = variable
    val A = variable
    val X = variable
    val B = variable
    val B1 = variable
    val phi = predicate(2)
    val psi = predicate(3)
    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> H)
    val H2 = instantiatePredicateSchemas(H1, Map(phi -> LambdaTermFormula(Seq(x, a), psi(x, a, b))))

    have((H2) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by InstPredSchema(
      Map(phi -> LambdaTermFormula(Seq(x, a), psi(x, a, b)))
    )(thm"functionalMapping")

    andThen((H2, in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by Weakening
    andThen((in(b, B) ==> H2, in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by LeftSubstIff(List((in(b, B), And())), LambdaFormulaFormula(Seq(h), h() ==> H2))
    andThen((forall(b, in(b, B) ==> H2), in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by LeftForall.withParameters(in(b, B) ==> H2, b, b)
    andThen(forall(b, in(b, B) ==> H2) |- in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by Rewrite
    val s5 = andThen(forall(b, in(b, B) ==> H2) |- forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))))) by RightForall.withParameters(
      in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))),
      b
    )

    have(forall(b, in(b, B) ==> existsOne(X, phi(X, b))) |- instantiateTermSchemas(thm"functionalMapping".proposition.right.head, Map(A -> LambdaTermTerm(Nil, B)))) by InstFunSchema(
      Map(A -> LambdaTermTerm(Nil, B))
    )(thm"functionalMapping")
    val s7 = andThen(
      forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) |- existsOne(
        X,
        forall(x, in(x, X) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
      )
    ) by InstPredSchema(
      Map(phi -> LambdaTermFormula(Seq(y, b), forall(x, in(x, y) <=> exists(a, in(a, A) /\ psi(x, a, b)))))
    )

    val s8 = have(forall(b, in(b, B) ==> H2) |- existsOne(X, forall(x, in(x, X) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b))))))) by Cut.withParameters(
      forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))))
    )(s5, s7)

  }
  show
  /*
  val applyFunctionToUniqueObject = makeTHM("∃! 'x. 'phi('x) ⊢ ∃! 'z. ∃ 'x. ('z = 'F('x)) ∧ 'phi('x)") {
    val x1 = variable
    val z1 = variable
    val F = function(1)
    val f = variable
    val phi = predicate(1)
    val g = formulaVariable

    val g2 = have(forall(x, phi(x) <=> (x === x1)) |- exists(x, phi(x) /\ (F(x) === z)) ==> (F(x1) === z)) subproof {
      have(F(x1) === z |- F(x1) === z) by Hypothesis
      andThen((x === x1, F(x) === z) |- F(x1) === z) by LeftSubstEq(List((x, x1)), LambdaTermFormula(Seq(f), F(f) === z))
      andThen(Set(phi(x) <=> (x === x1), phi(x), F(x) === z) |- F(x1) === z) by LeftSubstIff(List((x === x1, phi(x))), LambdaFormulaFormula(Seq(g), g))
      andThen(Set(forall(x, phi(x) <=> (x === x1)), phi(x), F(x) === z) |- F(x1) === z) by LeftForall.withParameters(phi(x) <=> (x === x1), x, x)
      andThen(Set(forall(x, phi(x) <=> (x === x1)), phi(x) /\ (F(x) === z)) |- F(x1) === z) by Rewrite
      andThen(Set(forall(x, phi(x) <=> (x === x1)), exists(x, phi(x) /\ (F(x) === z))) |- F(x1) === z) by LeftExists.withParameters(phi(x) /\ (F(x) === z), x)
      andThen(forall(x, phi(x) <=> (x === x1)) |- exists(x, phi(x) /\ (F(x) === z)) ==> (F(x1) === z)) by Rewrite
    }

    val g1 = have(forall(x, (x === x1) <=> phi(x)) |- z === F(x1) ==> exists(x, (z === F(x)) /\ phi(x))) subproof {
      have(phi(x1) |- phi(x1)) by Hypothesis
      val s1 = andThen(forall(x, (x === x1) <=> phi(x)) |- phi(x1)) by LeftForall.withParameters((x === x1) <=> phi(x), x, x1)
      val s2 = have(z === F(x1) |- z === F(x1)) by Hypothesis
      have((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- (z === F(x1)) /\ phi(x1)) by RightAnd.withParameters(z === F(x1), phi(x1))(s2, s1)
      andThen((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- exists(x, (z === F(x)) /\ phi(x))) by RightExists.withParameters((z === F(x)) /\ phi(x), x, x1)
      andThen(forall(x, (x === x1) <=> phi(x)) |- z === F(x1) ==> exists(x, (z === F(x)) /\ phi(x))) by Rewrite
    }

    have(forall(x, (x === x1) <=> phi(x)) |- (z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x))) by RightIff.withParameters(z === F(x1), exists(x, (z === F(x)) /\ phi(x)))(g1, g2)
    andThen(forall(x, (x === x1) <=> phi(x)) |- forall(z, (z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x)))) by RightForall.withParameters((z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x)), z)
    andThen(forall(x, (x === x1) <=> phi(x)) |- exists(z1, forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x))))) by RightExists.withParameters(
      forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x))), z1, F(x1))
    andThen(exists(x1, forall(x, (x === x1) <=> phi(x))) |- exists(z1, forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x))))) by LeftExists.withParameters(forall(x, (x === x1) <=> phi(x)), x1)
    andThen(existsOne(x, phi(x)) |- existsOne(z, exists(x, (z === F(x)) /\ phi(x)))) by Rewrite

  }
  show

  val mapTwoArguments = makeTHM("∀ 'b. elem('b, 'B) ⇒ (∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'psi('x, 'a, 'b))) ⊢ " +
      "∃!'z. ∃'x. 'z = union('x) ∧ (∀ 'x_2. elem('x_2, 'x) ↔ " +
      "(∃ 'b. elem('b, 'B) ∧ (∀ 'x1. elem('x1, 'x_2) ↔ (∃ 'a. elem('a, 'A) ∧ 'psi('x1, 'a, 'b)))))") {
    val x1 = variable
    val a = variable
    val b = variable
    val F = function(1)
    val A = variable
    val B = variable
    val phi = predicate(1)
    val psi = predicate(3)

    val i1 = thm"lemmaLayeredTwoArgumentsMap"
    val i2 = thm"applyFunctionToUniqueObject"
    val rPhi = forall(x, in(x, y) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
    val seq0 = instantiatePredicateSchemaInSequent(i2.proposition, Map(phi -> LambdaTermFormula(Seq(y), rPhi)))
    val s0 = have(seq0) by InstPredSchema(Map(phi -> LambdaTermFormula(Seq(y), rPhi)))(i2)

    val seq1 = instantiateFunctionSchemaInSequent(seq0, Map(F -> LambdaTermTerm(Seq(x), union(x))))
    val s1 = andThen(seq1) by InstFunSchema(Map(F -> LambdaTermTerm(Seq(x), union(x))))
    have(i1.proposition.left |- seq1.right) by Cut.withParameters(seq1.left.head)(i1, s1)
  }
  show */
}
