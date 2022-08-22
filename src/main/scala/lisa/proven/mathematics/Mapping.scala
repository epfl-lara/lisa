package lisa.proven.mathematics

import lisa.automation.kernel.Destructors.*
import lisa.automation.kernel.ProofTactics.*

import SetTheory.*

/**
 * This file contains theorem related to the replacement schema, i.e. how to "map" a set through a functional symbol.
 * Leads to the definition of the cartesian product.
 */
object Mapping extends lisa.proven.Main {

  THEOREM("functionalMapping") of
    "∀a. (a ∈ ?A) ⇒ ∃!x. ?phi(x, a) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ ?A) ∧ ?phi(x, a)" PROOF {
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
      val s0 = hypothesis(H) // () |- existsOne(x, phi(x, a)))
      val s1 = Weakening((H, in(a, A)) |- existsOne(x, phi(x, a)), 0)
      val s2 = Rewrite((H) |- in(a, A) ==> existsOne(x, phi(x, a)), 1)
      // val s3 = RightForall((H) |- forall(a, in(a, A) ==> existsOne(x, phi(x, a))), 2, in(a, A) ==> existsOne(x, phi(x, a)), a) // () |- ∀a∈A. ∃!x. phi(x, a)
      val s3 = hypothesis(H1)
      val i1 = () |- replacementSchema
      val p0 = InstPredSchema(
        () |- instantiatePredicateSchemas(replacementSchema, Map(sPsi -> LambdaTermFormula(Seq(y, a, x), phi(x, a)))),
        -1,
        Map(sPsi -> LambdaTermFormula(Seq(y, a, x), phi(x, a)))
      )
      val p1 = instantiateForall(Proof(steps(p0), imports(i1)), A)
      val s4 = SCSubproof(p1, Seq(-1)) //
      val s5 = Rewrite(s3.bot.right.head |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 4)
      val s6 = Cut((H1) |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 3, 5, s3.bot.right.head) // ⊢ ∃B. ∀x. (x ∈ A) ⇒ ∃y. (y ∈ B) ∧ (y = (x, b))

      val i2 = () |- comprehensionSchema // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,z) /\ sPhi(x,z)))))
      val q0 = InstPredSchema(
        () |- instantiatePredicateSchemas(comprehensionSchema, Map(sPhi -> LambdaTermFormula(Seq(x, z), exists(a, in(a, A) /\ phi(x, a))))),
        -1,
        Map(sPhi -> LambdaTermFormula(Seq(x, z), exists(a, in(a, A) /\ phi(x, a))))
      )
      val q1 = instantiateForall(Proof(steps(q0), imports(i2)), B)
      val s7 = SCSubproof(q1, Seq(-2)) // ∃y. ∀x. (x ∈ y) ↔ (x ∈ B) ∧ ∃a. a ∈ A /\ x = (a, b)      := exists(y, F(y) )
      Proof(steps(s0, s1, s2, s3, s4, s5, s6, s7), imports(i1, i2))
      val s8 = SCSubproof({
        val y1 = VariableLabel("y1")
        val s0 = hypothesis(in(y1, B))
        val s1 = RightSubstEq((in(y1, B), x === y1) |- in(x, B), 0, List((x, y1)), LambdaTermFormula(Seq(f), in(f, B)))
        val s2 = LeftSubstIff(Set(in(y1, B), (x === y1) <=> phi(x, a), phi(x, a)) |- in(x, B), 1, List(((x === y1), phi(x, a))), LambdaFormulaFormula(Seq(h), h()))
        val s3 = LeftSubstEq(Set(y === y1, in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B), 2, List((y, y1)), LambdaTermFormula(Seq(f), (x === f) <=> phi(x, a)))
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
        RightForall(
          (H1, G, F) |- forall(x, in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a)))),
          13,
          in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))),
          x
        ) // G, F |- ∀x. (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)

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
            LambdaTermFormula(Seq(f), forall(x, in(x, f) <=> exists(a, in(a, A) /\ phi(x, a))))
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
      val f = VariableLabel("f")
      val h = VariableFormulaLabel("h")
      val A = VariableLabel("A")
      val X = VariableLabel("X")
      val B = VariableLabel("B")
      val B1 = VariableLabel("B1")
      val phi = SchematicPredicateLabel("phi", 2)
      val psi = SchematicPredicateLabel("psi", 3)
      val H = existsOne(x, phi(x, a))
      val H1 = forall(a, in(a, A) ==> H)
      val i1 = thm"functionalMapping"
      val H2 = instantiatePredicateSchemas(H1, Map(phi -> LambdaTermFormula(Seq(x, a), psi(x, a, b))))
      val s0 = InstPredSchema((H2) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))), -1, Map(phi -> LambdaTermFormula(Seq(x, a), psi(x, a, b))))
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
        forall(b, in(b, B) ==> existsOne(X, phi(X, b))) |- instantiateTermSchemas(i1.right.head, Map(A -> LambdaTermTerm(Nil, B))),
        -1,
        Map(A -> LambdaTermTerm(Nil, B))
      )
      val s7 = InstPredSchema(
        forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) |- existsOne(
          X,
          forall(x, in(x, X) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
        ),
        6,
        Map(phi -> LambdaTermFormula(Seq(y, b), forall(x, in(x, y) <=> exists(a, in(a, A) /\ psi(x, a, b)))))
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
      val f = VariableLabel("f")
      val phi = SchematicPredicateLabel("phi", 1)
      val g = VariableFormulaLabel("g")

      val g2 = SCSubproof({
        val s0 = hypothesis(F(x1) === z)
        val s1 = LeftSubstEq((x === x1, F(x) === z) |- F(x1) === z, 0, List((x, x1)), LambdaTermFormula(Seq(f), F(f) === z))
        val s2 = LeftSubstIff(Set(phi(x) <=> (x === x1), phi(x), F(x) === z) |- F(x1) === z, 1, List((x === x1, phi(x))), LambdaFormulaFormula(Seq(g), g))
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
      val y = VariableLabel("y")
      val F = SchematicFunctionLabel("F", 1)
      val A = VariableLabel("A")
      val B = VariableLabel("B")
      val phi = SchematicPredicateLabel("phi", 1)
      val psi = SchematicPredicateLabel("psi", 3)

      val i1 = thm"lemmaLayeredTwoArgumentsMap"
      val i2 = thm"applyFunctionToUniqueObject"
      val rPhi = forall(x, in(x, y) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
      val seq0 = instantiatePredicateSchemaInSequent(i2, Map(phi -> LambdaTermFormula(Seq(y), rPhi)))
      val s0 = InstPredSchema(seq0, -2, Map(phi -> LambdaTermFormula(Seq(y), rPhi))) // val s0 = InstPredSchema(instantiatePredicateSchemaInSequent(i2, phi, rPhi, Seq(X)), -2, phi, rPhi, Seq(X))
      val seq1 = instantiateFunctionSchemaInSequent(seq0, Map(F -> LambdaTermTerm(Seq(x), union(x))))
      val s1 = InstFunSchema(seq1, 0, Map(F -> LambdaTermTerm(Seq(x), union(x))))
      val s2 = Cut(i1.left |- seq1.right, -1, 1, seq1.left.head)
      Proof(steps(s0, s1, s2), imports(i1, i2))
    } using (thm"lemmaLayeredTwoArgumentsMap", thm"applyFunctionToUniqueObject")
  show

  val A = VariableLabel("A")
  val B = VariableLabel("B")
  private val z = VariableLabel("z")
  val cartesianProduct: ConstantFunctionLabel =
    DEFINE("cartProd", A, B) asThe z suchThat {
      val a = VariableLabel("a")
      val b = VariableLabel("b")
      val x = VariableLabel("x")
      val x0 = VariableLabel("x0")
      val x1 = VariableLabel("x1")
      val A = VariableLabel("A")
      val B = VariableLabel("B")
      exists(x, (z === union(x)) /\ forall(x0, in(x0, x) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x0) <=> exists(a, in(a, A) /\ (x1 === oPair(a, b)))))))
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
      val A = VariableLabel("A")
      val B = VariableLabel("B")
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
        instantiatePredicateSchemaInSequent(i1, Map(psi -> LambdaTermFormula(Seq(x, a, b), x === oPair(a, b)))),
        -1,
        Map(psi -> LambdaTermFormula(Seq(x, a, b), x === oPair(a, b)))
      )
      val s2 = Cut(() |- s1.bot.right, 0, 1, s1.bot.left.head)
      Proof(steps(s0, s1, s2), imports(i1))
    } using (thm"mapTwoArguments")
  show

}
