package proven.DSetTheory
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.KernelHelpers.{*, given}
import lisa.kernel.Printer
import lisa.kernel.Printer.{prettyFormula, prettySCProof}
import lisa.kernel.fol.FOL
import proven.tactics.ProofTactics.*
import proven.tactics.Destructors.*
import lisa.settheory.AxiomaticSetTheory.*
import proven.ElementsOfSetTheory.{oPair, orderedPairDefinition}

import scala.collection.immutable.SortedSet
import lisa.kernel.proof.{SCProof, SCProofChecker}
import lisa.settheory.AxiomaticSetTheory

import scala.collection.immutable
object Part1 {
  val theory = AxiomaticSetTheory.runningSetTheory
  def axiom(f: Formula): theory.Axiom = theory.getAxiom(f).get

  private val x = SchematicFunctionLabel("x", 0)
  private val y = SchematicFunctionLabel("y", 0)
  private val z = SchematicFunctionLabel("z", 0)
  private val x1 = VariableLabel("x")
  private val y1 = VariableLabel("y")
  private val z1 = VariableLabel("z")
  private val f = SchematicFunctionLabel("f", 0)
  private val g = SchematicFunctionLabel("g", 0)
  private val h = SchematicPredicateLabel("h", 0)

  given Conversion[SchematicFunctionLabel, Term] with
    def apply(s: SchematicFunctionLabel): Term = s()

  /**
   */
  val russelParadox: SCProof = {
    val contra = (in(y, y)) <=> !(in(y, y))
    val s0 = Hypothesis(contra |- contra, contra)
    val s1 = LeftForall(forall(x1, in(x1, y) <=> !in(x1, x1)) |- contra, 0, in(x1, y) <=> !in(x1, x1), x1, y)
    val s2 = Rewrite(forall(x1, in(x1, y) <=> !in(x1, x1)) |- (), 1)
    // val s3 = LeftExists(exists(y1, forall(x1, in(x,y) <=> !in(x, x))) |- (), 2, forall(x1, in(x,y) <=> !in(x, x)), y1)
    // val s4 = Rewrite(() |- !exists(y1, forall(x1, in(x1,y1) <=> !in(x1, x1))), 3)
    SCProof(s0, s1, s2)
  }
  val thm_russelParadox = theory.proofToTheorem("russelParadox", russelParadox, Nil).get

  val thm4: SCProof = {
    // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,y) /\ sPhi(x,z)))))
    val i1 = () |- comprehensionSchema
    val i2 = russelParadox.conclusion // forall(x1, in(x1,y) <=> !in(x1, x1)) |- ()
    val p0: SCProofStep = InstPredSchema(() |- forall(z1, exists(y1, forall(x1, in(x1, y1) <=> (in(x1, z1) /\ !in(x1, x1))))), -1, Map(sPhi -> LambdaTermFormula(Seq(x, z), !in(x(), x()))))
    val s0 = SCSubproof(instantiateForall(SCProof(IndexedSeq(p0), IndexedSeq(i1)), z), Seq(-1)) // exists(y1, forall(x1, in(x1,y1) <=> (in(x1,z1) /\ !in(x1, x1))))
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
    SCProof(Vector(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10), Vector(i1, i2))
  }
  val thm_thm4 = theory.proofToTheorem("thm4", thm4, Seq(axiom(comprehensionSchema), thm_russelParadox)).get

  val thmMapFunctional: SCProof = {
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
    val A = SchematicFunctionLabel("A", 0)()
    val X = VariableLabel("X")
    val B = VariableLabel("B")
    val B1 = VariableLabel("B1")
    val phi = SchematicPredicateLabel("phi", 2)
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
    val p1 = instantiateForall(SCProof(Vector(p0), Vector(i1)), A)
    val s4 = SCSubproof(p1, Seq(-1)) //
    val s5 = Rewrite(s3.bot.right.head |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 4)
    val s6 = Cut((H1) |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x))))), 3, 5, s3.bot.right.head) // ⊢ ∃B. ∀x. (x ∈ A) ⇒ ∃y. (y ∈ B) ∧ (y = (x, b))

    val i2 = () |- comprehensionSchema // forall(z, exists(y, forall(x, in(x,y) <=> (in(x,z) /\ sPhi(x,z)))))
    val q0 = InstPredSchema(
      () |- instantiatePredicateSchemas(comprehensionSchema, Map(sPhi -> LambdaTermFormula(Seq(x1, z1), exists(a, in(a, A) /\ phi(x1, a))))),
      -1,
      Map(sPhi -> LambdaTermFormula(Seq(x1, z1), exists(a, in(a, A) /\ phi(x1, a))))
    )
    val q1 = instantiateForall(SCProof(Vector(q0), Vector(i2)), B)
    val s7 = SCSubproof(q1, Seq(-2)) // ∃y. ∀x. (x ∈ y) ↔ (x ∈ B) ∧ ∃a. a ∈ A /\ x = (a, b)      := exists(y, F(y) )
    SCProof(Vector(s0, s1, s2, s3, s4, s5, s6, s7), Vector(i1, i2))
    val s8 = SCSubproof({
      val y1 = VariableLabel("y1")
      val f = SchematicFunctionLabel("f", 0)
      /*
            val s0 = hypothesis(in(y, B)) // redgoal  (y ∈ B) |- (y ∈ B)     TRUE
            val s1 = RightSubstEq((in(y, B), y===x) |- in(x, B), 0, x, y, in(f(), B), f)// redgoal  (y ∈ B), (y = x) |- (x ∈ B)
            val s2 = LeftSubstEq((phi(x, a), in(y, B), phi(y, a)) |- in(x, B), 1, x, oPair(a,b), y===f(), f )// redGoal  x = (a, b), (y ∈ B), (y = (a, b)) |- (x ∈ B)
            val s3 = Rewrite((phi(x, a), in(y, B) /\ (phi(y, a))) |- in(x, B), 2)
            val s4 = LeftExists((phi(x, a), exists(y, in(y, B) /\ (phi(y, a)))) |- in(x, B), 3, in(y, B) /\ (phi(y, a)), y)// redGoal  x = (a, b), ∃y. (y ∈ B) ∧ (y = (a, b)) |- (x ∈ B)
            val s5 = Rewrite( (phi(x, a), And()==> exists(y, in(y, B) /\ (phi(y, a)))) |- in(x, B), 4) //redGoal (T) ⇒ ∃y. y ∈ B ∧ y = (a, b), x = (a, b) |- (x ∈ B)
            val s6 = LeftSubstIff(Set(phi(x, a), in(a, A)==> exists(y, in(y, B) /\ (phi(y, a))), And()<=>in(a, A)) |- in(x, B),5, And(), in(a, A), h()==> exists(y, in(y, B) /\ (phi(y, a))), h) //redGoal (a ∈ A) ⇒ ∃y. y ∈ B ∧ y = (a, b), a ∈ A <=> T, x = (a, b) |- (x ∈ B)
            val s7 = Rewrite(Set(in(a, A)==> exists(y, in(y, B) /\ (phi(y, a))), in(a, A) /\ (phi(x, a))) |- in(x, B), 6) //redGoal (a ∈ A) ⇒ ∃y. y ∈ B ∧ y = (a, b), a ∈ A ∧ x = (a, b) |- (x ∈ B)
            val s8 = LeftForall((forall(a, in(a, A)==> exists(y, in(y, B) /\ (phi(y, a)))), in(a, A) /\ (phi(x, a)))|- in(x, B), 7, in(a, A)==> exists(y, in(y, B) /\ (phi(y, a))), a, a) //redGoal ∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ y = (a, b), a ∈ A ∧ x = (a, b) |- (x ∈ B)
            val s9 = LeftExists((forall(a, in(a, A)==> exists(y, in(y, B) /\ (phi(y, a)))), exists(a, in(a, A) /\ (phi(x, a))))|- in(x, B), 8, in(a, A) /\ (phi(x, a)), a) //∀a. (a ∈ A) ⇒ ∃y. y ∈ B ∧ y = (a, b), ∃a. a ∈ A ∧ x = (a, b) |- (x ∈ B)
            SCProof(Vector(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9))
       */

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
      SCProof(Vector(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17))
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
      val p0 = instantiateForall(SCProof(hypothesis(F)), x)
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
      val p0 = instantiateForall(SCProof(hypothesis(F)), x)
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
          SCSubproof(instantiateForall(SCProof(Vector(Rewrite(() |- extensionalityAxiom, -1)), Vector(() |- extensionalityAxiom)), X, B1), Vector(-2)) // (∀z. (z ∈ X) <=> (z ∈ B1)) <=> (X === B1)))
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

        SCProof(Vector(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9), Vector(i1, i2, i3))
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
    val steps = Vector(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22)
    SCProof(steps, Vector(i1, i2, i3))
  }
  val thm_thmMapFunctional = theory.proofToTheorem("thmMapFunctional", thmMapFunctional, Seq(axiom(replacementSchema), axiom(comprehensionSchema), axiom(extensionalityAxiom))).get

  /**
   * ∀ b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b)    |-    ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)
   */
  val lemma1: SCProof = {
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
    val A = SchematicFunctionLabel("A", 0)()
    val X = VariableLabel("X")
    val B = SchematicFunctionLabel("B", 0)()
    val B1 = VariableLabel("B1")
    val phi = SchematicPredicateLabel("phi", 2)
    val psi = SchematicPredicateLabel("psi", 3)
    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> H)
    val i1 = thmMapFunctional.conclusion
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
    SCProof(Vector(s0, s1, s2, s3, s4, s5, s6, s7, s8), Vector(i1))

    // have ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s0
    // have (b ∈ B), ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s1
    // have (b ∈ B), (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s2
    // have (b ∈ B), ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s3
    // have ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢  (b ∈ B) ⇒ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s4
    // have ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢  ∀b. (b ∈ B) ⇒ ∃!X. ∀x. (x ∈ X) ↔ ∃a. (a ∈ A) ∧ ?psi(x, a, b)    s5
    // by thmMapFunctional have ∀b. (b ∈ B) ⇒ ∃!x. ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)        phi(x, b) = ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)    s6
    // have ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b)    |-    ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)   s7
  }
  val thm_lemma1 = theory.proofToTheorem("lemma1", lemma1, Seq(thm_thmMapFunctional)).get

  /*
    val lemma2 = SCProof({


        // goal ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b)   ⊢   ∃!Z. ∃X. Z=UX /\ ∀x. (x ∈ X) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)
        // redGoal ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b)   ⊢   ∃Z1. ∀Z. Z=Z1 <=> ∃X. Z=UX /\ ∀x. (x ∈ X) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)
        // redGoal ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b)   ⊢   ∀Z. Z=UX <=> ∃X. Z=UX /\ ∀x. (x ∈ X) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)
        // redGoal ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b)   ⊢   ∀Z. Z=UX <=> ∃X. Z=UX /\ ∀x. (x ∈ X) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)
    })
   */

  /**
   * ∃!x. ?phi(x)   ⊢   ∃!z. ∃x. z=?F(x) /\ ?phi(x)
   */
  val lemmaApplyFToObject: SCProof = {
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
      SCProof(Vector(s0, s1, s2, s3, s4, s5, s6))
    }) // redGoal2 ∀x. x=x1 <=> phi(x)   ⊢   ∃x. z=F(x) /\ phi(x) ==> F(x1)=z  g2.s5

    val g1 = SCSubproof({
      val s0 = hypothesis(phi(x1))
      val s1 = LeftForall(forall(x, (x === x1) <=> phi(x)) |- phi(x1), 0, (x === x1) <=> phi(x), x, x1)
      val s2 = hypothesis(z === F(x1))
      val s3 = RightAnd((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- (z === F(x1)) /\ phi(x1), Seq(2, 1), Seq(z === F(x1), phi(x1)))
      val s4 = RightExists((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- exists(x, (z === F(x)) /\ phi(x)), 3, (z === F(x)) /\ phi(x), x, x1)
      val s5 = Rewrite(forall(x, (x === x1) <=> phi(x)) |- z === F(x1) ==> exists(x, (z === F(x)) /\ phi(x)), 4)
      SCProof(Vector(s0, s1, s2, s3, s4, s5))
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

    SCProof(Vector(s0, s1, s2, s3, s4, s5, s6))

    // goal ∃!x. phi(x)   ⊢   ∃!z. ∃x. z=F(x) /\ phi(x)
    // redGoal ∃x1. ∀X. x=x1 <=> phi(x)   ⊢   ∃z1. ∀z. z1=z <=> ∃x. Z=F(x) /\ phi(x)  s4, s5
    // redGoal ∀x. x=x1 <=> phi(x)   ⊢   ∀z. F(x1)=z <=> ∃x. Z=F(x) /\ phi(x) s3
    // redGoal ∀x. x=x1 <=> phi(x)   ⊢   F(x1)=z <=> ∃x. Z=F(x) /\ phi(x) s2
    // redGoal1 ∀x. x=x1 <=> phi(x)   ⊢   F(x1)=z ==> ∃x. Z=F(x) /\ phi(x)  g1.s5
    // redGoal1 ∀x. x=x1 <=> phi(x), F(x1)=z   ⊢    ∃x. z=F(x) /\ phi(x) g1.s4
    // redGoal1 ∀x. x=x1 <=> phi(x), F(x1)=z   ⊢    z=F(x1) /\ phi(x1) g1.s3
    // redGoal11 ∀x. x=x1 <=> phi(x), F(x1)=z   ⊢    z=F(x1)     TRUE  g1.s2
    // redGoal12 ∀x. x=x1 <=> phi(x)  ⊢    phi(x1)  g1.s1
    // redGoal12 x1=x1 <=> phi(x1)  ⊢    phi(x1)
    // redGoal12 phi(x1)  ⊢    phi(x1)  g1.s0
    // redGoal2 ∀x. x=x1 <=> phi(x)   ⊢   ∃x. z=F(x) /\ phi(x) ==> F(x1)=z  g2.s5
    // redGoal2 ∀x. x=x1 <=> phi(x), ∃x. z=F(x) /\ phi(x)   ⊢   F(x1)=z  g2.s4
    // redGoal2 ∀x. x=x1 <=> phi(x), z=F(x), phi(x)   ⊢   F(x1)=z  g2.s3
    // redGoal2 x=x1 <=> phi(x), z=F(x), phi(x)   ⊢   F(x1)=z  g2.s2
    // redGoal2 x=x1 <=> phi(x), z=F(x), x=x1   ⊢   F(x1)=z  g2.s1
    // redGoal2 x=x1 <=> phi(x), z=F(x1), x=x1   ⊢   F(x1)=z TRUE  g2.s0
  }
  val thm_lemmaApplyFToObject = theory.proofToTheorem("lemmaApplyFToObject", lemmaApplyFToObject, Nil).get

  /**
   * ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!z. ∃x. (z = U(x)) ∧ ∀x_0. (x_0 ∈ x) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x_0) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)
   */
  val lemmaMapTwoArguments: SCProof = {
    val a = VariableLabel("a")
    val b = VariableLabel("b")
    val x = VariableLabel("x")
    val x1 = VariableLabel("x1")
    val a_ = SchematicFunctionLabel("a", 0)
    val b_ = SchematicFunctionLabel("b", 0)
    val x_ = SchematicFunctionLabel("x", 0)
    val y_ = SchematicFunctionLabel("y", 0)
    val F = SchematicFunctionLabel("F", 1)
    val A = SchematicFunctionLabel("A", 0)()
    val X = VariableLabel("X")
    val B = SchematicFunctionLabel("B", 0)()
    val phi = SchematicPredicateLabel("phi", 1)
    val psi = SchematicPredicateLabel("psi", 3)

    val i1 = lemma1.conclusion
    val i2 = lemmaApplyFToObject.conclusion
    val rPhi = forall(x, in(x, y_) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
    val seq0 = instantiatePredicateSchemaInSequent(i2, Map(phi -> LambdaTermFormula(Seq(y_), rPhi)))
    val s0 = InstPredSchema(seq0, -2, Map(phi -> LambdaTermFormula(Seq(y_), rPhi))) // val s0 = InstPredSchema(instantiatePredicateSchemaInSequent(i2, phi, rPhi, Seq(X)), -2, phi, rPhi, Seq(X))
    val seq1 = instantiateFunctionSchemaInSequent(seq0, Map(F -> LambdaTermTerm(Seq(x_), union(x_))))
    val s1 = InstFunSchema(seq1, 0, Map(F -> LambdaTermTerm(Seq(x_), union(x_))))
    val s2 = Cut(i1.left |- seq1.right, -1, 1, seq1.left.head)
    SCProof(Vector(s0, s1, s2), Vector(i1, i2))
  }
  val thm_lemmaMapTwoArguments = theory.proofToTheorem("lemmaMapTwoArguments", lemmaMapTwoArguments, Seq(thm_lemma1, thm_lemmaApplyFToObject)).get

  /**
   *  ⊢ ∃!z. ∃x. (z = U(x)) ∧ ∀x_0. (x_0 ∈ x) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x_0) ↔ ∃a. (a ∈ ?A) ∧ (x1 = (a, b))
   */
  val lemmaCartesianProduct: SCProof = {
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

    val i1 =
      lemmaMapTwoArguments.conclusion // ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!z. ∃x. (z = U(x)) ∧ ∀x_0. (x_0 ∈ x) ↔ ∃b. (b ∈ ?B) ∧ ∀x1. (x1 ∈ x_0) ↔ ∃a. (a ∈ ?A) ∧ ?psi(x1, a, b)
    val s0 = SCSubproof({
      val s0 = SCSubproof(makeFunctional(oPair(a, b)))
      val s1 = Weakening((in(b, B), in(a, A)) |- s0.bot.right, 0)
      val s2 = Rewrite(in(b, B) |- in(a, A) ==> s0.bot.right.head, 1)
      val s3 = RightForall(in(b, B) |- forall(a, in(a, A) ==> s0.bot.right.head), 2, in(a, A) ==> s0.bot.right.head, a)
      val s4 = Rewrite(() |- in(b, B) ==> forall(a, in(a, A) ==> s0.bot.right.head), 3)
      val s5 = RightForall(() |- forall(b, in(b, B) ==> forall(a, in(a, A) ==> s0.bot.right.head)), 4, in(b, B) ==> forall(a, in(a, A) ==> s0.bot.right.head), b)
      SCProof(Vector(s0, s1, s2, s3, s4, s5))
    }) // ∀b. (b ∈ ?B) ⇒ ∀a. (a ∈ ?A) ⇒ ∃!x. x= (a, b)

    val s1 = InstPredSchema(
      instantiatePredicateSchemaInSequent(i1, Map(psi -> LambdaTermFormula(Seq(x_, a_, b_), x_ === oPair(a_, b_)))),
      -1,
      Map(psi -> LambdaTermFormula(Seq(x_, a_, b_), x_ === oPair(a_, b_)))
    )
    val s2 = Cut(() |- s1.bot.right, 0, 1, s1.bot.left.head)

    val vA = VariableLabel("A")
    val vB = VariableLabel("B")
    val s3 = InstFunSchema(
      instantiateFunctionSchemaInSequent(s2.bot, Map(SchematicFunctionLabel("A", 0) -> LambdaTermTerm(Nil, vA))),
      2,
      Map(SchematicFunctionLabel("A", 0) -> LambdaTermTerm(Nil, vA))
    )
    val s4 = InstFunSchema(
      instantiateFunctionSchemaInSequent(s3.bot, Map(SchematicFunctionLabel("B", 0) -> LambdaTermTerm(Nil, vA))),
      3,
      Map(SchematicFunctionLabel("B", 0) -> LambdaTermTerm(Nil, vA))
    )
    val s5 = RightForall(() |- forall(vA, s4.bot.right.head), 4, s4.bot.right.head, vA)
    val s6 = RightForall(() |- forall(vB, s5.bot.right.head), 5, s5.bot.right.head, vB)
    SCProof(Vector(s0, s1, s2, s3, s4, s5, s6), Vector(i1))

  }
  println("cartesian")
  /*
    val thm_lemmaCartesianProduct = theory.proofToTheorem("lemmaCartesianProduct", lemmaCartesianProduct, Seq(thm_lemmaMapTwoArguments)).get

    val vA = VariableLabel("A")
    val vB = VariableLabel("B")
    val cart_product = ConstantFunctionLabel("cart_cross", 2)
    val def_oPair = theory.makeFunctionDefinition(lemmaCartesianProduct, Seq(thm_lemmaMapTwoArguments), cart_product, Seq(vA, vB), VariableLabel("z"), innerOfDefinition(lemmaCartesianProduct.conclusion.right.head)).get


   */

  def innerOfDefinition(f: Formula): Formula = f match {
    case BinderFormula(Forall, bound, inner) => innerOfDefinition(inner)
    case BinderFormula(ExistsOne, bound, inner) => inner
    case _ => f
  }

  // def makeFunctionalReplacement(t:Term)
  def makeFunctional(t: Term): SCProof = {
    val x = VariableLabel(freshId(t.freeVariables.map(_.id), "x"))
    val y = VariableLabel(freshId(t.freeVariables.map(_.id), "y"))
    val s0 = RightRefl(() |- t === t, t === t)
    val s1 = Rewrite(() |- (x === t) <=> (x === t), 0)
    val s2 = RightForall(() |- forall(x, (x === t) <=> (x === t)), 1, (x === t) <=> (x === t), x)
    val s3 = RightExists(() |- exists(y, forall(x, (x === y) <=> (x === t))), 2, forall(x, (x === y) <=> (x === t)), y, t)
    val s4 = Rewrite(() |- existsOne(x, x === t), 3)
    SCProof(s0, s1, s2, s3, s4)
  }

  def main(args: Array[String]): Unit = {
    def checkProof(proof: SCProof): Unit = {
      val error = SCProofChecker.checkSCProof(proof)
      println(prettySCProof(proof, error))
    }
    println("\nthmMapFunctional")
    checkProof(thmMapFunctional)
    println("\nlemma1")
    checkProof(lemma1)
    println("\nlemmaApplyFToObject")
    checkProof(lemmaApplyFToObject)
    println("\nlemmaMapTwoArguments")
    checkProof(lemmaMapTwoArguments)
    println("\nlemmaCartesianProduct")
    checkProof(lemmaCartesianProduct)
  }
}

// have union ∀x. ∀z. x ∈ Uz <=> ∃y. (x ∈ y /\ y ∈ z)
// have  x ∈ UY <=> ∃y. (x ∈ y /\ y ∈ Y)
//
//
// goal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b) ⊢ ∃Y. ∀X. (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), ∃!X. ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)      ⊢      ∃Y. ∀X. (UY=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), ∃Y. ∀X. (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)      ⊢     ∃Y. ∀X. (UY=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), ∀X. (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)      ⊢     ∃Y. ∀X. (UY=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), ∀X. (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)      ⊢     ∀X. (UY=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), ∀X. (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)      ⊢     (UY=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b)      ⊢     (UY=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b), x ∈ UY <=> ∃y. (x ∈ y /\ y ∈ Y)      ⊢     (UY=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal1 ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b), x ∈ UY <=> ∃y. (x ∈ y /\ y ∈ Y)      ⊢     (UY=X) => ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal1 ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b), x ∈ UY <=> ∃y. (x ∈ y /\ y ∈ Y), (UY=X)      ⊢      ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal1 ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b), x ∈ UY <=> ∃y. (x ∈ y /\ y ∈ Y), (UY=X)      ⊢      ∀x. (x ∈ UY) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal1 ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b), x ∈ UY <=> ∃y. (x ∈ y /\ y ∈ Y), (UY=X)      ⊢      ∀x. (x ∈ UY) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
// redGoal2 ∀b. (b ∈ B) ⇒ ∀a. (a ∈ A) ⇒ ∃!x. ?psi(x, a, b), (Y=X) <=> ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∀x1. (x1 ∈ x) ↔ ∃a. (a ∈ A) ∧ ?psi(x1, a, b), x ∈ UY <=> ∃y. (x ∈ y /\ y ∈ Y)      ⊢     (UY=X) <= ∀x. (x ∈ X) ↔ ∃b. (b ∈ B) ∧ ∃a. (a ∈ A) ∧ ?psi(x, a, b)
