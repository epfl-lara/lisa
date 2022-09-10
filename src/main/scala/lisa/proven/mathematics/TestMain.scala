package lisa.proven.mathematics

import lisa.kernel.proof.SCProof
import lisa.utils.Printer
import lisa.transformers.Transformer

import lisa.proven.tactics.ProofTactics.*
import lisa.kernel.proof.SCProofChecker
import lisa.transformers.SimpleProofTransformer

object TestMain extends lisa.proven.Main{
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
      val phi = SchematicNPredicateLabel("phi", 2)
      val sPhi = SchematicNPredicateLabel("P", 2)
      val sPsi = SchematicNPredicateLabel("P", 3)

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
      val pr = Proof(steps(s0, s1, s2), imports(i1, i2))

    println(Printer.prettySCProof(SCProofChecker.checkSCProof(SCProof(SimpleProofTransformer(pr).transform(pr), IndexedSeq()))))
    println(Printer.prettySCProof(pr))
    println((SCProofChecker.checkSCProof(pr).isValid))
}
    