package lisa.proven.mathematics

import lisa.proven.tactics.Destructors.*
import lisa.proven.tactics.ProofTactics.*
import lisa.transformers.SimpleProofTransformer
import lisa.utils.Printer
import lisa.kernel.proof.SCProofChecker
import lisa.transformers.Transformer
import lisa.kernel.proof.SCProof

object TransformersTests extends lisa.proven.Main {

    val x = VariableLabel("x")
    val y = VariableLabel("y")
    val z = VariableLabel("z")
    val h = VariableFormulaLabel("h")
    val fin = SCSubproof(
    {
        val pr0 = SCSubproof(
        {
            val pairSame11 = instantiateForall(new Proof(steps(), imports(ax"pairAxiom")), pairAxiom, x)
            val pairSame12 = instantiateForall(pairSame11, pairSame11.conclusion.right.head, y)
            instantiateForall(pairSame12, pairSame12.conclusion.right.head, z)
        },
        Seq(-1)
        )
        val pr1 = SCSubproof(
        {
            val pairSame21 = instantiateForall(new Proof(steps(), imports(ax"pairAxiom")), pairAxiom, y)
            val pairSame22 = instantiateForall(pairSame21, pairSame21.conclusion.right.head, x)
            instantiateForall(pairSame22, pairSame22.conclusion.right.head, z)
        },
        Seq(-1)
        )
        val pr2 = RightSubstIff(
        Sequent(pr1.bot.right, Set(in(z, pair(x, y)) <=> in(z, pair(y, x)))),
        0,
        List(((x === z) \/ (y === z), in(z, pair(y, x)))),
        LambdaFormulaFormula(Seq(h), in(z, pair(x, y)) <=> h)
        )
        val pr3 = Cut(Sequent(pr1.bot.left, pr2.bot.right), 1, 2, pr2.bot.left.head)
        val pr4 = RightForall(Sequent(Set(), Set(forall(z, pr2.bot.right.head))), 3, pr2.bot.right.head, z)
        Proof(steps(pr0, pr1, pr2, pr3, pr4), imports(ax"pairAxiom"))
    },
    Seq(-2)
    )
    val pairExt = SCSubproof(
    {
        val pairExt1 = instantiateForall(Proof(steps(), imports(ax"extensionalityAxiom")), ax"extensionalityAxiom", pair(x, y))
        instantiateForall(pairExt1, pairExt1.conclusion.right.head, pair(y, x))
    },
    Seq(-1)
    )
    val fin2 = byEquiv(
    pairExt.bot.right.head,
    fin.bot.right.head
    )(pairExt, fin)
    val fin3 = generalizeToForall(fin2, fin2.conclusion.right.head, x)
    val fin4 = generalizeToForall(fin3, fin3.conclusion.right.head, y)
    val pr = fin4.copy(imports = imports(ax"extensionalityAxiom", ax"pairAxiom"))
    val tr = SimpleProofTransformer(pr).transform()
    
    val A  = SchematicNPredicateLabel("A", 0)()
    val B  = SchematicNPredicateLabel("B", 0)()
    val C  = SchematicNPredicateLabel("C", 0)()

    val hypo = Hypothesis((A, A ==> (B \/ C)) |- (B, C, A ==> (B \/ C)), A ==> (B \/ C))
    val rew = Rewrite((A, A ==> (B \/ C)) |- (B, C), 0)
    
    val prpr = SCProof(IndexedSeq(hypo, rew), IndexedSeq())
    
    print(Printer.prettySCProof(SCProofChecker.checkSCProof(tr)))

    }
