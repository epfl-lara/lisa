package proven

import utilities.Printer
import lisa.kernel.fol.FOL.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory.*
import proven.ElementsOfSetTheory.*
import proven.tactics.ProofTactics
import test.ProofCheckerSuite
import utilities.Helpers.{_, given}
import utilities.Helpers.{_, given}

class ElementsOfSetTheoryTests extends ProofCheckerSuite {

  test("Verification of the proof of symmetry of the pair") {
    checkProof(proofUnorderedPairSymmetry, emptySeq +> forall(vl, forall(ul, pair(u, v) === pair(v, u))))
  }

  test("Verification of the proof of deconstruction of the unordered pair") {
    checkProof(
      proofUnorderedPairDeconstruction,
      emptySeq +>
        forall(
          sl,
          forall(
            tl,
            forall(
              ul,
              forall(
                vl,
                (pair(s, t) === pair(u, v)) ==>
                  (((VariableTerm(v) === t) /\ (VariableTerm(u) === s)) \/ ((VariableTerm(s) === v) /\ (VariableTerm(t) === u)))
              )
            )
          )
        )
    )
  }

  // forall x, y. (x in {y, y}) <=> (x = y)
  val singletonSetEqualityProof: SCProof = {
    val t0 = SCSubproof(
      {
        val t0 = Rewrite(() |- pairAxiom, -1)
        val p0 = ProofTactics.instantiateForall(SCProof(IndexedSeq(t0), IndexedSeq(() |- pairAxiom)), t0.bot.right.head, v)
        val p1 = ProofTactics.instantiateForall(p0, p0.conclusion.right.head, v)
        val p2: SCProof = ProofTactics.instantiateForall(p1, p1.conclusion.right.head, u)
        p2
      },
      IndexedSeq(-1),
      display = false
    )

    // |- f <=> (f \/ f)
    def selfIffOr(f: Formula): SCSubproof = SCSubproof(
      {
        val t0 = Hypothesis(Sequent(Set(f), Set(f)), f)
        val t1 = RightOr(Sequent(Set(f), Set(f \/ f)), 0, f, f)
        val t2 = LeftOr(Sequent(Set(f \/ f), Set(f)), Seq(0, 0), Seq(f, f))
        val t3 = RightImplies(Sequent(Set(), Set(f ==> (f \/ f))), 1, f, f \/ f)
        val t4 = RightImplies(Sequent(Set(), Set((f \/ f) ==> f)), 2, f \/ f, f)
        val t5 = RightIff(Sequent(Set(), Set(f <=> (f \/ f))), 3, 4, f, f \/ f)
        SCProof(IndexedSeq(t0, t1, t2, t3, t4, t5))
      },
      display = false
    )
    val t1 = selfIffOr(u === v)
    val xy = u === v
    val h = SchematicPredicateLabel("h", 0)
    val t2 = RightSubstIff(
      Sequent(Set((xy \/ xy) <=> xy), Set(xy <=> in(u, pair(v, v)))),
      0,
      List(((v === u) \/ (v === u), v === u)),
      LambdaFormulaFormula(Seq(h), in(u, pair(v, v)) <=> PredicateFormula(h, Seq.empty))
    )
    val t3 = Cut(Sequent(Set(), Set(xy <=> in(u, pair(v, v)))), 1, 2, (xy \/ xy) <=> xy)

    val p0 = SCProof(IndexedSeq(t0, t1, t2, t3), IndexedSeq(() |- pairAxiom))

    ProofTactics.generalizeToForall(ProofTactics.generalizeToForall(p0, vl), ul)
  }

  test("Singleton set equality") {
    checkProof(singletonSetEqualityProof, emptySeq +> forall(u, forall(v, (u === v) <=> in(u, pair(v, v)))))
  }

}
