package lisa.proven.tactics

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.Printer.*

import scala.collection.immutable.Set

/**
 * SCProof tactics are a set of strategies that help the user write proofs in a more expressive way
 * by focusing on the final goal rather on the individual steps.
 */
object ProofTactics {
  class TacticNotApplicable(msg: String) extends RuntimeException(msg)

  private def combineTwoSubproofs(sp1: SCSubproof, sp2: SCSubproof, otherSteps: SCProofStep*): SCSubproof =
    // sp1 and sp2 become steps of this subproof instead of the encompassing proof, hence their imports stay the same
    // but the premises change the numbering
    SCSubproof(
      SCProof(
        IndexedSeq(
          sp1.withPremises(-1 to -sp1.premises.length by -1),
          sp2.withPremises(-(sp1.premises.length + 1) to -(sp1.premises.length + sp2.premises.length) by -1)
        ) ++ otherSteps.toIndexedSeq,
        sp1.sp.imports ++ sp2.sp.imports
      ),
      sp1.premises ++ sp2.premises
    )

  def hypothesis(f: Formula): SCProofStep = Hypothesis(emptySeq +< f +> f, f)

  def instantiateForall(p: SCProof, phi: Formula, t: Term): SCProof = { // given a proof with a formula quantified with \forall on the right, extend the proof to the same formula with something instantiated instead.
    require(p.conclusion.right.contains(phi))
    phi match {
      case b @ BinderFormula(Forall, _, _) =>
        val c = p.conclusion
        val tempVar = VariableLabel(freshId(b.freeVariables.map(_.id), "x"))
        val in = instantiateBinder(b, t)
        val p1 = Hypothesis(Sequent(Set(in), Set(in)), in)
        val p2 = LeftForall(Sequent(Set(b), Set(in)), p.length, instantiateBinder(b, tempVar), tempVar, t)
        val p3 = Cut(Sequent(c.left, c.right - phi + in), p.length - 1, p.length + 1, phi)
        p withNewSteps IndexedSeq(p1, p2, p3)
      case _ => throw new Exception("not a forall")
    }
  }
  def instantiateForall(p: SCProof, phi: Formula, t: Term*): SCProof = { // given a proof with a formula quantified with \forall on the right, extend the proof to the same formula with something instantiated instead.
    t.foldLeft((p, phi)) { case ((p, f), t1) =>
      (
        instantiateForall(p, f, t1),
        f match {
          case b @ BinderFormula(Forall, _, _) => instantiateBinder(b, t1)
          case _ => throw new Exception
        }
      )
    }._1
  }
  def instantiateForall(p: SCProof, t: Term): SCProof = instantiateForall(p, p.conclusion.right.head, t) // if a single formula on the right
  def instantiateForall(p: SCProof, t: Term*): SCProof = { // given a proof with a formula quantified with \forall on the right, extend the proof to the same formula with something instantiated instead.
    t.foldLeft(p)((p1, t1) => instantiateForall(p1, t1))
  }
  def instantiateForall(sp: SCSubproof, phi: Formula, t: Term): SCSubproof = SCSubproof(instantiateForall(sp.sp, phi, t), sp.premises)
  def generalizeToForall(p: SCProof, phi: Formula, x: VariableLabel): SCProof = {
    require(p.conclusion.right.contains(phi))
    val p1 = RightForall(p.conclusion -> phi +> forall(x, phi), p.length - 1, phi, x)
    p appended p1
  }
  def generalizeToForall(p: SCProof, x: VariableLabel): SCProof = generalizeToForall(p, p.conclusion.right.head, x)
  def generalizeToForall(p: SCProof, x: VariableLabel*): SCProof = { // given a proof with a formula on the right, extend the proof to the same formula with variables universally quantified.
    x.foldRight(p)((x1, p1) => generalizeToForall(p1, x1))
  }
  def generalizeToForall(sp: SCSubproof, phi: Formula, x: VariableLabel): SCSubproof = SCSubproof(generalizeToForall(sp.sp, phi, x), sp.premises)

  def byEquiv(equiv: FOL.Formula, equivSide: FOL.Formula)(pEq: SCSubproof, pSide: SCSubproof): SCSubproof = {
    require(pEq.bot.right.contains(equiv))
    require(pSide.bot.right.contains(equivSide))
    require(equiv.isInstanceOf[ConnectorFormula])
    require(equiv.asInstanceOf[ConnectorFormula].label == Iff)
    require(equiv.asInstanceOf[ConnectorFormula].args.length == 2)
    val (fl, fr) = equiv match {
      case ConnectorFormula(Iff, Seq(fl, fr)) => (fl, fr)
      case _ => throw TacticNotApplicable(s"$equiv is not an Iff on two arguments")
    }
    val otherSide = if (isSame(equivSide, fl)) fr else if (isSame(equivSide, fr)) fl else throw new Error("not applicable")
    val p2 = hypothesis(equivSide)
    val p3 = hypothesis(otherSide)
    val p4 = LeftImplies(Sequent(Set(equivSide, equivSide ==> otherSide), Set(otherSide)), 2, 3, equivSide, otherSide)
    val p5 = LeftIff(Sequent(Set(equivSide, equivSide <=> otherSide), Set(otherSide)), 4, equivSide, otherSide)
    val p6 = Cut(pEq.bot -> equiv +< equivSide +> otherSide, 0, 5, equiv)
    val p7 = Cut(p6.bot -< equivSide ++ pSide.bot -> equivSide, 1, 6, equivSide)
    combineTwoSubproofs(pEq, pSide, p2, p3, p4, p5, p6, p7)
  }

  @deprecated
  def simpleFunctionDefinition(expression: LambdaTermTerm, out: VariableLabel): SCProof = {
    val x = out
    val LambdaTermTerm(vars, body) = expression
    val xeb = x === body
    val y = VariableLabel(freshId(body.freeVariables.map(_.id) ++ vars.map(_.id), "y"))
    val s0 = RightRefl(() |- body === body, body === body)
    val s1 = Rewrite(() |- (xeb) <=> (xeb), 0)
    val s2 = RightForall(() |- forall(x, (xeb) <=> (xeb)), 1, (xeb) <=> (xeb), x)
    val s3 = RightExists(() |- exists(y, forall(x, (x === y) <=> (xeb))), 2, forall(x, (x === y) <=> (xeb)), y, body)
    val s4 = Rewrite(() |- existsOne(x, xeb), 3)
    val v = Vector(s0, s1, s2, s3, s4) /*
    val v2 = args.foldLeft((v, s4.bot.right.head, 4))((prev, x) => {
      val fo = forall(x, prev._2)
      (prev._1 appended RightForall(emptySeq +> fo, prev._3, prev._2, x), fo, prev._3 + 1)
    })*/
    SCProof(v)
  }
  def byCase(phi: FOL.Formula)(psiGivenPhi: SCSubproof, psiGivenNotPhi: SCSubproof): SCSubproof = {
    val nphi = !phi
    val (leftAphi, leftBnphi) = (psiGivenPhi.bot.left.find(isSame(_, phi)), psiGivenNotPhi.bot.left.find(isSame(_, nphi)))

    require(leftAphi.nonEmpty && leftBnphi.nonEmpty)
    val p2 = RightNot(psiGivenPhi.bot -< leftAphi.get +> nphi, 0, phi)
    val p3 = Cut(psiGivenPhi.bot -< leftAphi.get ++ (psiGivenNotPhi.bot -< leftBnphi.get), 2, 1, nphi)
    combineTwoSubproofs(psiGivenPhi, psiGivenNotPhi, p2, p3)
  }
  // |- phi ==> psi           |- phi
  // -------------------------------------
  //          |- psi
  def modusPonens(phi: FOL.Formula)(proofPhi: SCSubproof, proofPhiImpliesPsi: SCSubproof): SCSubproof = {
    require(proofPhi.bot.right.contains(phi))
    val opsi = proofPhiImpliesPsi.bot.right.collectFirst({
      case ConnectorFormula(Implies, Seq(l, r)) if isSame(l, phi) => r
    })
    if (opsi.isEmpty) {
      throw TacticNotApplicable(s"Second proof does not prove any formula of form phi => psi")
    } else {
      val psi = opsi.get
      val p2 = hypothesis(psi)
      val p3 = LeftImplies(emptySeq ++ (proofPhi.bot -> phi) +< (phi ==> psi) +> psi, 0, 2, phi, psi)
      val p4 = Cut(emptySeq ++ (proofPhi.bot -> phi) ++< proofPhiImpliesPsi.bot +> psi ++> (proofPhiImpliesPsi.bot -> (phi ==> psi)), 1, 3, phi ==> psi)

      combineTwoSubproofs(proofPhi, proofPhiImpliesPsi, p2, p3, p4)
    }
  }

  def detectSubstitution(x: VariableLabel, f: Formula, s: Formula, c: Option[Term] = None): (Option[Term], Boolean) = (f, s) match {
    case (PredicateFormula(la1, args1), PredicateFormula(la2, args2)) if isSame(la1, la2) => {
      args1
        .zip(args2)
        .foldLeft[(Option[Term], Boolean)](c, true)((r1, a) => {
          val r2 = detectSubstitutionT(x, a._1, a._2, r1._1)
          (if (r1._1.isEmpty) r2._1 else r1._1, r1._2 && r2._2 && (r1._1.isEmpty || r2._1.isEmpty || isSame(r1._1.get, r2._1.get)))
        })
    }
    case (ConnectorFormula(la1, args1), ConnectorFormula(la2, args2)) if isSame(la1, la2) => {
      args1
        .zip(args2)
        .foldLeft[(Option[Term], Boolean)](c, true)((r1, a) => {
          val r2 = detectSubstitution(x, a._1, a._2, r1._1)
          (if (r1._1.isEmpty) r2._1 else r1._1, r1._2 && r2._2 && (r1._1.isEmpty || r2._1.isEmpty || isSame(r1._1.get, r2._1.get)))
        })
    }
    case (BinderFormula(la1, bound1, inner1), BinderFormula(la2, bound2, inner2)) if la1 == la2 && bound1 == bound2 => { // TODO renaming
      detectSubstitution(x, inner1, inner2, c)
    }
    case _ => (c, false)
  }
  def detectSubstitutionT(x: VariableLabel, t: Term, s: Term, c: Option[Term] = None): (Option[Term], Boolean) = (t, s) match {
    case (y: VariableTerm, z: Term) => {
      if (isSame(y.label, x)) {
        if (c.isDefined) {
          (c, isSame(c.get, z))
        } else {
          (Some(z), true)
        }
      } else (c, isSame(y, z))
    }
    case (FunctionTerm(la1, args1), FunctionTerm(la2, args2)) if isSame(la1, la2) => {
      args1
        .zip(args2)
        .foldLeft[(Option[Term], Boolean)](c, true)((r1, a) => {
          val r2 = detectSubstitutionT(x, a._1, a._2, r1._1)
          (if (r1._1.isEmpty) r2._1 else r1._1, r1._2 && r2._2 && (r1._1.isEmpty || r2._1.isEmpty || isSame(r1._1.get, r2._1.get)))
        })
    }
    case _ => (c, false)
  }

}
