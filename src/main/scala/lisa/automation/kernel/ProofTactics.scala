package lisa.automation.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.Printer.*

/**
 * SCProof tactics are a set of strategies that help the user write proofs in a more expressive way
 * by focusing on the final goal rather on the individual steps.
 */
object ProofTactics {

  def hypothesis(f: Formula): SCProofStep = Hypothesis(emptySeq +< f +> f, f)

  def instantiateForall(p: SCProof, phi: Formula, t: Term): SCProof = { // given a proof with a formula quantified with \forall on the right, extend the proof to the same formula with something instantiated instead.
    require(p.conclusion.right.contains(phi))
    phi match {
      case b@BinderFormula(Forall, _, _) =>
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
          case b@BinderFormula(Forall, _, _) => instantiateBinder(b, t1)
          case _ => throw new Exception
        }
      )
    }._1
  }

  def instantiateForall(p: SCProof, t: Term): SCProof = instantiateForall(p, p.conclusion.right.head, t) // if a single formula on the right

  def instantiateForall(p: SCProof, t: Term*): SCProof = { // given a proof with a formula quantified with \forall on the right, extend the proof to the same formula with something instantiated instead.
    t.foldLeft(p)((p1, t1) => instantiateForall(p1, t1))
  }

  def generalizeToForall(p: SCProof, phi: Formula, x: VariableLabel): SCProof = {
    require(p.conclusion.right.contains(phi))
    val p1 = RightForall(p.conclusion -> phi +> forall(x, phi), p.length - 1, phi, x)
    p appended p1
  }

  def generalizeToForall(p: SCProof, x: VariableLabel): SCProof = generalizeToForall(p, p.conclusion.right.head, x)

  def generalizeToForall(p: SCProof, x: VariableLabel*): SCProof = { // given a proof with a formula on the right, extend the proof to the same formula with variables universally quantified.
    x.foldRight(p)((x1, p1) => generalizeToForall(p1, x1))
  }

  def byEquiv(f: Formula, f1: Formula)(pEq: SCProofStep, pr1: SCProofStep): SCProof = {
    require(pEq.bot.right.contains(f))
    require(pr1.bot.right.contains(f1))
    f match {
      case ConnectorFormula(Iff, Seq(fl, fr)) =>
        val f2 = if (isSame(f1, fl)) fr else if (isSame(f1, fr)) fl else throw new Error("not applicable")
        val p2 = hypothesis(f1)
        val p3 = hypothesis(f2)
        val p4 = LeftImplies(Sequent(Set(f1, f1 ==> f2), Set(f2)), 2, 3, f1, f2)
        val p5 = LeftIff(Sequent(Set(f1, f1 <=> f2), Set(f2)), 4, f1, f2)
        val p6 = Cut(pEq.bot -> (f1 <=> f2) +< f1 +> f2, 0, 5, f1 <=> f2)
        val p7 = Cut(p6.bot -< f1 ++ pr1.bot -> f1, 1, 6, f1)
        new SCProof(IndexedSeq(pEq, pr1, p2, p3, p4, p5, p6, p7))
      case _ => throw new Error("not applicable")
    }
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

  // p1 is a proof of psi given phi, p2 is a proof of psi given !phi
  def byCase(phi: Formula)(pa: SCProofStep, pb: SCProofStep): SCProof = {
    val nphi = !phi
    val (leftAphi, leftBnphi) = (pa.bot.left.find(isSame(_, phi)), pb.bot.left.find(isSame(_, nphi)))

    require(leftAphi.nonEmpty && leftBnphi.nonEmpty)
    val p2 = RightNot(pa.bot -< leftAphi.get +> nphi, 0, phi)
    val p3 = Cut(pa.bot -< leftAphi.get ++ (pb.bot -< leftBnphi.get), 2, 1, nphi)
    SCProof(IndexedSeq(pa, pb, p2, p3))
  }

  // pa is a proof of phi, pb is a proof of phi ==> ???
  // |- phi ==> psi, phi===>gamma            |- phi
  // -------------------------------------
  //          |- psi, gamma
  def modusPonens(phi: Formula)(pa: SCProofStep, pb: SCProofStep): SCProof = {
    require(pa.bot.right.contains(phi))
    val opsi = pb.bot.right.find {
      case ConnectorFormula(Implies, Seq(l, _)) if isSame(l, phi) => true
      case _ => false
    }
    if (opsi.isEmpty) SCProof(pa, pb)
    else {
      val psi = opsi.get.asInstanceOf[ConnectorFormula].args(1)
      val p2 = hypothesis(psi)
      val p3 = LeftImplies(emptySeq ++ (pa.bot -> phi) +< (phi ==> psi) +> psi, 0, 2, phi, psi)
      val p4 = Cut(emptySeq ++ (pa.bot -> phi) ++< pb.bot +> psi ++> (pb.bot -> (phi ==> psi)), 1, 3, phi ==> psi)
      SCProof(pa, pb, p2, p3, p4)
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
    case (y@ Term(l:VariableLabel, _), z: Term) => {
      if (isSame(y.label, x)) {
        if (c.isDefined) {
          (c, isSame(c.get, z))
        } else {
          (Some(z), true)
        }
      } else (c, isSame(y, z))
    }
    case (Term(la1, args1), Term(la2, args2)) if isSame(la1, la2) => {
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
