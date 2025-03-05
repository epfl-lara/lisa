package lisa.automation

import lisa.utils.fol.FOL as F
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib.*
import lisa.utils.K.{_, given}

/**
 * A tactic object dedicated to solve any propositionaly provable sequent (possibly in exponential time). Can be used with arbitrary many premises.
 * Leverages the OL algorithm for scalafmpropositional logic.
 */
object Tautology extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic {

  /**
   * Given a targeted conclusion sequent, try to prove it using laws of propositional logic and reflexivity and symmetry of equality.
   *
   * @param proof The ongoing proof object in which the step happens.
   * @param bot The desired conclusion.
   */
  def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
    val botK = bot.underlying
    solveSequent(botK) match {
      case Left(value) => proof.ValidProofTactic(bot, value.steps, Seq())
      case Right((msg, seq)) => proof.InvalidProofTactic(msg)
    }
  }

  /**
   * Given a targeted conclusion sequent, try to prove it using laws of propositional logic and reflexivity and symmetry of equality.
   * Uses the given already proven facts as assumptions to reach the desired goal.
   *
   * @param proof The ongoing proof object in which the step happens.
   * @param premise A previously proven step necessary to reach the conclusion.
   * @param bot   The desired conclusion.
   */
  def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
    from(using lib, proof)(Seq(premise)*)(bot)

  def from(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
    val botK = bot.underlying
    val premsFormulas: Seq[((proof.Fact, Expression), Int)] = premises.map(p => (p, sequentToFormula(proof.getSequent(p).underlying))).zipWithIndex
    val initProof = premsFormulas.map(s => Restate(() |- s._1._2, -(1 + s._2))).toList
    val sqToProve = botK ++<< (premsFormulas.map(s => s._1._2).toSet |- ())

    solveSequent(sqToProve) match {
      case Left(value) =>
        val subpr = SCSubproof(value)
        val stepsList = premsFormulas.foldLeft[List[SCProofStep]](List(subpr))((prev: List[SCProofStep], cur) => {
          val ((prem, form), position) = cur
          if prev.head.bot.left.contains(form) then Cut(prev.head.bot -<< form, position, initProof.length + prev.length - 1, form) :: prev
          else prev
        })
        val steps = (initProof ++ stepsList.reverse).toIndexedSeq
        proof.ValidProofTactic(bot, steps, premises)
      case Right((msg, seq)) =>
        proof.InvalidProofTactic(msg)
    }
  }

  /**
   * This function returns a proof of the given sequent if such a proof exists using only the rules of propositional logic and reflexivity and symmetry of equality.
   * Be aware that the runtime and size of the proof may be exponential in the number of atoms (i.e. number of non-propositional subformulas of the input).
   * The strategy consists in leveraging OL formula reduction by alternating between branching on an atom and reducing the formula.
   * @param s A sequent that should be a propositional logic tautology. It can contain binders and schematic connector symbols, but they will be treated as atoms.
   * @return A proof of the given sequent, if it exists
   */
  def solveSequent(s: Sequent): Either[SCProof, (String, Sequent)] = {
    val augSeq = augmentSequent(s)
    val MaRvIn = Variable(freshId(augSeq.formula.freeVariables.map(_.id), "MaRvIn"), Prop) // arbitrary name that is unlikely to already exist in the formula

    try {
      val steps = solveAugSequent(augSeq, 0)(using MaRvIn)
      Left(SCProof((Restate(s, steps.length - 1) :: steps).reverse.toIndexedSeq))
    } catch
      case e: NoProofFoundException =>
        Right(
          (
            "The statement may be incorrect or not provable within propositional logic.\n" +
              "The proof search failed because it needed the truth of the following sequent:\n" +
              s"${e.unsolvable.repr}",
            e.unsolvable
          )
        )

  }

  // From there, private code.

  // Augmented Sequent
  private case class AugSequent(decisions: (List[Expression], List[Expression]), formula: Expression)

  // Transform a sequent into a format more adequate for solving
  private def augmentSequent(s: Sequent): AugSequent = {
    val f = reducedForm(sequentToFormula(s))
    val atoms: scala.collection.mutable.Map[Expression, Int] = scala.collection.mutable.Map.empty
    AugSequent((Nil, Nil), f)
  }

  def reduceSequent(s: Sequent): Expression = {
    val p = simplify(sequentToFormula(s))
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toExpressionAIG(fln)
    res
  }

  // Find all "atoms" of the formula.
  // We mean atom in the propositional logic sense, so any formula starting with a predicate symbol, a binder or a schematic connector is an atom here.
  def findBestAtom(f: Expression): Option[Expression] = {
    val atoms: scala.collection.mutable.Map[Expression, Int] = scala.collection.mutable.Map.empty
    def findAtoms2(fi: Expression, add: Expression => Unit): Unit = fi match {
      case And(f1, f2) => findAtoms2(f1, add); findAtoms2(f2, add)
      case Neg(f1) => findAtoms2(f1, add)
      case _ if fi != top && fi != bot => add(fi)
      case _ => ()
    }
    findAtoms2(f, a => atoms.update(a, { val g = atoms.get(a); if (g.isEmpty) 1 else g.get + 1 }))
    if (atoms.isEmpty) None else Some(atoms.toList.maxBy(_._2)._1)
  }

  private class NoProofFoundException(val unsolvable: Sequent) extends Exception

  // Given a sequent, return a proof of that sequent if on exists that only uses propositional logic rules and reflexivity of equality.
  // Alternates between reducing the formulas using the OL algorithm for propositional logic and branching on an atom using excluded middle.
  // An atom is a subformula of the input that is either a predicate, a binder or a schematic connector, i.e. a subformula that has not meaning in propositional logic.
  private def solveAugSequent(s: AugSequent, offset: Int)(using MaRvIn: Variable): List[SCProofStep] = {
    val redF = reducedForm(s.formula)
    if (redF == top()) {
      List(RestateTrue(s.decisions._1 ++ s.decisions._2.map((f: Expression) => neg(f)) |- s.formula))
    } else
      val bestAtom = findBestAtom(redF)
      if (bestAtom.isEmpty) {
        assert(redF == bot()) // sanity check; If the formula has no atom left in it and is reduced, it should be either ⊤ or ⊥.
        val res = s.decisions._1 |- redF :: s.decisions._2 // the branch that can't be closed
        throw new NoProofFoundException(res)
      } else {
        val atom = bestAtom.get
        val optLambda = findSubformula(redF, MaRvIn, atom)
        if (optLambda.isEmpty) return solveAugSequent(AugSequent(s.decisions, redF), offset)
        val lambdaF = optLambda.get

        val seq1 = AugSequent((atom :: s.decisions._1, s.decisions._2), substituteVariables(lambdaF, Map(MaRvIn -> top)))
        val proof1 = solveAugSequent(seq1, offset)
        val subst1 = RightSubstIff(
          atom :: s.decisions._1 ++ s.decisions._2.map((f: Expression) => neg(f)) |- redF,
          offset + proof1.length - 1,
          Seq((atom, top)),
          (Seq(MaRvIn), lambdaF)
        )
        val negatom = neg(atom)
        val seq2 = AugSequent((negatom :: s.decisions._1, s.decisions._2), substituteVariables(lambdaF, Map(MaRvIn -> bot)))
        val proof2 = solveAugSequent(seq2, offset + proof1.length + 1)
        val subst2 = RightSubstIff(
          negatom :: s.decisions._1 ++ s.decisions._2.map((f: Expression) => neg(f)) |- redF,
          offset + proof1.length + proof2.length + 1 - 1,
          Seq((atom, bot)),
          (Seq(MaRvIn), lambdaF)
        )
        val red2 = Restate(s.decisions._1 ++ s.decisions._2.map((f: Expression) => neg(f)) |- (redF, atom), offset + proof1.length + proof2.length + 2 - 1)
        val cutStep = Cut(s.decisions._1 ++ s.decisions._2.map((f: Expression) => neg(f)) |- redF, offset + proof1.length + proof2.length + 3 - 1, offset + proof1.length + 1 - 1, atom)
        val redStep = Restate(s.decisions._1 ++ s.decisions._2.map((f: Expression) => neg(f)) |- s.formula, offset + proof1.length + proof2.length + 4 - 1)
        redStep :: cutStep :: red2 :: subst2 :: proof2 ++ (subst1 :: proof1)

      }
  }

  private def condflat[T](s: Seq[(T, Boolean)]): (Seq[T], Boolean) = (s.map(_._1), s.exists(_._2))

  private def findSubformula2(outer: Expression, x: Variable, e: Expression, fv: Set[Variable]): (Expression, Boolean) = {
    if (isSame(outer, e)) (x, true)
    else
      val res = outer match {
        case Application(f, arg) =>
          val rf = findSubformula2(f, x, e, fv)
          val ra = findSubformula2(arg, x, e, fv)
          if (rf._2 || ra._2) (Application(rf._1, ra._1), true)
          else (outer, false)
        case Lambda(v, inner) =>
          if (!fv.contains(v)) {
            val induct = findSubformula2(inner, x, e, fv)
            if (!induct._2) (outer, false)
            else (Lambda(v, induct._1), true)
          } else {
            val newv = Variable(freshId((outer.freeVariables ++ fv).map(_.id), v.id), v.sort)
            val newInner = substituteVariables(inner, Map(v -> newv))
            val induct = findSubformula2(newInner, x, e, fv + newv)
            if (!induct._2) (outer, false)
            else (Lambda(newv, induct._1), true)
          }
        case _ => (outer, false)
      }
      // assert(res._1.sort == f.sort, s"Sort mismatch in findSubformula2. ${res._1.repr} : ${res._1.sort} != ${f.repr} : ${f.sort}")
      res
  }

  def findSubformula(f: Expression, x: Variable, e: Expression): Option[Expression] = {
    val r = findSubformula2(f, x, e, e.freeVariables)
    if (r._2) Some(r._1)
    else None
  }

}
