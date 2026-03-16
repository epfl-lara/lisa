package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.Quantifiers.∃!

import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.*

object UsefullTheorems {

  private val n, m = variable[Ind]
  private val s, t, d = variable[Ind]
  private val x, y, z = variable[Ind]
  private val f, g, h = variable[Ind]
  private val p1, p2, p3 = variable[Prop]
  private val P = variable[Ind >>: Prop]

  /**
   *  ATTENTION : THE FILES IN SetTheory/Types/ADT CANNOT BE USED
   *
   *  ADT/ is deprecated and should not be used But the files are still here for reference
   */

  object QuantifiersIntro extends lisa.utils.prooflib.ProofTacticLib.ProofTactic {

    /**
     *  Executes the tactic on a specific goal.
     *
     *  @param lib the library that is currently being used
     *  @param proof the ongoing proof in which the tactic is called
     *  @param vars the variables that needs to be quantified
     *  @param fact the proof of the sequent without quantification
     *  @param bot the statement to prove
     */
    def apply(using
        lib: lisa.utils.prooflib.Library,
        proof: lib.Proof
    )(vars: Seq[Variable[Ind]])(
        fact: proof.Fact
    )(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof { sp ?=>
      if vars.isEmpty then lib.have(bot) by Restate.from(fact)
      else
        val diff: Sequent = bot -- fact.statement

        diff match
          case Sequent(s, _) if s.size == 1 =>
            val diffRest = bot.left -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.left -- diffRest).head
            f match
              case ∀(_, _) => vars
                  .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                    val (accFact, accFormula) = acc
                    val newFormula = ∀(v, accFormula)
                    (
                      lib.have(diffRest + newFormula |- bot.right) by LeftForall(accFact),
                      newFormula
                    )
                  }
              case ∃(_, _) => vars
                  .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                    val (accFact, accFormula) = acc
                    val newFormula = ∃(v, accFormula)
                    (
                      lib.have(diffRest + newFormula |- bot.right) by LeftExists(accFact),
                      newFormula
                    )
                  }
              case _ => return proof
                  .InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(_, s) if s.size == 1 =>
            val diffRest = bot.right -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.right -- diffRest).head
            f match
              case ∀(_, _) => vars
                  .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                    val (accFact, accFormula) = acc
                    val newFormula = forall(v, accFormula)
                    (
                      lib.have(bot.left |- diffRest + newFormula) by RightForall(accFact),
                      newFormula
                    )
                  }
              case ∃(_, _) => vars
                  .foldRight[(sp.Fact, Expr[Prop])](fact, fWithoutQuant) { (v, acc) =>
                    val (accFact, accFormula) = acc
                    val newFormula = exists(v, accFormula)
                    (
                      lib.have(bot.left |- diffRest + newFormula) by RightExists(accFact),
                      newFormula
                    )
                  }
              case _ => return proof
                  .InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty =>
            lib.have(bot) by Restate.from(fact)
          case _ => return proof
              .InvalidProofTactic("Two or more formulas in the sequent have changed.")

    }

  }

  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2)(have(thesis) by Tautology)

  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2)(have(thesis) by Tautology)

  val equivalenceAnd =
    Lemma((p2, p1 <=> (p2 /\ p3)) |- p1 <=> p3)(have(thesis) by Tautology)

  val unionPreimageMonotonic = Lemma(
    (subset(s, t), P(s) ==> P(t)) |- (P(s) \/ in(x, s)) ==> (P(t) \/ in(x, t))
  )(have(thesis) by Sorry)

  val unionRangeMonotonic =
    Lemma(subset(f, g) |- subset(unionRange(f), unionRange(g)))(have(thesis) by Sorry)

  val subsetNotEmpty =
    Lemma((subset(x, y), !(x === ∅)) |- !(y === ∅))(have(thesis) by Sorry)

  val successorInjectivity =
    Lemma((n === m) <=> (successor(n) === successor(m)))(have(thesis) by Sorry)

  val zeroIsNotSucc = Lemma(!(successor(n) === ∅))(have(thesis) by Sorry)

  val zeroIsNat = Lemma(in(∅, N))(have(thesis) by Sorry)

  val natNotEmpty = Lemma(!(N === ∅))(have(thesis) by Sorry)

  val successorIsNat = Lemma(in(n, N) <=> in(successor(n), N))(have(thesis) by Sorry)

  val subsetIsNat = Lemma(subset(x, y) |- in(y, N) ==> in(x, N))(have(thesis) by Sorry)

  val subsetSuccessor = Lemma(subset(n, successor(n)))(have(thesis) by Sorry)

  val restrictedFunctionEmptyDomain = Lemma(restrictedFunction(h, ∅) === ∅)(have(thesis) by Sorry)

  val restrictedFunctionNotEmpty = Lemma(
    (!(h === ∅), !(d === ∅)) |- !(restrictedFunction(h, d) === ∅)
  ){have(thesis) by Sorry}

  val nonEmptyDomain = Lemma(!(relationDomain(h) === ∅) |- !(h === ∅)){
    have(thesis) by Sorry
  }

  val restrictedFunctionDomainMonotonic = Lemma(
    subset(x, y) |- subset(restrictedFunction(f, x), restrictedFunction(f, y))
  )(have(thesis) by Sorry)

  val unionRangeCumulativeRestrictedFunction = Lemma(
    (
      functional(h),
      in(n, N),
      relationDomain(h) === N,
      forall(m, subset(m, n) ==> subset(app(h)(m), app(h)(n)))
    ) |- unionRange(restrictedFunction(h, successor(n))) === app(h)(n)
  )(have(thesis) by Sorry)

  val existsOneUniqueness =
    Lemma((∃!(x, P(x)), P(x), P(y)) |- x === y)(have(thesis) by Sorry)


  val altEqualityTransitivity = Lemma(
    (x === y, y === z) |- x === z
  ){
    have(thesis) by Sorry
  }

  val equivalenceRewriting = Lemma((p1 <=> p2, p2 <=> p3) |- (p1 <=> p3)){
    have(thesis) by Sorry
  }

  val impliesEquivalence = Lemma((p1 <=> p2, p3 <=> p4) |- (p1 ==> p3) <=> (p2 ==> p4)) {
    have(thesis) by Tautology
  }

  val leftImpliesEquivalenceWeak = Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2)) {
    have(thesis) by Tautology
  }

  val leftImpliesEquivalenceStrong = Lemma(p ==> (p1 <=> p2) |- (p ==> p1) <=> (p ==> p2)) {
    have(thesis) by Tautology
  }

}
