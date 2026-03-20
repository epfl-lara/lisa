package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.Quantifiers.∃!

import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.*
import lisa.maths.SetTheory.Base.*
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Ordinals.Integer.{omegaInduction, omegaPredecessor, omegaSuccessor}
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.SimpleDeducedSteps.Generalize
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.BasicStepTactic.RightExists
import lisa.utils.prooflib.BasicStepTactic.RightForall

object UsefullTheorems {

  private val n, m = variable[Ind]
  private val s, t, d = variable[Ind]
  private val x, y, z = variable[Ind]
  private val f, g, h = variable[Ind]
  private val p1, p2, p3 = variable[Prop]
  private val q1, q2 = variable[Prop]
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

  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2){
    have(thesis) by Tautology
  }

  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2){
    have(thesis) by Tautology
  }

  val equivalenceAnd = Lemma((p2, p1 <=> (p2 /\ p3)) |- p1 <=> p3){
    have(thesis) by Tautology
  }

  val disjunctionsImplies = Lemma((p1 ==> p2, q1 ==> q2) |- (p1 \/ q1) ==> (p2 \/ q2)) {

    val right = have((p1 ==> p2, q1 ==> q2, p1) |- p2 \/ q2) by Restate
    val left = have((p1 ==> p2, q1 ==> q2, q1) |- p2 \/ q2) by Restate

    have((p1 ==> p2, q1 ==> q2, p1 \/ q1) |- p2 \/ q2) by LeftOr(left, right)
  }

  val unionPreimageMonotonic = Lemma(
    (subset(s, t), P(s) ==> P(t)) |- (P(s) \/ in(x, s)) ==> (P(t) \/ in(x, t))
  ){
    have(subset(s, t) |- forall(z, in(z, s) ==> in(z, t))) by Cut(
      subsetAxiom of (x := s, y := t),
      equivalenceApply of (p1 := subset(s, t), p2 := forall(z, in(z, s) ==> in(z, t)))
    )
    thenHave(subset(s, t) |- in(x, s) ==> in(x, t)) by InstantiateForall(x)
    have(thesis) by Cut(lastStep, disjunctionsImplies of (p1 := in(x, s), p2 := in(x, t), q1 := P(s), q2 := P(t)))
  }

  val unionMonotonic = Lemma(subset(x, y) |- subset(⋃(x), ⋃(y))) {
    have(z ∈ b /\ b ∈ x |- z ∈ b /\ b ∈ x ) by Hypothesis
    thenHave(subset(x, y) /\ z ∈ b /\ b ∈ x |- b ∈ x ) by Weakening
    
    // Extract the forall version from the subset equivalence
    have(subset(x, y) |- forall(b, in(b, x) ==> in(b, y))) by Cut(
      subsetAxiom of (x := x, y := y),
      equivalenceApply of (p1 := subset(x, y), p2 := forall(b, in(b, x) ==> in(b, y)))
    )
    
    // Instantiate the universal quantifier with b
    thenHave(subset(x, y) |- in(b, x) ==> in(b, y)) by InstantiateForall(b)
    
    // Apply modus ponens
    have(subset(x, y) /\ in(b, x) |- in(b, y)) by Tautology.from(lastStep)
    have(subset(x, y) /\ z ∈ b /\ b ∈ x |- b ∈ y ) by Tautology.from(lastStep)
    
    have(subset(x, y) /\ z ∈ b /\ b ∈ x |- z ∈ b /\ b ∈ y ) by Tautology.from(lastStep)
    thenHave(subset(x, y) /\ z ∈ b /\ b ∈ x |- exists(a, z ∈ a /\ a ∈ y)) by RightExists
    thenHave(z ∈ b /\ b ∈ x |- subset(x, y) ==> exists(a, z ∈ a /\ a ∈ y)) by Tautology
    thenHave(exists(b, z ∈ b /\ b ∈ x) |- subset(x, y) ==> exists(a, z ∈ a /\ a ∈ y)) by LeftExists
    have(z ∈ ⋃(x) |- subset(x, y) ==> exists(a, z ∈ a /\ a ∈ y)) by 
      Tautology.from(lastStep, ⋃.definition of (x := x, y := b, z := z))
    have(z ∈ ⋃(x) |- subset(x, y) ==> z ∈ ⋃(y)) by 
      Tautology.from(lastStep, ⋃.definition of (x := y, y := b, z := z))
    have(subset(x, y) |- z ∈ ⋃(x) ==> z ∈ ⋃(y)) by Tautology.from(lastStep)
    thenHave(subset(x, y) |- forall(z,z ∈ ⋃(x) ==> z ∈ ⋃(y))) by RightForall
    have(thesis) by Tautology.from(lastStep, Subset.definition of (x := ⋃(x), y := ⋃(y)))
  }

  val rangeMonotonic = Lemma(subset(f, g) |- subset(Relation.range(f), Relation.range(g))) {
    have(thesis) by Sorry
  }

  val unionRangeMonotonic = Lemma(subset(f, g) |- subset(⋃(Relation.range(f)), ⋃(Relation.range(g)))){

    val rf = Relation.range(f)
    val rg = Relation.range(g)

    have(
      subset(rf, rg) ==> subset(⋃(rf), ⋃(rg))
    ) by Tautology.from(
      unionMonotonic of (x := rf, y := rg)
    )
    have(subset(f, g) |- subset(⋃(rf), ⋃(rg))) by Tautology.from(
      lastStep, rangeMonotonic
    )
    thenHave(thesis) by Restate
  }

  val subsetNotEmpty = Lemma((subset(x, y), !(x === ∅)) |- !(y === ∅)){
    val subst = have(y === ∅ |- y === ∅) by Hypothesis
    have((subset(x, ∅), y === ∅) |- (x === ∅)) by Tautology.from(
      equivalenceApply of (p1 := subset(x, ∅)),Subset.rightEmpty)
    have((subset(x, y), y === ∅) |- (x === ∅)) by Congruence.from(subst, lastStep)
  }

  val nInSuccN = Lemma( n ∈ successor(n) ){
    val sn = ∪(n)(Singleton.singleton(n))
    have( n ∈ Singleton.singleton(n) ) by Tautology.from(Singleton.membership of (x := n, y := n))
    have( n ∈ sn ) by Tautology.from(
      lastStep,
      Union.membership of (x := n, y := Singleton.singleton(n), z := n)
    )
    have(thesis) by Congruence.from(lastStep, successor.definition of (x := n))
  }

  val successorInjectivity = Lemma((n === m) <=> (successor(n) === successor(m))){

    val forward = have(n === m |- successor(n) === successor(m)) by Congruence

    val h = successor(n) === successor(m) 
    val eq = have(h |- successor(n) === successor(m)) by Hypothesis

    have(h /\ in(z, n) |- in(z, successor(n))) by Sorry 
    // Tautology.from(
    //   successor.definition of (n := n, m := m), 
    //   UnorderedPair.leftInPair of (x := z, y := Singleton.singleton(n))
    // )
    have(h /\ in(z, n) |- in(z, successor(m))) by Congruence.from(lastStep, eq)

    have(h /\ in(z, n) |- in(z, m)) by Sorry
    have(h |- in(z, n) ==> in(z, m)) by Tautology.from(lastStep)
    thenHave(h |- forall(z, in(z, n) ==> in(z, m))) by RightForall
    val incl = have(h |- subset(n, m)) by Tautology.from(lastStep, subsetAxiom of (x := n, y := m))

    thenHave(h ==> subset(n, m)) by Restate
    thenHave(forall(n, forall(m, h ==> subset(n, m)))) by Generalize
    val revIncl = thenHave(h |- subset(m, n)) by InstantiateForall(m, n)

    val backward = have(h |- n === m) by Tautology.from(
      Subset.doubleInclusion of (x := n, y := m),
      incl, revIncl
    )

    have(thesis) by Tautology.from(forward, backward)
  }
  

  val zeroIsNotSucc = Lemma(!(successor(n) === ∅)){
    val sn = ∪(n)(Singleton.singleton(n))
    have( n ∈ Singleton.singleton(n) ) by Tautology.from(Singleton.membership of (x := n, y := n))
    have( n ∈ sn ) by Tautology.from(
      lastStep,
      Union.membership of (x := n, y := Singleton.singleton(n), z := n)
    )
    have(sn =/= ∅) by Tautology.from(lastStep, EmptySet.setWithElementNonEmpty of (x := n, y := sn))
    have(successor(n) =/= ∅) by Congruence.from(lastStep, successor.definition of (x := n))
  }

  val zeroIsNat = Lemma(in(∅, N)){
    have(thesis) by Sorry
  }

  val natNotEmpty = Lemma(!(N === ∅)){
    have(thesis) by Sorry
  }

  val successorIsNat = Lemma(in(n, N) <=> in(successor(n), N)){
    val α = variable[Ind]
    val eqSucc = have(S(n) === successor(n)) by Congruence.from(
      S.definition of (α := n),
      successor.definition of (x := n)
    )

    val toS = have(in(n, N) |- in(S(n), N)) by Restate.from(omegaSuccessor of (α := n))
    val fromS = have(in(S(n), N) |- in(n, N)) by Restate.from(omegaPredecessor of (α := n))

    val toSuccConv = have(in(S(n), N) |- in(successor(n), N)) by Congruence.from(eqSucc)
    val fromSuccConv = have(in(successor(n), N) |- in(S(n), N)) by Congruence.from(eqSucc)

    val toSucc = have(in(n, N) |- in(successor(n), N)) by Cut(toS, toSuccConv)
    val fromSucc = have(in(successor(n), N) |- in(n, N)) by Cut(fromSuccConv, fromS)

    have(thesis) by Tautology.from(toSucc, fromSucc)
  }

  val natInduction = Lemma((P(∅), forall(m, in(m, N) ==> (P(m) ==> P(successor(m))))) |- forall(n, in(n, N) ==> P(n))) {
    val α = variable[Ind]
    val eqSucc = have(S(m) === successor(m)) by Congruence.from(
      S.definition of (α := m),
      successor.definition of (x := m)
    )

    val stepS = have(
      forall(m, in(m, N) ==> (P(m) ==> P(successor(m)))) |-
        forall(m, in(m, N) ==> (P(m) ==> P(S(m))))
    ) subproof {
      assume(forall(m, in(m, N) ==> (P(m) ==> P(successor(m)))))
      thenHave(in(m, N) ==> (P(m) ==> P(successor(m)))) by InstantiateForall(m)
      have(in(m, N) ==> (P(m) ==> P(S(m)))) by Congruence.from(lastStep, eqSucc)
      thenHave(forall(m, in(m, N) ==> (P(m) ==> P(S(m))))) by RightForall
    }

    have(thesis) by Tautology.from(omegaInduction, stepS)
  }

  val subsetIsNat = Lemma(subset(x, y) |- in(y, N) ==> in(x, N)){

    have(subset(x, y) /\ in(y, N) |- in(x, N)) by Sorry
    
    have(thesis) by Tautology.from(lastStep)
  }

  val subsetSuccessor = Lemma(subset(n, successor(n))){
    val succExpanded = ∪(n)(Singleton.singleton(n))

    have(subset(n, succExpanded)) by Tautology.from(
      Union.leftSubset of (x := n, y := Singleton.singleton(n))
    )
    have(subset(n, n) |- subset(n, successor(n))) by
      Congruence.from(lastStep, successor.definition of (x := n))
    have(thesis) by Cut(
      Subset.reflexivity of (x := n),
      lastStep
    )
  }

  val restrictedFunctionEmptyDomain =
    Lemma(restrictedFunction(h, ∅) === ∅){
    have(thesis) by Sorry
  }

  val restrictedFunctionNotEmpty = Lemma(
    (!(h === ∅), !(d === ∅)) |- !(restrictedFunction(h, d) === ∅)
  ){
    have(thesis) by Sorry
  }

  val nonEmptyDomain =
    Lemma(!(relationDomain(h) === ∅) |- !(h === ∅)){
    have(thesis) by Sorry
  }

  val restrictedFunctionDomainMonotonic = Lemma(
    subset(x, y) |- subset(restrictedFunction(f, x), restrictedFunction(f, y))
  ){
    have(thesis) by Sorry
  }

  val unionRangeCumulativeRestrictedFunction = Lemma(
    (
      functional(h),
      in(n, N),
      relationDomain(h) === N,
      forall(m, subset(m, n) ==> subset(app(h)(m), app(h)(n)))
    ) |- unionRange(restrictedFunction(h, successor(n))) === app(h)(n)
  ){
    have(thesis) by Sorry
  }

  val existsOneUniqueness =
    Lemma((∃!(x, P(x)), P(x), P(y)) |- x === y){
    have(thesis) by Sorry
  }

  val altEqualityTransitivity =
    Lemma((x === y, y === z) |- x === z){
    have(thesis) by Congruence
  }

  val equivalenceRewriting =
    Lemma((p1 <=> p2, p2 <=> p3) |- (p1 <=> p3)){
    have(thesis) by Tautology
  }

  val impliesEquivalence = Lemma((p1 <=> p2, p3 <=> p4) |- (p1 ==> p3) <=> (p2 ==> p4)) {
    have(thesis) by Tautology
  }

  val leftImpliesEquivalenceWeak =
    Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2)){
    have(thesis) by Tautology
  }

  val leftImpliesEquivalenceStrong =
    Lemma(p ==> (p1 <=> p2) |- (p ==> p1) <=> (p ==> p2)){
    have(thesis) by Tautology
  }

  val existsNeg = Lemma(∃(x, !P(x)) |- !(forall(x, P(x)))) {
    have(thesis) by Tautology
  }

}
