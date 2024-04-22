import lisa.automation.Substitution.{ApplyRules as Substitute}
import lisa.automation.Tableau
import lisa.automation.atp.Goeland
import lisa.automation.Congruence

object Example extends lisa.Main:
  draft()

  val x = variable
  val y = variable
  val P = predicate[1]
  val f = function[1]

  // Simple proof with LISA's DSL
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    val a1 = assume(∀(x, P(x) ==> P(f(x))))
    have(thesis) by Tautology.from(a1 of x, a1 of f(x))
  }

  // Example of set theoretic development

  /**
   * Theorem --- The empty set is a subset of every set.
   *
   *    `|- ∅ ⊆ x`
   */
  val emptySetIsASubset = Theorem(
    ∅ ⊆ x
  ) {
    have((y ∈ ∅) ==> (y ∈ x)) by Weakening(emptySetAxiom of (x := y))
    val rhs = thenHave(∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    have(thesis) by Tautology.from(subsetAxiom of (x := ∅, y := x), rhs)
  }

  /**
   * Theorem --- If a set has an element, then it is not the empty set.
   *
   *    `y ∈ x ⊢ ! x = ∅`
   */
  val setWithElementNonEmpty = Theorem(
    (y ∈ x) |- x =/= ∅
  ) {
    have((x === ∅) |- !(y ∈ x)) by Substitute(x === ∅)(emptySetAxiom of (x := y))
  }

  /**
   * Theorem --- A power set is never empty.
   *
   *   `|- !powerAxiom(x) = ∅`
   */
  val powerSetNonEmpty = Theorem(
    powerSet(x) =/= ∅
  ) {
    have(thesis) by Tautology.from(
      setWithElementNonEmpty of (y := ∅, x := powerSet(x)),
      powerAxiom of (x := ∅, y := x),
      emptySetIsASubset
    )
  }

  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Tableau
  }

  // val a = variable
  // val one = variable
  // val two = variable
  // val * = SchematicFunctionLabel("*", 2)
  // val << = SchematicFunctionLabel("<<", 2)
  // val / = SchematicFunctionLabel("/", 2)
  // private val star: SchematicFunctionLabel[2] = *
  // private val shift: SchematicFunctionLabel[2] = <<
  // private val divide: SchematicFunctionLabel[2] = /

  // extension (t:Term) {
  //   def *(u:Term) = star(t, u)
  //   def <<(u:Term) = shift(t, u)
  //   def /(u:Term) = divide(t, u)
  // }
  // val congruence = Theorem(((a*two) === (a<<one), a*(two/two) === (a*two)/two, (two/two) === one, (a*one) === a) |- ((a<<one)/two) === a) {
  //   have(thesis) by Congruence
  // }

  // import lisa.mathematics.settheory.SetTheory.*

  // Examples of definitions
  val succ = DEF(x) --> union(unorderedPair(x, singleton(x)))
  show

  val inductiveSet = DEF(x) --> in(∅, x) /\ forall(y, in(y, x) ==> in(succ(y), x))
  show

  // Simple tactic definition for LISA DSL

  import lisa.automation.kernel.OLPropositionalSolver.*

  object SimpleTautology extends ProofTactic {
    def solveFormula(using proof: library.Proof)(f: Formula, decisionsPos: List[Formula], decisionsNeg: List[Formula]): proof.ProofTacticJudgement = {
      val redF = reducedForm(f)
      if (redF == ⊤) {
        Restate(decisionsPos |- f :: decisionsNeg)
      } else if (redF == ⊥) {
        proof.InvalidProofTactic("Sequent is not a propositional tautology")
      } else {
        val atom = findBestAtom(redF).get
        def substInRedF(f: Formula) = redF.substituted(atom -> f)
        TacticSubproof {
          have(solveFormula(substInRedF(⊤), atom :: decisionsPos, decisionsNeg))
          val step2 = thenHave(atom :: decisionsPos |- redF :: decisionsNeg) by Substitution2(⊤ <=> atom)
          have(solveFormula(substInRedF(⊥), decisionsPos, atom :: decisionsNeg))
          val step4 = thenHave(decisionsPos |- redF :: atom :: decisionsNeg) by Substitution2(⊥ <=> atom)
          have(decisionsPos |- redF :: decisionsNeg) by Cut(step4, step2)
          thenHave(decisionsPos |- f :: decisionsNeg) by Restate
        }
      }
    }

    def solveSequent(using proof: library.Proof)(bot: Sequent) =
      TacticSubproof { // Since the tactic above works on formulas, we need an extra step to convert an arbitrary sequent to an equivalent formula
        have(solveFormula(sequentToFormula(bot), Nil, Nil))
        thenHave(bot) by Restate.from
      }
  }

  val a = formulaVariable()
  val b = formulaVariable()
  val c = formulaVariable()
  val testTheorem = Lemma((a /\ (b \/ c)) <=> ((a /\ b) \/ (a /\ c))) {
    have(thesis) by SimpleTautology.solveSequent
  }
  show

/**
 * Example showing discharge of proofs using the Goeland theorem prover. Will
 * fail if Goeland is not available on PATH.
 */
object GoelandExample extends lisa.Main:
  val x = variable
  val y = variable
  val P = predicate[1]
  val f = function[1]

  val buveurs2 = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Goeland // ("goeland/Example.buveurs2_sol")
  }
