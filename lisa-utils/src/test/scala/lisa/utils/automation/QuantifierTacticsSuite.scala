package lisa.utils.automation

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.BasicStep
import lisa.utils.prooflib.Lemma
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.ProofHelpers
import lisa.utils.prooflib.ProofHelpers._
import lisa.utils.prooflib.ProofJudgement
import lisa.utils.prooflib.StringOutputManager
import lisa.utils.prooflib.Theorem
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks quantifier tactics through LCF proof carriers, including invalid inputs.
 */
class QuantifierTacticsSuite extends AnyFunSuite:
  private given Library = new Library
  private given OutputManager = new StringOutputManager
  private val x, y = variable[Ind]
  private val p = variable[Ind >>: Ind >>: Prop]
  private val formula = forall(x, forall(y, p(x)(y)))
  private val source = BasicStep.Hypothesis(formula |- formula).thm

  private def assertProved(result: ProofJudgement, expected: Sequent): Unit =
    assert(result.isValid, result.toString)
    assert(result.thm.statement == expected)
    assert(!result.thm.kernel.usesSorry)

  test("preserve assumptions through capture-avoiding instantiation and empty arguments"):
    for (args, conclusion) <- Seq(Seq(y, x) -> p(y)(x), Seq.empty[Expr[Ind]] -> formula) do
      val goal = formula |- conclusion
      assertProved(InstantiateForallSeq(args)(source)(goal), goal)

  test("instantiate under unrelated ambient assumptions"):
    val reflexivity = Theorem.generated(forall(x, x === x)) {
      have(x === x) by BasicStep.RightRefl
      thenHave(thesis) by BasicStep.RightForall
    }
    for args <- Seq(Seq.empty[Expr[Ind]], Seq(y)) do
      val goal = p(x)(y) |- (if args.isEmpty then forall(x, x === x) else y === y)
      val checked = Theorem.generated(goal) {
        ProofHelpers.assume(p(x)(y))
        have(thesis) by InstantiateForallSeq(args)(reflexivity)
      }
      assertProved(checked.judgement, goal)

  test("reject multiple conclusions and excess arguments"):
    val multiple = BasicStep.Hypothesis(formula |- (formula, p(x)(y))).thm
    assert(!InstantiateForallSeq(Seq(x))(multiple)(formula |- p(x)(y)).isValid)
    assert(!InstantiateForallSeq(Seq(x, y, x))(source)(formula |- p(x)(y)).isValid)

  test("introduce universal quantifiers while preserving assumptions"):
    val specialized = source.of(x, y)
    assertProved(QuantifiersIntro(Seq(x, y))(specialized)(source.statement), source.statement)

  test("reject quantification of a variable free in the remaining context"):
    val atom = p(x)(y)
    val identity = BasicStep.Hypothesis(atom |- atom).thm
    assert(!QuantifiersIntro(Seq(x, y))(identity)(atom |- formula).isValid)

  test("require exactly one formula replaced on one side"):
    val atom = p(x)(y)
    val other = variable[Prop]
    val identity = BasicStep.Hypothesis(atom |- atom).thm
    val twoPremises = BasicStep.Hypothesis((atom, other) |- atom).thm
    val twoConclusions = BasicStep.Hypothesis(atom |- (atom, other)).thm
    val quantified = forall(x, atom)
    for (fact, goal) <- Seq(
        identity -> ((atom, quantified) |- atom),
        identity -> (atom |- (atom, quantified)),
        twoPremises -> (quantified |- atom),
        twoConclusions -> (atom |- quantified),
        identity -> (quantified |- quantified)
      )
    do assert(!QuantifiersIntro(Seq(x))(fact)(goal).isValid)

  test("left introduction preserves other conclusions"):
    val atom = p(x)(y)
    val other = variable[Prop]
    val identity = BasicStep.Hypothesis(atom |- (atom, other)).thm
    val goal = forall(x, atom) |- (atom, other)
    assertProved(QuantifiersIntro(Seq(x))(identity)(goal), goal)

  test("introduce existential quantifiers on either side"):
    val atom = p(x)(y)
    val identity = BasicStep.Hypothesis(atom |- atom).thm
    val rightGoal = atom |- exists(x, exists(y, atom))
    assertProved(QuantifiersIntro(Seq(x, y))(identity)(rightGoal), rightGoal)
    val tautology = BasicStep.Hypothesis((atom, p(y)(x)) |- p(y)(x)).thm
    val leftGoal = (exists(x, atom), p(y)(x)) |- p(y)(x)
    assert(!QuantifiersIntro(Seq(x))(tautology)(leftGoal).isValid)

  test("explicit theorem names retain their proof and registry entry"):
    val named = Theorem.named("generated/example")(x === x) {
      have(thesis) by BasicStep.RightRefl
    }
    assertProved(named.judgement, () |- x === x)
    assert(summon[Library].theorems.getFull("generated/example").contains(named))

  test("generated theorems from the same source retain distinct registry entries"):
    val generated = (1 to 2).map { _ =>
      Lemma.generated(x === x) { have(thesis) by BasicStep.RightRefl }
    }
    assert(generated.map(_.fullName.value).distinct.size == 2)
    for theorem <- generated do
      assertProved(theorem.judgement, () |- x === x)
      assert(summon[Library].theorems.getFull(theorem.fullName.value).contains(theorem))
