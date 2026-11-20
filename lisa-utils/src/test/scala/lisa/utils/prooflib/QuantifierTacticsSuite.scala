package lisa.utils.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.prooflib.ProofTacticLib.UnapplicableProofTactic
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes quantifier tactics and checks their deferred failure diagnostics.
 */
class QuantifierTacticsSuite extends AnyFunSuite:
  private object TestLibrary extends Library:
    val theory = new RunningTheory

  import TestLibrary.*
  private given TestLibrary.type = TestLibrary
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val x, y = variable[Ind]
  private val p = variable[Ind >>: Ind >>: Prop]
  private val formula = forall(x, forall(y, p(x)(y)))
  private val source = Theorem(formula |- formula) { have(thesis) by Hypothesis }

  private def check(args: Seq[Expr[Ind]], conclusion: Expr[Prop]): Unit =
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given proof.type = proof
    val expected = formula |- conclusion
    val result = have(InstantiateForallSeq(args)(source)(expected))
    assert(result.statement == expected)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("preserve assumptions through successive capture-avoiding instantiations"):
    check(Seq(y, x), p(y)(x))

  test("preserve the source fact when no arguments are supplied"):
    check(Seq.empty, formula)

  test("instantiate a raw theorem under unrelated ambient assumptions"):
    val reflexivity = Theorem(forall(x, x === x)) {
      have(x === x) by RightRefl
      thenHave(thesis) by RightForall
    }
    for arguments <- Seq(Seq.empty[Expr[Ind]], Seq(y)) do
      val conclusion = if arguments.isEmpty then forall(x, x === x) else y === y
      val checked = Theorem(p(x)(y) |- conclusion) {
        TestLibrary.assume(p(x)(y))
        have(thesis) by InstantiateForallSeq(arguments)(reflexivity)
      }
      assert(!checked.withSorry)

  test("reject a fact with multiple conclusions"):
    val multiple = Theorem(formula |- (formula, p(x)(y))) { have(thesis) by Hypothesis }
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given proof.type = proof
    assert(!InstantiateForallSeq(Seq(x))(multiple)(formula |- p(x)(y)).isValid)

  test("reject more arguments than universal quantifiers"):
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given proof.type = proof
    InstantiateForallSeq(Seq(x, y, x))(source)(formula |- p(x)(y)) match
      case proof.InvalidProofTactic(message) =>
        assert(message.contains("argument #3"))
        assert(message.replace("\r\n", "\n").contains(s"Current intermediate statement:\n  ${formula |- p(x)(y)}"))
      case _ => fail("Expected the third argument to fail")

  test("introduce several quantifiers while preserving source assumptions"):
    val specialized = Theorem(formula |- p(x)(y)) {
      have(thesis) by InstantiateForallSeq(Seq(x, y))(source)
    }
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given proof.type = proof
    val result = have(QuantifiersIntro(Seq(x, y))(specialized)(source.statement))
    assert(result.statement == source.statement)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("quantifier introduction reports the failing variable and formulas"):
    val atom = p(x)(y)
    val identity = Theorem(atom |- atom) { have(thesis) by Hypothesis }
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given proof.type = proof
    val error = intercept[UnapplicableProofTactic] {
      QuantifiersIntro(Seq(x, y))(identity)(atom |- formula)
    }
    val message = error.getMessage.replace("\r\n", "\n")
    assert(message.contains(s"introducing `$y` on the right side"))
    assert(message.contains(s"Current formula:\n  $atom"))
    assert(message.contains(s"Target formula:\n  ${forall(y, atom)}"))
    assert(message.contains("Underlying error:"))

  test("quantifier introduction requires one corresponding source formula"):
    val atom = p(x)(y)
    val other = variable[Prop]
    val identity = Theorem(atom |- atom) { have(thesis) by Hypothesis }
    val twoPremises = Theorem((atom, other) |- atom) { have(thesis) by Hypothesis }
    val twoConclusions = Theorem(atom |- (atom, other)) { have(thesis) by Hypothesis }
    val quantified = forall(x, atom)
    val cases = Seq(
      identity -> ((atom, quantified) |- atom),
      identity -> (atom |- (atom, quantified)),
      twoPremises -> (quantified |- atom),
      twoConclusions -> (atom |- quantified),
      identity -> (quantified |- quantified)
    )
    for (fact, goal) <- cases do
      val proof = new BaseProof(source.asInstanceOf[THMFromProof])
      given proof.type = proof
      QuantifiersIntro(Seq(x))(fact)(goal) match
        case proof.InvalidProofTactic(message) =>
          assert(message.contains("exactly one source formula"))
        case _ => fail("Expected an unsupported quantifier-introduction shape to be rejected")

  test("left quantifier introduction preserves other conclusions"):
    val atom = p(x)(y)
    val other = variable[Prop]
    val identity = Theorem(atom |- (atom, other)) { have(thesis) by Hypothesis }
    val goal = forall(x, atom) |- (atom, other)
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given proof.type = proof
    val result = have(QuantifiersIntro(Seq(x))(identity)(goal))
    assert(result.statement == goal)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("successful diagnostic wrappers do not evaluate their context"):
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given ProofTactic = InstantiateForallSeq
    def unexpected: Nothing = fail("Successful tactics must not evaluate diagnostics")
    val attempted = TacticErrors.attemptOrInvalid(using TestLibrary)(proof)(
      tacticName = "test",
      summary = unexpected,
      factStatement = unexpected,
      bot = unexpected,
      entries = unexpected
    ) { 42 }
    val wrapped = TacticErrors.wrapUnapplicable(using TestLibrary)(proof)(
      tactic = InstantiateForallSeq,
      summary = unexpected,
      factStatement = unexpected,
      bot = unexpected,
      entries = unexpected
    ) { 43 }
    assert(attempted == Right(42))
    assert(wrapped == 43)

  test("failed diagnostic wrappers evaluate context once and retain the underlying error"):
    val proof = new BaseProof(source.asInstanceOf[THMFromProof])
    given ProofTactic = InstantiateForallSeq
    var evaluated = Vector.empty[String]
    def observed[A](label: String, value: A): A =
      evaluated :+= label
      value
    def failure: Nothing = throw UnapplicableProofTactic(InstantiateForallSeq, proof, "original failure")
    def checkMessage(message: String): Unit =
      val normalized = message.replace("\r\n", "\n")
      assert(evaluated.sorted == Seq("entries", "goal", "source", "summary"))
      assert(normalized.contains("failed: context summary"))
      assert(normalized.contains("Detail:\n  context detail"))
      assert(normalized.contains("Underlying error:\n  original failure"))

    TacticErrors.attemptOrInvalid(using TestLibrary)(proof)(
      tacticName = "test",
      summary = observed("summary", "context summary"),
      factStatement = observed("source", source.statement),
      bot = observed("goal", source.statement),
      entries = observed("entries", Seq("Detail" -> "context detail"))
    ) { failure } match
      case Left(proof.InvalidProofTactic(message)) => checkMessage(message)
      case _ => fail("Expected a failed tactic judgement")

    evaluated = Vector.empty
    val error = intercept[UnapplicableProofTactic] {
      TacticErrors.wrapUnapplicable(using TestLibrary)(proof)(
        tactic = InstantiateForallSeq,
        summary = observed("summary", "context summary"),
        factStatement = observed("source", source.statement),
        bot = observed("goal", source.statement),
        entries = observed("entries", Seq("Detail" -> "context detail"))
      ) { failure }
    }
    checkMessage(error.getMessage)
