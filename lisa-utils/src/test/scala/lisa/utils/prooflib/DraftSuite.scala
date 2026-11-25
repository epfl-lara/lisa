package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers._
import org.scalatest.funsuite.AnyFunSuite

class DraftSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager
  private val p = variable[Prop]

  private def configured(target: Option[String]): Library =
    val previous = sys.props.get("lisa.draft.target")
    try
      target match
        case Some(value) => sys.props.update("lisa.draft.target", value)
        case None => sys.props.remove("lisa.draft.target")
      new Library
    finally
      previous match
        case Some(value) => sys.props.update("lisa.draft.target", value)
        case None => sys.props.remove("lisa.draft.target")

  test("normal mode executes and checks theorem bodies"):
    given Library = configured(None)
    var executed = false
    val theorem = Theorem.named("example.Dependency.identity")(p |- p) {
      executed = true
      have(thesis) by BasicStep.Hypothesis
    }
    assert(executed && !theorem.isDraft && !theorem.thm.usesSorry)
    assert(theorem.errors.isEmpty)

  test("draft mode never evaluates omitted theorem bodies"):
    given library: Library = configured(Some("example.Target"))
    for kind <- Seq[TheoremKind](Theorem, Lemma, Corollary) do
      val theorem = kind.named(s"example.Dependency.$kind")(p) {
        throw new AssertionError("An omitted proof was evaluated")
      }
      assert(theorem.isDraft && theorem.thm.usesSorry && theorem.errors.isEmpty)
      assert(theorem.statement == (() |- p))
      assert(theorem.kernel.assumptions.isEmpty && theorem.kernel.axioms.isEmpty)
      assert(library.theorems.getFull(theorem.fullName.value).contains(theorem))

  test("a selected module checks its proofs after dependencies initialize"):
    given Library = configured(Some("example.Target"))
    object Dependency:
      val theorem = Theorem.named("example.Dependency.identity")(p |- p) {
        throw new AssertionError("The dependency proof was evaluated")
      }
    object Target:
      val imported = Dependency.theorem
      var executed = false
      val theorem = Theorem.named("example.Target.identity")(p |- p) {
        executed = true
        have(imported)
      }
    assert(Target.executed && !Target.theorem.isDraft)
    assert(Target.imported.isDraft && Target.theorem.thm.usesSorry)
    assert(Target.theorem.errors.isEmpty)

  test("prefix selection checks package members but not neighboring names"):
    given Library = configured(Some("example.Target"))
    val selected = Theorem.named("example.Target.Nested.identity")(p |- p) { have(thesis) by BasicStep.Hypothesis }
    val neighbor = Theorem.named("example.TargetOther.identity")(p) { throw new AssertionError("Neighbor proof was evaluated") }
    assert(!selected.isDraft && !selected.thm.usesSorry)
    assert(neighbor.isDraft && neighbor.thm.usesSorry)

  test("selected proof failures still produce diagnostics"):
    given Library = configured(Some("example.Target"))
    val theorem = Theorem.named("example.Target.failure")(p) { ProofCarrier.Failure("selected proof failed") }
    assert(!theorem.isDraft && theorem.thm.usesSorry)
    assert(theorem.errors.exists(_.message.contains("selected proof failed")))

  test("selected proofs still reject unresolved kernel assumptions"):
    given library: Library = configured(Some("example.Target"))
    val statement = p |- p
    val open = lisa.kernel.proof.Assume(using library.theory)(statement.underlying).toOption.get
    val theorem = Theorem.named("example.Target.open")(statement) { have(open) }
    assert(!theorem.isDraft && theorem.thm.usesSorry)
    assert(theorem.errors.exists(_.message.contains("unresolved kernel assumptions")))
    assert(theorem.kernel.assumptions.isEmpty)

  test("draft mode still checks definitions"):
    given library: Library = configured(Some("example.Target"))
    val x = variable[Ind]
    val (identity, definition) = library.define("example.Dependency.identity", λ(x, x))
    assert(library.defines(identity) && !definition.usesSorry)
    assert(library.contains(identity))
