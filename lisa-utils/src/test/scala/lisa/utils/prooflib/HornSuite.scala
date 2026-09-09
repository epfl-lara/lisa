package lisa.utils.prooflib

import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class HornSuite extends AnyFunSuite:

  given testLibrary: Library = new Library

  private val a = variable[Prop]
  private val b = variable[Prop]
  private val c = variable[Prop]
  private val d = variable[Prop]

  private def sorry(statement: Sequent): Thm =
    BasicStep.Sorry(statement).destruct._1

  private def assertValid(judgement: ProofJudgement): Unit =
    assert(judgement.isValid, judgement.errors.map(_.message).mkString("\n"))

  test("HornSolver derives a multi-step consequence"):
    val clauses = IndexedSeq(
      HornSolver.Clause(Vector("a"), "b"),
      HornSolver.Clause(Vector("b", "c"), "d")
    )
    val result = HornSolver.solve(Seq("a", "c"), clauses, Seq("d"))(identity)
    assert(result.goal.contains("d"))
    assert(result.derived == Vector("a", "c", "b", "d"))

  test("HornSolver terminates on an unreachable cycle"):
    val clauses = IndexedSeq(
      HornSolver.Clause(Vector("a"), "b"),
      HornSolver.Clause(Vector("b"), "a")
    )
    val result = HornSolver.solve(Seq.empty, clauses, Seq("b"))(identity)
    assert(!result.reached)
    assert(result.derived.isEmpty)

  test("HornSolver uses the supplied cut key"):
    val clauses = IndexedSeq(HornSolver.Clause(Vector("A"), "B"))
    val result = HornSolver.solve(Seq("a"), clauses, Seq("b"))(_.toLowerCase)
    assert(result.reached)
    assert(result.derived == Vector("a", "B"))

  test("HornSolver fires facts with empty bodies"):
    val clauses = IndexedSeq(
      HornSolver.Clause(Vector.empty, "a"),
      HornSolver.Clause(Vector("a"), "b")
    )
    val result = HornSolver.solve(Seq.empty, clauses, Seq("b"))(identity)
    assert(result.goal.contains("b"))

  test("Horn reconstructs a chain of cuts"):
    val ab = sorry(a |- b)
    val bc = sorry(b |- c)
    assertValid(Horn.from(ab, bc)(a |- c))

  test("Horn keeps initial assumptions instead of cutting them"):
    val abc = sorry((a, b) |- c)
    val ab = sorry(a |- b)
    assertValid(Horn.from(abc, ab)(a |- c))

  test("Horn reconstructs empty-body facts"):
    val fact = sorry(() |- a)
    val rule = sorry(a |- b)
    assertValid(Horn.from(fact, rule)(() |- b))

  test("Horn rejects unreachable goals"):
    val judgement = Horn.from(sorry(a |- b))(c |- b)
    assert(!judgement.isValid)

  test("Horn rejects non-definite premises"):
    val judgement = Horn.from(sorry(a |- (b, c)))(a |- b)
    assert(!judgement.isValid)
    assert(judgement.errors.exists(_.message.contains("not definite")))

  test("Horn can select cuts modulo OL"):
    val rule = sorry((a /\ b) |- c)
    assert(!Horn.from(rule)((b /\ a) |- c).isValid)
    assertValid(Horn.withCutKey(Horn.CutKey.OL)(rule)((b /\ a) |- c))
