package lisa.utils.fol

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class SequentSuite extends AnyFunSuite:
  private val x = variable[Ind](K.Identifier("sequent-x", 1))
  private val y = variable[Ind](K.Identifier("sequent-x", 2))
  private val p = variable[Ind >>: Prop](K.Identifier("sequent-p"))

  test("reuse a sequent's kernel conversion without sharing a copy's cache"):
    val original = Sequent(Set(p(x)), Set(p(y)))
    val converted = original.underlying
    assert(converted eq original.underlying)
    val changed = original.copy(left = Set.empty)
    assert(changed.underlying.left.isEmpty)
    assert(changed.underlying.right == converted.right)
    assert(original.underlying eq converted)
    assert(converted.left == Set(p(x).underlying))

  test("convert substituted sequents independently of the source"):
    val original = Sequent(Set(p(x)), Set(p(y)))
    val converted = original.underlying
    val replaced = original.substitute(x := y)
    assert(replaced.underlying.left == Set(p(y).underlying))
    assert(original.underlying eq converted)
    assert(original.underlying.left == Set(p(x).underlying))

  test("hasFree agrees with freeVars across binders and shared subexpressions"):
    val shared = p(x)
    val formulas = Seq(shared, p(y), forall(x, shared), forall(y, shared),
      forall(x, forall(x, shared)), shared /\ forall(x, shared))
    for left <- formulas.combinations(2); right <- formulas; v <- Seq(x, y) do
      val statement = Sequent(left.toSet, Set(right))
      assert(statement.hasFree(v) == statement.freeVars.contains(v))
      assert(statement.hasFree(p) == statement.freeVars.contains(p))
    assert(!Sequent(Set.empty, Set.empty).hasFree(x))
    assert(Sequent(Set(shared), Set.empty).hasFree(x))
    assert(!Sequent(Set.empty, Set(forall(x, shared))).hasFree(x))

  test("hasFree distinguishes identifier indices and sorts"):
    val proposition = variable[Prop](x.id)
    val statement = Sequent(Set(proposition), Set(p(y)))
    assert(statement.hasFree(proposition))
    assert(statement.hasFree(y))
    assert(statement.hasFree(p))
    assert(!statement.hasFree(x))

  test("hasFree respects exact and OL-equivalent removals on either side"):
    val first = exists(x, p(x))
    val second = exists(y, p(y))
    assert(first != second && isSame(first, second))
    val statement = Sequent(Set(first, second), Set.empty)
    assert((statement -<< first).hasFree(p))
    assert(!(statement -<? first).hasFree(p))
    assert((Sequent(Set(first), Set(first)) -<< first).hasFree(p))

  test("hasFree queries kernel support without enumerating frontend variables"):
    val guarded = new Variable[Ind](K.Identifier("sequent-guarded")):
      override def freeVars: Set[Variable[?]] = throw new AssertionError("Frontend traversal")
    val statement = Sequent(Set.empty, Set(p(guarded)))
    assert(statement.hasFree(guarded))
    assert(!statement.hasFree(x))

  test("hasFree remains correct after capture-avoiding substitution"):
    val original = Sequent(Set.empty, Set(forall(x, p(y))))
    val replaced = original.substitute(y := x)
    assert(!original.hasFree(x) && original.hasFree(y))
    assert(replaced.hasFree(x) && !replaced.hasFree(y))
    assert(replaced.hasFree(x) == replaced.freeVars.contains(x))
