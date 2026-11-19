package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import scala.util.Random

class TautologySuite extends AnyFunSuite:
  given Library = new Library

  private val p, q, r, s = variable[Prop]
  private val atoms = Vector(p, q, r, s)

  private def check(statement: Sequent, expected: Boolean): Unit =
    val result = Tautology(statement)
    assert(result.isValid == expected, s"Tautology: $statement\n${result.errors}")
    assert(Tautology.solveSequent(statement.underlying).isLeft == expected)
    if expected then
      assert(result.kernel.statement == statement.underlying)
      assert(!result.kernel.usesSorry)
      assert(result.kernel.axioms.isEmpty && result.kernel.assumptions.isEmpty)
    else assert(result.justification.isEmpty && result.errors.nonEmpty)

  test("direct rules cover connectives, constants, duplicates and branching"):
    val statements = Seq(
      p |- p,
      (p, p ==> q) |- q,
      (p, p ==> q, q ==> r) |- r,
      (p /\ q) |- p,
      (p, q) |- (p /\ q),
      p |- (p \/ q),
      (p \/ q) |- (q \/ p),
      () |- (p \/ !p),
      (p, !p) |- (),
      () |- ((p ==> q) <=> (!q ==> !p)),
      (p <=> q, p) |- q,
      ((p \/ q) /\ (p \/ q)) |- (q \/ p),
      () |- ((p /\ (q \/ r)) <=> ((p /\ q) \/ (p /\ r))),
      () |- (((p ==> q) ==> p) ==> p),
      () |- top,
      bot |- (),
      () |- (top <=> !bot)
    )
    statements.foreach(check(_, true))
    Seq(() |- p, p |- q, () |- bot, top |- bot, (p \/ q) |- p, p |- (p /\ q)).foreach(check(_, false))

  test("seeded sequents agree with truth tables"):
    val random = new Random(0x715a)
    def formula(depth: Int): Expr[Prop] =
      if depth == 0 then atoms(random.nextInt(atoms.size))
      else
        random.nextInt(7) match
          case 0 => top
          case 1 => bot
          case 2 => !formula(depth - 1)
          case 3 => formula(depth - 1) /\ formula(depth - 1)
          case 4 => formula(depth - 1) \/ formula(depth - 1)
          case 5 => formula(depth - 1) ==> formula(depth - 1)
          case _ => formula(depth - 1) <=> formula(depth - 1)

    def evaluate(formula: Expr[Prop], valuation: Int): Boolean = formula match
      case `top` => true
      case `bot` => false
      case neg(a) => !evaluate(a, valuation)
      case a /\ b => evaluate(a, valuation) && evaluate(b, valuation)
      case a \/ b => evaluate(a, valuation) || evaluate(b, valuation)
      case a ==> b => !evaluate(a, valuation) || evaluate(b, valuation)
      case a <=> b => evaluate(a, valuation) == evaluate(b, valuation)
      case atom => (valuation & (1 << atoms.indexOf(atom))) != 0

    for _ <- 0 until 400 do
      val statement = Sequent(Set.fill(random.nextInt(3))(formula(3)), Set.fill(random.nextInt(3))(formula(3)))
      val valid = (0 until 16).forall(valuation => !statement.left.forall(evaluate(_, valuation)) || statement.right.exists(evaluate(_, valuation)))
      check(statement, valid)

  test("opaque atoms retain kernel equality and lambda normalization"):
    val x, y = variable[Ind]
    val P = variable[Ind >>: Prop]
    val f = variable[Prop >>: Prop]
    val statements = Seq(
      () |- (x === x),
      (x === y) |- (y === x),
      ∀(x, P(x) /\ top) |- ∀(y, P(y)),
      ∃(x, P(x)) |- !(∀(y, !P(y))),
      f(p /\ q) |- f(q /\ p),
      App(λ(p, p /\ (q \/ r)), s) |- ((s /\ q) \/ (s /\ r))
    )
    statements.foreach(check(_, true))
    check(∀(x, P(x)) |- P(y), false)

  test("premise reconstruction preserves dependencies and caller assumptions"):
    val theory = summon[Library].theory
    def assume(statement: Sequent): Thm = Thm(lisa.kernel.proof.Assume(using theory)(statement.underlying).toOption.get)
    val first = assume(p |- q)
    val second = assume(q |- r)
    for statement <- Seq(p |- r, () |- (p ==> r)) do
      val result = Tautology.from(first, second)(statement)
      assert(result.isValid, result.errors.mkString("\n"))
      assert(!result.kernel.usesSorry)
      assert(result.kernel.assumptions == Set(first.kernel.statement, second.kernel.statement))
      assert(result.kernel.statement == statement.underlying)
    assert(Tautology.from(first)(p |- q).isValid)
    assert(Tautology.from(first)((p, p ==> q) |- q).isValid)
    assert(!Tautology.from(first)(r |- q).isValid)

  test("foreign-theory premises are rejected"):
    val other = new Library
    val premise = Thm(lisa.kernel.proof.Assume(using other.theory)((p |- q).underlying).toOption.get)
    assert(!Tautology.from(premise)(p |- q).isValid)

  test("compound premises and multiple conclusions require no eager formula conversion"):
    val theory = summon[Library].theory
    def assume(statement: Sequent): Thm = Thm(lisa.kernel.proof.Assume(using theory)(statement.underlying).toOption.get)
    val examples = Seq(
      (Seq(() |- (p \/ q), p |- r, q |- r), () |- r),
      (Seq((p /\ q) |- r), (p, q) |- r),
      (Seq(() |- p, () |- !p), () |- r),
      (Seq(() |- (p <=> q)), (p \/ r) |- (q \/ r)),
      (Seq(() |- (p, q), p |- r, q |- r), () |- r)
    )
    for (premises, target) <- examples do
      val imports = premises.map(assume)
      val result = Tautology.from(imports*)(target)
      assert(result.isValid, result.errors.mkString("\n"))
      assert(!result.kernel.usesSorry)

  test("arbitrary premise sequents agree with exhaustive Boolean consequence"):
    val random = new Random(0x1e77a)
    val variables = Vector(p, q, r)
    def literal(): Expr[Prop] =
      val atom = variables(random.nextInt(variables.size))
      if random.nextBoolean() then atom else !atom
    def sequent(): Sequent = Sequent(Set.fill(random.nextInt(3))(literal()), Set.fill(random.nextInt(3))(literal()))
    def evaluate(formula: Expr[Prop], bits: Int): Boolean = formula match
      case neg(atom) => !evaluate(atom, bits)
      case atom => (bits & (1 << variables.indexOf(atom))) != 0
    def valid(statement: Sequent, bits: Int): Boolean =
      !statement.left.forall(evaluate(_, bits)) || statement.right.exists(evaluate(_, bits))
    val theory = summon[Library].theory
    for _ <- 0 until 250 do
      val premises = Vector.fill(3)(sequent())
      val target = sequent()
      val expected = (0 until 8).forall(bits => !premises.forall(valid(_, bits)) || valid(target, bits))
      val theorems = premises.map(statement => Thm(lisa.kernel.proof.Assume(using theory)(statement.underlying).toOption.get))
      val result = Tautology.from(theorems*)(target)
      assert(result.isValid == expected, s"$premises => $target: ${result.errors}")
      if expected then
        assert(!result.kernel.usesSorry)
        assert(result.kernel.assumptions.subsetOf(premises.map(_.underlying).toSet))
