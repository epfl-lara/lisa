package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import scala.util.Random

class CongruenceRegressionSuite extends AnyFunSuite:
  given Library = new Library
  private val a, b, c, d = variable[Ind]
  private val p, q, r = variable[Prop]
  private val f = variable[Ind >>: Ind]
  private val g = variable[Ind >>: Ind >>: Ind]
  private val P, Q = variable[Ind >>: Prop]
  private val F = variable[Prop >>: Prop]

  private def check(statement: Sequent, expected: Boolean): Unit =
    val result = Congruence.solve(statement)
    assert(result.isRight == expected, s"$statement\n$result")
    result.foreach { proof =>
      assert(proof.kernel.statement == statement.underlying)
      assert(!proof.kernel.usesSorry)
      assert(proof.kernel.axioms.isEmpty && proof.kernel.assumptions.isEmpty)
    }

  test("closure covers symmetry, chains, nested applications and both formula polarities"):
    Seq(
      p |- p,
      () |- (a === a),
      (a === b) |- (b === a),
      (a === b, b === c, c === d) |- (a === d),
      (a === b) |- (f(f(f(a))) === f(f(f(b)))),
      (a === b, c === d) |- (g(f(a))(c) === g(f(b))(d)),
      (a === b) |- (g(a)(a) === g(b)(b)),
      (a === b, P(f(a))) |- P(f(b)),
      (a === b, P(f(a)), !P(f(b))) |- (),
      (a === b) |- (P(f(a)), !P(f(b))),
      (a === b, !(f(a) === f(b))) |- (),
      (p <=> q) |- (F(F(p)) <=> F(F(q))),
      (p <=> q, F(p)) |- F(q),
      (p <=> q, !(F(p) <=> F(q))) |- (),
      (F(F(F(F(F(F(F(p))))))) <=> p, F(F(F(F(F(p))))) <=> p) |- (F(p) <=> p),
      (a === b, P(f(b)) <=> F(P(f(a))), F(F(P(f(a))))) |- F(F(P(f(b))))
    ).foreach(check(_, true))
    Seq(
      () |- (a === b),
      (f(a) === f(b)) |- (a === b),
      (a === b, P(a)) |- Q(b),
      (a === b) |- (P(a), !Q(b)),
      (a === b, !(a === c)) |- ()
    ).foreach(check(_, false))

  test("seeded ground equalities agree with a naive partition closure"):
    val random = new Random(0xced)
    val terms = Vector(a, b, c, f(a), f(b), f(c), f(f(a)), f(f(b)), g(a)(b), g(b)(a), g(c)(c))
    for _ <- 0 until 160 do
      val equations = Vector.fill(random.nextInt(6))(terms(random.nextInt(terms.size)) -> terms(random.nextInt(terms.size)))
      val initial = equations.foldLeft(terms.map(Set(_)).toSet) { case (classes, (left, right)) =>
        val touching = classes.filter(group => group.contains(left) || group.contains(right))
        (classes -- touching) + touching.flatten
      }
      def saturate(classes: Set[Set[Expr[Ind]]]): Set[Set[Expr[Ind]]] =
        def same(left: Expr[?], right: Expr[?]): Boolean = left == right || classes.exists(group => group.exists(_ == left) && group.exists(_ == right))
        val pair = (for
          left <- terms.iterator
          right <- terms.iterator
          if !same(left, right)
          (label, args) = Multiapp.unapply(left).get
          (other, targets) = Multiapp.unapply(right).get
          if label == other && args.size == targets.size && args.zip(targets).forall(same)
        yield left -> right).nextOption()
        pair match
          case None => classes
          case Some((left, right)) =>
            val touching = classes.filter(group => group.contains(left) || group.contains(right))
            saturate((classes -- touching) + touching.flatten)
      val classes = saturate(initial)
      val left = terms(random.nextInt(terms.size))
      val right = terms(random.nextInt(terms.size))
      val expected = classes.exists(group => group.contains(left) && group.contains(right))
      val assumptions = equations.map((x, y) => x === y).toSet
      check(Sequent(assumptions, Set(left === right)), expected)
      check(Sequent(assumptions + P(left), Set(P(right))), expected)

  test("flattening preserves opaque equalities, cyclic explanations and variable freshness"):
    check((f(a) === f(b)) |- (P(f(a)) <=> P(f(b))), true)
    check((f(a) === f(b)) |- (P(a) <=> P(b)), false)
    check((f(a) === g(a)(b), f(f(a)) === b, f(b) === g(a)(b), f(b) === g(c)(c), f(a) === f(f(b))) |- (f(b) === b), true)
    val hole = Variable[Ind](K.Identifier("hole", 100))
    val chain = Variable[Ind](K.Identifier("chain", 101))
    check((hole === chain, chain === c) |- (f(hole) === f(c)), true)

  test("conditional and multi-conclusion premises preserve only declared dependencies"):
    val theory = summon[Library].theory
    def assume(statement: Sequent): Thm = Thm(lisa.kernel.proof.Assume(using theory)(statement.underlying).toOption.get)
    val cases = Seq(
      ((P(b), a === b) |- Q(a), Seq(assume(P(a) |- Q(a)))),
      ((P(a), Q(b), a === b) |- r, Seq(assume((P(b), Q(a)) |- r))),
      ((P(a), a === b) |- Q(a), Seq(assume(P(c) |- Q(c)), assume(P(a) |- (a === c)))),
      (P(a) |- (Q(a), r), Seq(assume(P(a) |- (Q(a), r))))
    )
    for (statement, premises) <- cases do
      val result = Congruence.from(premises*)(statement)
      assert(result.isValid, s"$statement\n${result.errors}")
      assert(result.kernel.statement == statement.underlying)
      assert(!result.kernel.usesSorry)
      assert(result.kernel.assumptions.subsetOf(premises.flatMap(_.kernel.assumptions).toSet))
    val foreign = lisa.kernel.proof.Assume(using new Library().theory)((a === b |- ()).underlying).toOption.get
    assert(!Congruence.from(Thm(foreign))(p |- q).isValid)
