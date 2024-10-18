package lisa.kernel

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers._
import lisa.utils.KernelHelpers.given_Conversion_Identifier_String
import lisa.utils.KernelHelpers.given_Conversion_String_Identifier
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.MapView
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer
import scala.language.adhocExtensions
import scala.util.Random

class EquivalenceCheckerTests extends AnyFunSuite {
  private val verbose = false // Turn this on to print all tested couples

  def checkEquivalence(left: Expression, right: Expression): Unit = {
    assert(
      isSame(left, right),
      s"Couldn't prove the equivalence between ${left.repr} and ${right.repr}\nLeft tree: ${left}\nRight tree: ${right}"
    )
  }

  def checkNonEquivalence(left: Expression, right: Expression): Unit = {
    assert(
      !isSame(left, right),
      s"Expected the checker to not be able to show equivalence between ${left.repr} and ${right.repr}\nLeft tree: ${left}\nRight tree: ${right}"
    )
  }

  def nameGenerator(): () => String = {
    val chars = 'a' to 'z'
    def stream: LazyList[Seq[Char]] = LazyList.from(chars.map(Seq(_))) #::: stream.flatMap(l => chars.map(_ +: l))
    var current = stream
    () => {
      val id = current.head.reverse.mkString
      current = current.tail
      id
    }
  }

  def numbersGenerator(): () => Int = {
    var i = 1
    () => {
      val n = i
      i += 1
      n
    }
  }

  def constantsGenerator(): () => Expression = {
    val generator = nameGenerator()
    () => {
      val id = generator()
      Constant(id, Formula)
    }
  }

  def ExpressionsGenerator(c: Double)(random: Random): () => Expression = {
    val connectors = ArrayBuffer.empty[String]
    val variables = ArrayBuffer.empty[String]
    val nextConnectorName = nameGenerator()
    val nextVariableName = {
      val gen = numbersGenerator()
      () => s"v${gen()}"
    }
    def generate(p: Double): Expression = {
      val q = random.nextDouble()

      if (q >= p) {
        // Leaf
        val name =
          if (connectors.isEmpty || random.nextDouble() <= 0.75) { // TODO adapt
            // New name
            val id = nextConnectorName()
            connectors += id
            id
          } else {
            // Reuse existing name
            connectors(random.nextInt(connectors.size))
          }
        Constant(name, Formula)
      } else {
        // Branch
        val nextP = p * c
        if (random.nextDouble() < 0.9) {
          // Connector
          val binaries = Seq(and, or, iff, implies)
          if (random.nextInt(binaries.size + 1) > 0) {
            // Binary
            val binary = binaries(random.nextInt(binaries.size))
            val (l, r) = {
              val p1 = nextP * nextP
              val (f1, f2) = (generate(p1), generate(p1))
              if (random.nextBoolean()) (f1, f2) else (f2, f1)
            }
            (binary(l, r))
          } else {
            // Unary
            neg(generate(nextP))
          }
        } else {
          // Binder
          val name = nextVariableName()
          variables += name
          val binderTypes = IndexedSeq(forall, exists)
          val binderType = binderTypes(random.nextInt(binderTypes.size))
          binderType(lambda(Variable(name, Term), generate(nextP)))
        }
      }
    }

    () => generate(c)
  }

  def testcasesAny(generatorToTestcases: (() => Expression) => Random => Seq[(Expression, Expression)], equivalent: Boolean): Unit = {
    val random: Random = new Random(1)

    def testWith(generator: () => () => Expression): Unit = {
      val cases = generatorToTestcases(generator())(random)
      cases.foreach { (left, right) =>
        // For completeness we also test symmetry
        if (equivalent) {
          checkEquivalence(left, right)
          checkEquivalence(right, left)
          if (verbose) {
            println(s"${left.repr}  <==>  ${right.repr}")
          }
        } else {
          checkNonEquivalence(left, right)
          checkNonEquivalence(right, left)
          if (verbose) {
            println(s"${left.repr}  <!=>  ${right.repr}")
          }
        }
      }
    }

    def testWithRepeat(generator: () => () => Expression, n: Int): Unit = {
      for (i <- 0 until n) {
        testWith(generator)
      }
    }

    // 1. Constants (a, b, c, ...)

    testWith(constantsGenerator)

    // 2. Random Expressions (small)

    testWithRepeat(() => ExpressionsGenerator(0.8)(random), 5)

    // 3. Random Expressions (larger)

    testWithRepeat(() => ExpressionsGenerator(0.90)(random), 15)
  }

  def testcases(f: Expression => Random => Seq[(Expression, Expression)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator())(r), equivalent)
  def testcases(f: (Expression, Expression) => Random => Seq[(Expression, Expression)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator(), generator())(r), equivalent)
  def testcases(f: (Expression, Expression, Expression) => Random => Seq[(Expression, Expression)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator(), generator(), generator())(r), equivalent)
  def testcases(f: (Expression, Expression, Expression, Expression) => Random => Seq[(Expression, Expression)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator(), generator(), generator(), generator())(r), equivalent)

  def repeatApply[T](n: Int)(f: T => T)(initial: T): T = if (n > 0) repeatApply(n - 1)(f)(f(initial)) else initial
  def commutativeShuffle(iterations: Int)(random: Random)(f: Expression): Expression = {
    def transform(f: Expression): Expression = f match {
      case And(a, b) => if random.nextBoolean() then and(transform(a), transform(b)) else and(transform(b), transform(a))
      case Or(a, b) => if random.nextBoolean() then or(transform(a), transform(b)) else or(transform(b), transform(a))
      case Iff(a, b) => if random.nextBoolean() then iff(transform(a), transform(b)) else iff(transform(b), transform(a))
      case Application(f, arg) => Application(transform(f), transform(arg))
      case Lambda(v, body) => Lambda(v, transform(body))
      case _ => f
    }
    repeatApply(iterations)(transform)(f)
  }
  def associativeShuffle(iterations: Int)(random: Random)(f: Expression): Expression = {
    def transform(f: Expression): Expression = f match {
      case And(And(a, b), c) => if (random.nextBoolean()) and(transform(a), and(transform(b), transform(c))) else and(and(transform(a), transform(b)), transform(c))
      case Or(Or(a, b), c) => if (random.nextBoolean()) or(transform(a), or(transform(b), transform(c))) else or(or(transform(a), transform(b)), transform(c))
      case Application(f, arg) => Application(transform(f), transform(arg))
      case Lambda(v, body) => Lambda(v, transform(body))
      case _ => f
    }
    repeatApply(iterations)(transform)(f)
  }
  def addDoubleNegations(p: Double)(random: Random)(f: Expression): Expression = {
    def transform(f: Expression): Expression =
      if (random.nextDouble() < p) neg(neg(transform(f)))
      else
        f match {
          case Application(f, arg) => Application(transform(f), transform(arg))
          case Lambda(v, body) => Lambda(v, transform(body))
          case _ => f
        }
    transform(f)
  }
  def addDeMorgans(p: Double)(random: Random)(f: Expression): Expression = {
    def transform(f: Expression): Expression = f match {
      case And(a, b) => if random.nextBoolean() then !or(!transform(a), !transform(b)) else and(transform(b), transform(a))
      case Or(a, b) => if random.nextBoolean() then !and(!transform(a), !transform(b)) else or(transform(b), transform(a))
      case Application(f, arg) => Application(transform(f), transform(arg))
      case Lambda(v, body) => Lambda(v, transform(body))
      case _ => f
    }
    transform(f)
  }

  // Positive

  test("Reflexivity") {
    testcases(a => _ => Seq(a -> a), equivalent = true)
  }

  test("Commutativity (root with equal leaves)") {
    testcases(
      (a, b) =>
        _ =>
          Seq(
            and(a, b) -> and(b, a),
            or(a, b) -> or(b, a),
            iff(a, b) -> iff(b, a)
          ),
      equivalent = true
    )
  }

  test("Associativity (root with equal leaves)") {
    testcases(
      (a, b, c, d) =>
        _ =>
          Seq(
            and(and(a, b), c) -> and(a, and(b, c)),
            or(or(a, b), c) -> or(a, or(b, c))
          ),
      equivalent = true
    )
  }

  test("Commutativity (general)") {
    testcases(
      (a, b) =>
        random =>
          Seq(
            a -> commutativeShuffle(15)(random)(a)
          ),
      equivalent = true
    )
  }

  test("Associativity (general)") {
    testcases(
      (a, b) =>
        random =>
          Seq(
            a -> associativeShuffle(15)(random)(a)
          ),
      equivalent = true
    )
  }

  test("Commutativity and associativity (general)") {
    testcases(
      (a, b) =>
        random =>
          Seq(
            a -> repeatApply(15)(commutativeShuffle(1)(random).andThen(associativeShuffle(1)(random)))(a)
          ),
      equivalent = true
    )
  }

  test("Double negation (root with equal leaf)") {
    testcases(
      a =>
        _ =>
          Seq(
            a -> neg(neg(a)),
            neg(a) -> neg(neg(neg(a))),
            a -> neg(neg(neg(neg(a))))
          ),
      equivalent = true
    )
  }

  test("Double negation (general)") {
    val p = 0.25
    testcases(
      a =>
        random =>
          Seq(
            addDoubleNegations(p)(random)(a) -> addDoubleNegations(p)(random)(a)
          ),
      equivalent = true
    )
  }

  test("De Morgan's law (root)") {
    testcases(
      (a, b) =>
        random =>
          Seq(
            and(a, b) -> neg(or(neg(a), neg(b))),
            or(a, b) -> neg(and(neg(a), neg(b)))
          ),
      equivalent = true
    )
  }

  test("De Morgan's law (general)") {
    val p = 0.25
    testcases(
      a =>
        random =>
          Seq(
            addDeMorgans(p)(random)(a) -> addDeMorgans(p)(random)(a)
          ),
      equivalent = true
    )
  }

  test("Allowed tautologies") {
    testcases(
      (a, b, c) =>
        random =>
          Seq(
            or(a, neg(a)) -> or(neg(a), neg(neg(a))),
            and(a, neg(a)) -> and(neg(a), neg(neg(a)))
          ),
      equivalent = true
    )
  }

  test("Absorption") {
    testcases(
      (a, b, c) =>
        random =>
          Seq(
            and(a, a) -> a,
            or(a, a) -> a
          ),
      equivalent = true
    )
  }

  test("All allowed transformations") {
    val transformations: Seq[Random => Expression => Expression] = IndexedSeq(
      r => commutativeShuffle(1)(r),
      r => associativeShuffle(1)(r),
      r => addDoubleNegations(0.02)(r),
      r => addDeMorgans(0.05)(r)
    )
    def randomTransformations(random: Random)(f: Expression): Expression = {
      val n = random.nextInt(50)
      Seq.fill(n)(transformations(random.nextInt(transformations.size))).foldLeft(f)((acc, e) => e(random)(acc))
    }

    testcases(
      a =>
        random =>
          Seq(
            randomTransformations(random)(a) -> randomTransformations(random)(a)
          ),
      equivalent = true
    )
  }

}
