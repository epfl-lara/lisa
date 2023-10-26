package lisa.kernel

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.utils.FOLPrinter
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

  def checkEquivalence(left: Formula, right: Formula): Unit = {
    assert(
      isSame(left, right),
      s"Couldn't prove the equivalence between ${FOLPrinter.prettyFormula(left)} and ${FOLPrinter.prettyFormula(right)}\nLeft tree: ${left}\nRight tree: ${right}"
    )
  }

  def checkNonEquivalence(left: Formula, right: Formula): Unit = {
    assert(
      !isSame(left, right),
      s"Expected the checker to not be able to show equivalence between ${FOLPrinter.prettyFormula(left)} and ${FOLPrinter.prettyFormula(right)}\nLeft tree: ${left}\nRight tree: ${right}"
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

  def constantsGenerator(): () => Formula = {
    val generator = nameGenerator()
    () => {
      val id = generator()
      PredicateFormula(ConstantPredicateLabel(id, 0), Seq.empty)
    }
  }

  def formulasGenerator(c: Double)(random: Random): () => Formula = {
    val connectors = ArrayBuffer.empty[String]
    val variables = ArrayBuffer.empty[String]
    val nextConnectorName = nameGenerator()
    val nextVariableName = {
      val gen = numbersGenerator()
      () => s"v${gen()}"
    }
    def generate(p: Double): Formula = {
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
        PredicateFormula(ConstantPredicateLabel(name, 0), Seq.empty)
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
          val binderTypes: IndexedSeq[BinderLabel] = IndexedSeq(Forall, Exists, ExistsOne)
          val binderType = binderTypes(random.nextInt(binderTypes.size))
          BinderFormula(binderType, VariableLabel(name), generate(nextP))
        }
      }
    }

    () => generate(c)
  }

  def testcasesAny(generatorToTestcases: (() => Formula) => Random => Seq[(Formula, Formula)], equivalent: Boolean): Unit = {
    val random: Random = new Random(1)

    def testWith(generator: () => () => Formula): Unit = {
      val cases = generatorToTestcases(generator())(random)
      cases.foreach { (left, right) =>
        // For completeness we also test symmetry
        if (equivalent) {
          checkEquivalence(left, right)
          checkEquivalence(right, left)
          if (verbose) {
            println(s"${FOLPrinter.prettyFormula(left)}  <==>  ${FOLPrinter.prettyFormula(right)}")
          }
        } else {
          checkNonEquivalence(left, right)
          checkNonEquivalence(right, left)
          if (verbose) {
            println(s"${FOLPrinter.prettyFormula(left)}  <!=>  ${FOLPrinter.prettyFormula(right)}")
          }
        }
      }
    }

    def testWithRepeat(generator: () => () => Formula, n: Int): Unit = {
      for (i <- 0 until n) {
        testWith(generator)
      }
    }

    // 1. Constants (a, b, c, ...)

    testWith(constantsGenerator)

    // 2. Random formulas (small)

    testWithRepeat(() => formulasGenerator(0.8)(random), 5)

    // 3. Random formulas (larger)

    testWithRepeat(() => formulasGenerator(0.90)(random), 15)
  }

  def testcases(f: Formula => Random => Seq[(Formula, Formula)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator())(r), equivalent)
  def testcases(f: (Formula, Formula) => Random => Seq[(Formula, Formula)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator(), generator())(r), equivalent)
  def testcases(f: (Formula, Formula, Formula) => Random => Seq[(Formula, Formula)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator(), generator(), generator())(r), equivalent)
  def testcases(f: (Formula, Formula, Formula, Formula) => Random => Seq[(Formula, Formula)], equivalent: Boolean): Unit =
    testcasesAny(generator => r => f(generator(), generator(), generator(), generator())(r), equivalent)

  def repeatApply[T](n: Int)(f: T => T)(initial: T): T = if (n > 0) repeatApply(n - 1)(f)(f(initial)) else initial
  def commutativeShuffle(iterations: Int)(random: Random)(f: Formula): Formula = {
    def transform(f: Formula): Formula = f match {
      case PredicateFormula(label, args) => f
      case ConnectorFormula(label, args) =>
        val newArgs = label match {
          case And | Or | Iff => random.shuffle(args)
          case _ => args
        }
        ConnectorFormula(label, newArgs.map(transform))
      case BinderFormula(label, bound, inner) => BinderFormula(label, bound, transform(inner))
    }
    repeatApply(iterations)(transform)(f)
  }
  def associativeShuffle(iterations: Int)(random: Random)(f: Formula): Formula = {
    def transform(f: Formula): Formula = f match {
      case PredicateFormula(label, args) => f
      // Simple for now, assume binary operations
      case ConnectorFormula(label1 @ (And | Or), Seq(ConnectorFormula(label2, Seq(a1, a2)), a3)) if label1 == label2 =>
        if (random.nextBoolean()) {
          ConnectorFormula(label1, Seq(a1, ConnectorFormula(label2, Seq(a2, a3))))
        } else {
          f
        }
      case ConnectorFormula(label1 @ (And | Or), Seq(a1, ConnectorFormula(label2, Seq(a2, a3)))) if label1 == label2 =>
        if (random.nextBoolean()) {
          ConnectorFormula(label1, Seq(ConnectorFormula(label2, Seq(a1, a2)), a3))
        } else {
          f
        }
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(transform))
      case BinderFormula(label, bound, inner) => BinderFormula(label, bound, transform(inner))
    }
    repeatApply(iterations)(transform)(f)
  }
  def addDoubleNegations(p: Double)(random: Random)(f: Formula): Formula = {
    def transform(f: Formula): Formula =
      if (random.nextDouble() < p) neg(neg(transform(f)))
      else
        f match {
          case _: PredicateFormula => f
          case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(transform))
          case BinderFormula(label, bound, inner) => BinderFormula(label, bound, transform(inner))
        }
    transform(f)
  }
  def addDeMorgans(p: Double)(random: Random)(f: Formula): Formula = {
    def transform(f: Formula): Formula = f match {
      case _: PredicateFormula => f
      case ConnectorFormula(label, args) =>
        val map: Map[ConnectorLabel, ConnectorLabel] = Map(And -> Or, Or -> And)
        map.get(label) match {
          case Some(opposite) if random.nextDouble() < p => transform(neg(ConnectorFormula(opposite, args.map(neg(_)))))
          case _ => ConnectorFormula(label, args.map(transform))
        }
      case BinderFormula(label, bound, inner) => BinderFormula(label, bound, transform(inner))
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
    val transformations: Seq[Random => Formula => Formula] = IndexedSeq(
      r => commutativeShuffle(1)(r),
      r => associativeShuffle(1)(r),
      r => addDoubleNegations(0.02)(r),
      r => addDeMorgans(0.05)(r)
    )
    def randomTransformations(random: Random)(f: Formula): Formula = {
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
