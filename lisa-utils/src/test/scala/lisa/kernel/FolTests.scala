package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.Printer
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.immutable.SortedSet
import scala.language.adhocExtensions
import scala.util.Random

class FolTests extends AnyFunSuite {

  val predicateVerifier = SCProofChecker.checkSCProof

  def nameGenerator(candidates: Seq[String], gen: Random = new Random(), l: Int = 1): String = {
    if (gen.nextBoolean()) gen.nextString(1)
    else candidates(gen.between(0, candidates.length))
  }

  def termGenerator(maxDepth: Int, gen: Random = new Random()): Term = {
    if (maxDepth <= 1) {
      val r = gen.between(0, 3)
      if (r == 0) {
        val name = "" + ('a' to 'e')(gen.between(0, 5))
        Term(ConstantFunctionLabel(name, 0), List())
      } else {
        val name = "" + ('v' to 'z')(gen.between(0, 5))
        VariableTerm(VariableLabel(name))
      }
    } else {
      val r = gen.between(0, 8)
      val name = "" + ('f' to 'j')(gen.between(0, 5))
      if (r == 0) {
        val name = "" + ('a' to 'e')(gen.between(0, 5))
        Term(ConstantFunctionLabel(name, 0), List())
      } else if (r == 1) {
        val name = "" + ('v' to 'z')(gen.between(0, 5))
        VariableTerm(VariableLabel(name))
      }
      if (r <= 3) Term(ConstantFunctionLabel(name, 1), Seq(termGenerator(maxDepth - 1, gen)))
      else if (r <= 5) Term(ConstantFunctionLabel(name, 2), Seq(termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen)))
      else if (r == 6) Term(ConstantFunctionLabel(name, 3), Seq(termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen)))
      else
        Term(
          ConstantFunctionLabel(name, 4),
          Seq(termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen))
        )

    }
  }

  def formulaGenerator(maxDepth: Int, gen: Random = new Random()): Formula = {
    if (maxDepth <= 2 || (gen.nextBoolean() && gen.nextBoolean())) {
      val r = gen.between(0, 7)
      if (r <= 1) {
        val name = "" + ('A' to 'E')(gen.between(0, 5))
        PredicateFormula(ConstantPredicateLabel(name, 0), Seq())
      } else if (r <= 3) {
        val name = "" + ('A' to 'E')(gen.between(0, 5))
        PredicateFormula(ConstantPredicateLabel(name, 1), Seq(termGenerator(maxDepth - 1, gen)))
      } else if (r <= 5) {
        val s = gen.between(0, 3)
        if (s == 0) PredicateFormula(equality, Seq(termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen)))
        else {
          val name = "" + ('A' to 'E')(gen.between(0, 5))
          PredicateFormula(ConstantPredicateLabel(name, 2), Seq(termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen)))
        }
      } else {
        val name = "" + ('A' to 'E')(gen.between(0, 5))
        PredicateFormula(ConstantPredicateLabel(name, 3), Seq(termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen), termGenerator(maxDepth - 1, gen)))
      }

    } else {
      val r = gen.between(0, 7)
      if (r <= 1) neg(formulaGenerator(maxDepth - 1, gen))
      else if (r == 2) and(formulaGenerator(maxDepth - 1, gen), formulaGenerator(maxDepth - 1, gen))
      else if (r == 3) or(formulaGenerator(maxDepth - 1, gen), formulaGenerator(maxDepth - 1, gen))
      else if (r == 4) implies(formulaGenerator(maxDepth - 1, gen), formulaGenerator(maxDepth - 1, gen))
      else if (r == 5) {
        val f = formulaGenerator(maxDepth - 1, gen)
        val l = f.freeVariables.toSeq ++ Seq(x)
        forall(l(gen.between(0, l.size)), f)
      } else {
        val f = formulaGenerator(maxDepth - 1, gen)
        val l = f.freeVariables.toSeq ++ Seq(x)
        exists(l(gen.between(0, l.size)), f)
      }
    }

  }

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  private val z = VariableLabel("z")
  private val a = PredicateFormula(ConstantPredicateLabel("A", 0), Seq())
  private val b = PredicateFormula(ConstantPredicateLabel("B", 0), Seq())
  private val fp = ConstantPredicateLabel("F", 1)
  private val sT = VariableLabel("t")

  def test_some_random_formulas(n: Int, maxDepth: Int): Unit = {
    (0 to n).foreach(_ => println(formulaGenerator(maxDepth)))
  }

  test("Random formulas well-constructed") {
    (0 to 50).foreach(_ => formulaGenerator(10))
  }

  test("Fresh variables should be fresh") {
    val y1 = VariableLabel(freshId(equ(VariableTerm(x), VariableTerm(x)).freeVariables.map(_.name), x.name))

    assert(!isSame(x, y1))
  }
}
