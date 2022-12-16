package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.{_, given}
import lisa.utils.Printer
import org.scalatest.funsuite.AnyFunSuite


class SubstitutionTest extends AnyFunSuite {
  private val x = variable
  private val y = variable
  private val z = variable

  private val f = function(1)
  private val g = function(1)

  private val h = function(2)

  private val X = formulaVariable
  private val Y = formulaVariable
  private val Z = formulaVariable


  private val P = predicate(1)
  private val Q = predicate(1)

  private val R = predicate(2)

  private val c1 = connector(1)

  private val c2 = connector(2)

  test("Substitution in Terms") {
    //  def instantiateTermSchemas(t: Term, m: Map[SchematicTermLabel, LambdaTermTerm]): Term

    val cases:List[(Term, Term)] = List(

    )
    assert(true)
  }

}
