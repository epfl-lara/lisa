package lisa.tptp

import lisa.tptp.KernelParser.annotatedStatementToKernel
import lisa.tptp.KernelParser.parseToKernel
import lisa.tptp.KernelParser.problemToSequent
import lisa.tptp.ProblemGatherer.getPRPproblems
import lisa.utils.K.given
import lisa.utils.K.repr

import KernelParser.{strictMapAtom, strictMapTerm, strictMapVariable, emptyctx}

object Example {

  def tptpExample(): Unit = {
    val axioms = List(
      "( ~ ( ? [X] : ( big_s(X) & big_q(X) ) ) )",
      "( ! [X] : ( big_p(X) => ( big_q(X) | big_r(X) ) ) )",
      "( ~ ( ? [X] : big_p(X) ) => ? [Y] : big_q(Y) )",
      "( ! [X] : ( ( big_q(X) | big_r(X) ) => big_s(X) ) )"
    )
    val conjecture = "( ? [X] : ( big_p(X) & big_r(X) ) )"
    val anStatements = List(
      "fof(pel24_1,axiom,\n    ( ~ ( ? [X] :\n            ( big_s(X)\n            & big_q(X) ) ) )).",
      "\nfof(pel24_2,axiom,\n    ( ! [X] :\n        ( big_p(X)\n       => ( big_q(X)\n          | big_r(X) ) ) )).",
      "fof(pel24_3,axiom,\n    ( ~ ( ? [X] : big_p(X) )\n   => ? [Y] : big_q(Y) )).",
      "fof(pel24_4,axiom,\n    ( ! [X] :\n        ( ( big_q(X)\n          | big_r(X) )\n       => big_s(X) ) )).",
      "fof(pel24,conjecture,\n    ( ? [X] :\n        ( big_p(X)\n        & big_r(X) ) ))."
    )

    println("\n---Individual Fetched Formulas---")
    axioms.foreach(a => println(parseToKernel(a)(using emptyctx, (strictMapAtom, strictMapTerm, strictMapVariable)).repr))
    println(parseToKernel(conjecture)(using emptyctx, (strictMapAtom, strictMapTerm, strictMapVariable)).repr)

    println("\n---Annotated Formulas---")
    anStatements.map(annotatedStatementToKernel(_)(using emptyctx, (strictMapAtom, strictMapTerm, strictMapVariable))).foreach(f => printAnnotatedStatement(f))

    println("\n---Problems---")

    try {
      val probs = getPRPproblems
      probs.foreach(p => println("Problem: " + p.name + " (" + p.domain + ") --- " + p.file))

      println("Number of problems found with PRP spc: " + probs.size)

      if (probs.nonEmpty) {
        println(" - First problem as illustration:")
        val seq = problemToSequent(probs.head)
        printProblem(probs.head)
        println("\n---Sequent---")
        println(seq.repr)
      }
    } catch {
      case error: NullPointerException => println("You can download the tptp library at http://www.tptp.org/ and put it in main/resources")
    }

  }

  // Utility
  def printAnnotatedStatement(a: AnnotatedStatement): Unit = {
    val prettyStatement = a match {
      case f: AnnotatedFormula => f.formula.repr
      case s: AnnotatedSequent => s.sequent.repr
    }
    if (a.role == "axiom") println("Given " + a.name + ": " + prettyStatement)
    else if (a.role == "conjecture") println("Prove " + a.name + ": " + prettyStatement)
    else println(a.role + " " + a.name + ": " + prettyStatement)
  }

  def printProblem(p: Problem): Unit = {
    println("Problem: " + p.name + " (" + p.domain + ") ---")
    println("Status: " + p.status)
    println("SPC: " + p.spc.mkString(", "))
    p.formulas.foreach(printAnnotatedStatement)
  }
}
