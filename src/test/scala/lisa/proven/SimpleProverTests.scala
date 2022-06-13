package lisa.proven

import lisa.utils.Printer
import lisa.utils.Printer.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.PredicateLogic
import lisa.kernel.proof.SCProofChecker
import org.scalatest.funsuite.AnyFunSuite
import lisa.proven.tactics.SimplePropositionalSolver as SPS
import lisa.utils.Helpers.*
import lisa.tptp.KernelParser.*
import lisa.tptp.ProblemGatherer.getPRPproblems

class SimpleProverTests extends AnyFunSuite {

  /*
    test("Simple propositional logic proofs") {
        val problems = getPRPproblems.take(1)
        problems.foreach( pr => {
            println("--- Problem "+pr.file)
            val sq = problemToSequent(pr)
            println(prettySequent(sq))
            val proof = SPS.solveSequent(sq)
            if (!Seq("Unsatisfiable", "Theorem", "Satisfiable").contains(pr.status)) println("Unknown status: "+pr.status+", "+pr.file)

            assert(SCProofChecker.checkSCProof(proof).isValid == (pr.status =="Unsatisfiable" || pr.status == "Theorem"))

        })

    }
   */
}
