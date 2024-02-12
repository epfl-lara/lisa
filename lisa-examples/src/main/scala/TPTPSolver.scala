import java.io.File
import java.io.FileWriter

import scala.concurrent.duration._

import lisa.utils.ProofsConverter.*
import lisa.utils.RunSolver.*
import lisa.utils.tptp.*
import lisa.utils.tptp.KernelParser.*
import lisa.utils.tptp.ProblemGatherer.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SCProofChecker.checkSCProof

object TPTPSolver extends lisa.Main {
  try {
    val spc = Seq("PRP", "FOF") // type of problems we want to extract and solve
    // val spc = Seq("PRP", "FOF", "CNF") // almost no CNF problems are solved by Tableau, TODO: investigate why

    // val d = new File(TPTPProblemPath)
    // val libraries = d.listFiles.filter(_.isDirectory)
    // val probfiles = libraries.flatMap(_.listFiles).filter(_.isFile)

    val d = new File(TPTPProblemPath + "SYN/")
    val probfiles = d.listFiles.filter(_.isFile)

    // We limit the execution time to solve each problem
    val timeoutTableau = .1.second
    val timeoutTautology = .1.second

    var nbProblemsExtracted = 0
    var nbProblemsSolvedByTableau = 0
    var nbProblemsSolvedByTautology = 0

    for ((probfile, i) <- probfiles.zipWithIndex) {
      // Progress bar
      if ((i + 1) % 10 == 0 || i + 1 == probfiles.size) {
        val pbarLength = 30
        var pbarContent = "=" * (((i + 1) * pbarLength) / probfiles.size)
        pbarContent += " " * (pbarLength - pbarContent.length)
        print(s"[$pbarContent]")
        print(s" -- ${i + 1}/${probfiles.size} processed files")
        print(s" -- $nbProblemsExtracted extracted problems")
        print(s" -- Tableau: $nbProblemsSolvedByTableau solved")
        println(s" -- Tautology: $nbProblemsSolvedByTautology solved")
      }

      // Try to extract and solve the problem
      try {
        val md = getProblemInfos(probfile)
        if (md.spc.exists(spc.contains)) {
          val p = problemToKernel(probfile, md)
          val seq = problemToSequent(p)
          nbProblemsExtracted += 1

          // Attempting proof by Tableau
          proveSequent(seq, timeoutTableau, Tableau.solve) match {
            case Solved(proof) =>
              if (checkSCProof(proof).isValid)
                nbProblemsSolvedByTableau += 1
                // writeProof(p, proof, "examples/proofs/tableau/")
              else throw new Exception("Tableau proof is not valid")
            case _ => ()
          }

          // Attempting proof by Tautology
          def tautologySolver(s: lisa.utils.K.Sequent): Option[SCProof] = Tautology.solveSequent(s) match
            case Left(proof) => Some(proof)
            case _ => None
          proveSequent(seq, timeoutTautology, tautologySolver) match {
            case Solved(proof) =>
              if (checkSCProof(proof).isValid)
                nbProblemsSolvedByTautology += 1
                // writeProof(p, proof, "examples/proofs/tautology/")
              else throw new Exception("Tautology proof is not valid")
            case _ => ()
          }
        }
      } catch {
        case e => println(s"Error while processing $probfile: $e")
      }
    }
  } catch {
    case error: NullPointerException => println("You can download the tptp library at http://www.tptp.org/ and put it in main/resources")
  }
}

def writeProof(problem: Problem, proof: SCProof, path: String): Unit = {
  val file = new File(path + problem.name + ".sc")
  val bw = new FileWriter(file)
  val fileContent = generateStandaloneTheoremFileContent(problem.name, problemToSequent(problem), proof)
  bw.write(fileContent)
  bw.close()
}
