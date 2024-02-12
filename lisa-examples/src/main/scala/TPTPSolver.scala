import java.io.File
import java.io.FileWriter

import scala.concurrent.duration._

import lisa.utils.ProofsConverter.*
import lisa.utils.RunSolver.*
import lisa.utils.tptp.*
import lisa.utils.tptp.KernelParser.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.ProofsShrink.optimizeProofIteratively

object TPTPSolver extends lisa.Main {
  sealed trait ProofType
  case object BySolver extends ProofType
  case object Kernel extends ProofType
  case object KernelOptimized extends ProofType

  class ProblemSolverResults(val problem: Problem, val solverName: String, val solverStatus: String, val proofCode: String, val proofType: ProofType)

  val spc = Seq("PRP", "FOF") // type of problems we want to extract and solve
  // val spc = Seq("CNF") // almost no CNF problems are solved by Tableau, TODO: investigate why

  // We limit the execution time to solve each problem
  val timeoutTableau = .1.second
  val timeoutTautology = .1.second

  val exportOnlySolvedProblems = true
  val exportOptimizedProofs = true
  val exportBySolverProofs = true

  val jsonResultsPath: String = "/home/auguste/Documents/EPFL/PhD/Projects/lisa/lisa-examples/src/main/resources/TPTPResults.json"
  val TPTPProblemPath: String = "/home/auguste/Documents/EPFL/PhD/Projects/TPTP-v8.2.0/Problems/"

  val d = new File(TPTPProblemPath)
  val libraries = d.listFiles.filter(_.isDirectory)
  val probfiles = libraries.flatMap(_.listFiles).filter(_.isFile)

  // val d = new File(TPTPProblemPath + "SYN/")
  // val probfiles = d.listFiles.filter(_.isFile)

  var nbProblemsExtracted = 0
  var nbProblemsSolved = Map("Tableau" -> 0, "Tautology" -> 0)
  var nbInvalidProofs = Map("Tableau" -> 0, "Tautology" -> 0)
  var results = Seq.empty[ProblemSolverResults]

  for ((probfile, i) <- probfiles.zipWithIndex) {
    // Progress bar
    if ((i + 1) % 10 == 0 || i + 1 == probfiles.size) {
      val pbarLength = 20
      var pbarContent = "=" * (((i + 1) * pbarLength) / probfiles.size)
      pbarContent += " " * (pbarLength - pbarContent.length)
      print(s"[$pbarContent]")
      print(s" -- ${i + 1}/${probfiles.size} processed files")
      print(s" -- $nbProblemsExtracted extracted problems")
      print(s" -- Tableau: ${nbProblemsSolved("Tableau")} solved + ${nbInvalidProofs("Tableau")} invalid")
      println(s" -- Tautology: ${nbProblemsSolved("Tautology")} solved + ${nbInvalidProofs("Tautology")} invalid")
    }

    // Try to extract and solve the problem
    try {
      val md = getProblemInfos(probfile)
      if (!(md.spc.contains("SAT"))) {
        if (md.spc.exists(spc.contains)) {
          val problem = problemToKernel(probfile, md)
          val seq = problemToSequent(problem)
          nbProblemsExtracted += 1

          def exportResults(problem: Problem, solverName: String, solverResult: SolverResult): Unit =
            val solverStatus = solverResult.getClass.getSimpleName.stripSuffix("$")
            solverResult match
              case Solved(proof) =>
                nbProblemsSolved += (solverName -> (nbProblemsSolved(solverName) + 1))
                results :+= new ProblemSolverResults(problem, solverName, solverStatus, generateStandaloneTheoremFileContent(problem.name, proof), Kernel)
                if (exportOptimizedProofs)
                  results :+= new ProblemSolverResults(problem, solverName, solverStatus, generateStandaloneTheoremFileContent(problem.name, optimizeProofIteratively(proof)), KernelOptimized)
                if (exportBySolverProofs)
                  val statementString = any2code(seq)
                  val proofCode = s"have(thesis) by $solverName"
                  val symbolDeclarations = generateSymbolDeclarationCode(Set(K.sequentToFormula(seq)), "private")
                  results :+= new ProblemSolverResults(problem, solverName, solverStatus, generateStandaloneTheoremFileContent(problem.name, statementString, proofCode, symbolDeclarations), BySolver)
              case InvalidProof(proof) =>
                nbInvalidProofs += (solverName -> (nbInvalidProofs(solverName) + 1))
                if (!exportOnlySolvedProblems)
                  results :+= new ProblemSolverResults(problem, solverName, solverStatus, generateStandaloneTheoremFileContent(problem.name, proof), Kernel)
              case _ =>
                if (!exportOnlySolvedProblems)
                  results :+= new ProblemSolverResults(problem, solverName, solverStatus, "", Kernel)

          // Attempting proof by Tableau
          val tableauResult = proveSequent(seq, timeoutTableau, Tableau.solve)
          exportResults(problem, "Tableau", tableauResult)

          // Attempting proof by Tautology
          def tautologySolver(s: lisa.utils.K.Sequent): Option[SCProof] = Tautology.solveSequent(s) match
            case Left(proof) => Some(proof)
            case _ => None
          val tautologyResult = proveSequent(seq, timeoutTautology, tautologySolver)
          exportResults(problem, "Tautology", tautologyResult)
        }
        // } else println(s"Problem $probfile not extracted because of its type: ${md.spc.mkString(",")}")
      }
    } catch case e => println(s"Error while processing $probfile (index $i): $e")
  }

  // Write results to a JSON file
  val jsonResultsFile = new File(jsonResultsPath)
  if (!jsonResultsFile.getParentFile.exists())
    jsonResultsFile.getParentFile.mkdirs()
  val jsonWriter = new java.io.PrintWriter(jsonResultsPath)
  ujson.writeTo(
    results.map(r =>
      ujson.Obj(
        "problemName" -> r.problem.name,
        "problemDomain" -> r.problem.domain,
        "problemStatus" -> r.problem.status,
        "problemSPC" -> r.problem.spc.mkString(","),
        "problemSequent" -> any2code(problemToSequent(r.problem)),
        "problemFile" -> r.problem.file,
        "solver" -> r.solverName,
        "solverStatus" -> r.solverStatus,
        "proofType" -> r.proofType.getClass.getSimpleName.stripSuffix("$"),
        "solverProofCode" -> r.proofCode
      )
    ),
    jsonWriter,
    indent = 2
  )
  jsonWriter.close()

}
