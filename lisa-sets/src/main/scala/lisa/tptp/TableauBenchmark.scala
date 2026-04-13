package lisa.tptp

import lisa.automation.Tableau
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.tptp.KernelParser._
import lisa.utils.K
import lisa.utils.KernelHelpers._
import mainargs.{ParserForClass, TokensReader, arg, main}

import java.io.File

/**
 * Benchmark utility for the Tableau tactic on TPTP problems.
 *
 * Usage (via sbt):
 *   sbt "lisa-sets/runMain lisa.tptp.TableauBenchmark --input <path-to-problem.p>"
 *   sbt "lisa-sets/runMain lisa.tptp.TableauBenchmark --input <path-to-problem.p> --timeout 30000"
 *
 * The TPTP environment variable should be set to the root of the TPTP distribution
 * if the problem has include directives referencing axiom files.
 */
object TableauBenchmark {

  case class BenchmarkResult(
      problemName: String,
      file: String,
      domain: String,
      status: String,
      spc: String,
      numFormulas: Int,
      parseTimeMs: Long,
      solveTimeMs: Long,
      totalTimeMs: Long,
      solved: Boolean,
      proofValid: Option[Boolean],
      proofSteps: Option[Int],
      error: Option[String]
  ) {
    def toCSVHeader: String =
      "problem,file,domain,status,spc,numFormulas,parseTimeMs,solveTimeMs,totalTimeMs,solved,proofValid,proofSteps,error"

    def toCSV: String = {
      val fields = Seq(
        problemName, file, domain, status, spc,
        numFormulas.toString, parseTimeMs.toString, solveTimeMs.toString, totalTimeMs.toString,
        solved.toString,
        proofValid.map(_.toString).getOrElse(""),
        proofSteps.map(_.toString).getOrElse(""),
        error.map(e => "\"" + e.replace("\"", "'") + "\"").getOrElse("")
      )
      fields.mkString(",")
    }

    override def toString: String = {
      val resultStr = if solved then "SOLVED" else "FAILED"
      val validStr = proofValid match
        case Some(true)  => " (proof valid)"
        case Some(false) => " (proof INVALID)"
        case None        => ""
      val stepsStr = proofSteps.map(s => s", $s steps").getOrElse("")
      val errorStr = error.map(e => s", error: $e").getOrElse("")
      s"$resultStr in ${solveTimeMs}ms$validStr$stepsStr$errorStr - $problemName ($domain)"
    }
  }

  @main
  case class Config(
      @arg(doc = "Path to a TPTP problem file (.p)")
      input: String,
      @arg(doc = "Timeout in milliseconds (0 = no timeout, default: 60000)")
      timeout: Long = 60000,
      @arg(doc = "Whether to verify the proof with the kernel checker (default: true)")
      verify: Boolean = true,
      @arg(doc = "Output format: text (default), csv, verbose")
      format: String = "text"
  )

  def main(args: Array[String]): Unit = {
    val config = ParserForClass[Config].constructOrThrow(args.toIndexedSeq)
    Tableau.debug = false
    val inputFile = File(config.input)
    // When run via sbt fork, the cwd is the subproject dir; resolve relative paths from the repo root
    val resolvedFile = if (inputFile.isAbsolute || inputFile.exists()) inputFile
      else File(sys.props.getOrElse("user.dir", ".")).getParentFile match
        case null => inputFile
        case parent => val candidate = File(parent, config.input); if candidate.exists() then candidate else inputFile
    val result = runBenchmark(resolvedFile, config.timeout, config.verify)
    config.format match {
      case "csv" =>
        println(result.toCSVHeader)
        println(result.toCSV)
      case "verbose" =>
        println(s"Problem:      ${result.problemName}")
        println(s"File:         ${result.file}")
        println(s"Domain:       ${result.domain}")
        println(s"Status:       ${result.status}")
        println(s"SPC:          ${result.spc}")
        println(s"Formulas:     ${result.numFormulas}")
        println(s"Parse time:   ${result.parseTimeMs} ms")
        println(s"Solve time:   ${result.solveTimeMs} ms")
        println(s"Total time:   ${result.totalTimeMs} ms")
        println(s"Solved:       ${result.solved}")
        result.proofValid.foreach(v => println(s"Proof valid:  $v"))
        result.proofSteps.foreach(s => println(s"Proof steps:  $s"))
        result.error.foreach(e => println(s"Error:        $e"))
      case _ =>
        println(result.toString)
    }
  }

  def runBenchmark(problemFile: File, timeoutMs: Long, verify: Boolean): BenchmarkResult = {
    val totalStart = System.currentTimeMillis()

    // Phase 1: Parse the TPTP file
    val parseStart = System.currentTimeMillis()
    val (problem, sequent, parseError) = try {
      val prob = problemToKernel(problemFile)(using strictMapAtom, strictMapTerm, strictMapVariable)
      val seq = problemToSequent(prob)
      (Some(prob), Some(seq), None)
    } catch {
      case e: Exception =>
        (None, None, Some(s"Parse error: ${e.getMessage}"))
    }
    val parseTime = System.currentTimeMillis() - parseStart

    if (problem.isEmpty || sequent.isEmpty) {
      return BenchmarkResult(
        problemName = problemFile.getName.stripSuffix(".p"),
        file = problemFile.getPath,
        domain = "?", status = "?", spc = "?",
        numFormulas = 0,
        parseTimeMs = parseTime,
        solveTimeMs = 0,
        totalTimeMs = System.currentTimeMillis() - totalStart,
        solved = false,
        proofValid = None,
        proofSteps = None,
        error = parseError
      )
    }

    val prob = problem.get
    val seq = sequent.get

    // Phase 2: Run the Tableau solver
    val solveStart = System.currentTimeMillis()
    val (optProof, solveError) =
      if (timeoutMs > 0) {
        // Run with timeout using a separate thread
        val resultHolder = new java.util.concurrent.atomic.AtomicReference[Option[K.SCProof]](None)
        val errorHolder = new java.util.concurrent.atomic.AtomicReference[Option[String]](None)
        val thread = new Thread(() => {
          try {
            resultHolder.set(Tableau.solve(seq))
          } catch {
            case e: Exception =>
              errorHolder.set(Some(s"Solve error: ${e.getMessage}"))
          }
        })
        thread.setDaemon(true)
        thread.start()
        thread.join(timeoutMs)
        if (thread.isAlive) {
          thread.interrupt()
          (None, Some(s"Timeout after ${timeoutMs}ms"))
        } else {
          (resultHolder.get(), errorHolder.get())
        }
      } else {
        try {
          (Tableau.solve(seq), None)
        } catch {
          case e: Exception =>
            (None, Some(s"Solve error: ${e.getMessage}"))
        }
      }
    val solveTime = System.currentTimeMillis() - solveStart

    // Phase 3: Verify the proof if found
    val (proofValid, proofSteps) = optProof match {
      case Some(proof) if verify =>
        val judgement = checkSCProof(proof)
        (Some(judgement.isValid), Some(proof.steps.size))
      case Some(proof) =>
        (None, Some(proof.steps.size))
      case None =>
        (None, None)
    }

    val totalTime = System.currentTimeMillis() - totalStart

    BenchmarkResult(
      problemName = prob.name,
      file = prob.file,
      domain = prob.domain,
      status = prob.status,
      spc = prob.spc.mkString("_"),
      numFormulas = prob.formulas.size,
      parseTimeMs = parseTime,
      solveTimeMs = solveTime,
      totalTimeMs = totalTime,
      solved = optProof.isDefined,
      proofValid = proofValid,
      proofSteps = proofSteps,
      error = solveError.orElse(if (optProof.isEmpty && solveError.isEmpty) Some("No proof found") else None)
    )
  }

}
