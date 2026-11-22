package lisa

import org.scalatest.funsuite.AnyFunSuite

import java.io.File
import java.net.URLClassLoader
import java.nio.file.Files
import java.nio.file.Path
import java.util.concurrent.TimeUnit

/**
 * Checks the runner in separate JVMs so an expected failure cannot terminate the test runner.
 */
class MainExitSuite extends AnyFunSuite:
  private def run(name: String): (Int, String) =
    val output = Files.createTempFile("lisa-main-exit-", ".log")
    val java = Path.of(sys.props("java.home"), "bin", if sys.props("os.name").startsWith("Windows") then "java.exe" else "java").toString
    // sbt loads test classes separately from the JVM's launcher classpath.
    val testClasspath = Iterator
      .iterate(getClass.getClassLoader)(_.getParent)
      .takeWhile(_ != null)
      .collect { case loader: URLClassLoader => loader.getURLs.toSeq }
      .flatten
      .filter(_.getProtocol == "file")
      .map(url => Path.of(url.toURI).toString)
      .toSeq
    val classpath = (testClasspath :+ sys.props("java.class.path")).mkString(File.pathSeparator)
    val process = new ProcessBuilder(java, "-Dfile.encoding=UTF-8", "-cp", classpath, s"lisa.$name")
      .redirectErrorStream(true)
      .redirectOutput(output.toFile)
      .start()
    try
      assert(process.waitFor(60, TimeUnit.SECONDS), s"$name did not finish")
      (process.exitValue(), Files.readString(output))
    finally
      if process.isAlive then process.destroyForcibly().waitFor()
      Files.deleteIfExists(output)

  test("a successful development exits with status zero"):
    val (status, output) = run("SuccessfulMainFixture")
    assert(status == 0, output)
    assert(output.contains("Theorem valid"))
    assert(!output.contains("Proof error"))

  test("all recovered errors and later declarations are printed before exit status one"):
    val (status, output) = run("FailingMainFixture")
    assert(status == 1, output)
    val first = output.indexOf("first failure")
    val second = output.indexOf("second failure")
    val last = output.indexOf("Theorem afterFailures")
    assert(first >= 0 && second > first && last > second, output)
    assert("-- Proof error:".r.findAllIn(output).length == 2, output)

  test("explicit sorry without a recorded error does not fail the run"):
    val (status, output) = run("AdmittedMainFixture")
    assert(status == 0, output)
    assert(output.contains("Theorem admitted"))

  test("dependency errors print once while successful imported declarations stay buffered"):
    val (status, output) = run("DependentMainFixture")
    assert(status == 1, output)
    assert(output.contains("Theorem reused"))
    assert(output.contains("first failure") && output.contains("second failure"), output)
    assert("-- Proof error:".r.findAllIn(output).length == 2, output)
    assert(output.contains("Theorem first :=") && output.contains("Theorem second :="), output)
    assert(!output.contains("Theorem afterFailures"), output)

  test("dependency diagnostics remain visible if initialization later aborts"):
    val (status, output) = run("AbortingDependentMainFixture")
    assert(status != 0, output)
    assert(output.contains("first failure") && output.contains("second failure"), output)
    assert("-- Proof error:".r.findAllIn(output).length == 2, output)
    assert(output.contains("abort after importing"), output)
    assert(!output.contains("Theorem afterFailures"), output)

/**
 * A clean development used by the process-exit tests.
 */
object SuccessfulMainFixture extends Main:
  private val p = variable[Prop]
  val valid = Theorem(p |- p) { have(thesis) by Hypothesis }

/**
 * A development that recovers twice and then proves another theorem.
 */
object FailingMainFixture extends Main:
  private val p = variable[Prop]
  val first = Theorem(p) { lisa.utils.prooflib.ProofCarrier.Failure("first failure") }
  val second = Theorem(p) { lisa.utils.prooflib.ProofCarrier.Failure("second failure") }
  val afterFailures = Theorem(p |- p) { have(thesis) by Hypothesis }

/**
 * An intentional admission is not a recovered proof error.
 */
object AdmittedMainFixture extends Main:
  private val p = variable[Prop]
  val admitted = Theorem(p) { have(thesis) by Sorry }

/**
 * Imports a theorem with a recorded error without producing a new diagnostic.
 */
object DependentMainFixture extends Main:
  val reused = Theorem(FailingMainFixture.first.statement) { have(FailingMainFixture.first) }

/**
 * Aborts after loading a failed development, before the runner can flush ordinary output.
 */
object AbortingDependentMainFixture extends Main:
  val imported = FailingMainFixture.first
  throw new IllegalStateException("abort after importing")
