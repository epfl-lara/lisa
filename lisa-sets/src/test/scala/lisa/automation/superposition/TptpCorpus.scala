package lisa.automation.superposition

import java.io.File
import java.util.concurrent.atomic.AtomicBoolean

/**
 * The TPTP corpus that the corpus-backed tests need, and — the point of this object — a loud warning when it
 * is absent.
 *
 * Roughly 40 of the suite's tests are `assume`d on the `TPTP` environment variable: without it they are
 * *cancelled*, not failed, which keeps the suite portable but makes a green run mean much less than it looks.
 * ScalaTest reports cancellations in a count most readers skim past ("canceled 41"), and the headline line
 * still says `All tests passed`. Among the tests that vanish are the entire uncertified/certified naming
 * equivalence check and the SYN reconstruction suite — i.e. exactly the evidence that the clausifier and the
 * proof reconstruction work on real input.
 *
 * So the first test to ask for the corpus and not find it prints a banner. That is deliberately all it does:
 * failing instead would make the suite unrunnable without a multi-gigabyte download, which is the trade the
 * `assume` was making in the first place. The warning just stops the trade from being silent.
 */
object TptpCorpus:

  /** The TPTP root — the directory containing `Problems/` — when `TPTP` names a real directory. */
  val root: Option[File] = sys.env.get("TPTP").map(new File(_)).filter(_.isDirectory)

  private val warned = new AtomicBoolean(false)

  /** Print the missing-corpus banner, once per JVM however many tests ask. */
  private def warnOnce(): Unit =
    if root.isEmpty && warned.compareAndSet(false, true) then
      // stdout, framed: it has to survive being scrolled past in a wall of test output, and it belongs in the
      // same stream as the report it is qualifying. Not stderr — sbt's test output is stdout, so a warning on
      // stderr can land out of order in a redirected log, and PowerShell turns any native-command stderr into
      // a `NativeCommandError` that makes a passing run look failed.
      println(
        s"""|
            |${"!" * 100}
            |!! TPTP corpus not found: the `TPTP` environment variable is unset or is not a directory.
            |!!
            |!! The corpus-backed tests are being CANCELLED, not run. ScalaTest will still print
            |!! "All tests passed" — it means "all tests that ran", and the ones skipped are the ones that
            |!! check the clausifier and the proof reconstruction against real problems.
            |!!
            |!! To run them, point TPTP at the directory containing Problems/:
            |!!     PowerShell   $$env:TPTP = "C:\\path\\to\\TPTP-v9.2.1"
            |!!     bash         export TPTP=/path/to/TPTP-v9.2.1
            |${"!" * 100}
            |""".stripMargin)

  /** The TPTP root, or cancel the calling test — having warned — when the corpus is absent. `what` names the
    * suite in the cancellation message, so a reader of the report can tell which coverage went missing. */
  def rootOrCancel(what: String): File =
    warnOnce()
    org.scalatest.Assertions.assume(root.isDefined, s"set TPTP to the directory containing Problems/ to run $what")
    root.get

  /** As [[rootOrCancel]], for a suite that wants a subdirectory such as `Problems/SYN`. */
  def subdirOrCancel(relative: String, what: String): File =
    val dir = new File(rootOrCancel(what), relative)
    org.scalatest.Assertions.assume(dir.isDirectory, s"$dir not found (TPTP is set, but the corpus looks incomplete)")
    dir
