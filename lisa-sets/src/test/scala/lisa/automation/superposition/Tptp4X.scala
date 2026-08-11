package lisa.automation.superposition

import java.io.File
import java.nio.file.Files
import java.util.concurrent.atomic.AtomicBoolean

import scala.util.Using

/**
 * The official TPTP syntax checker, `tptp4X`, as a test oracle.
 *
 * It ships with the TPTP distribution (`$TPTP/Scripts/tptp4X`), so no download and no network are involved.
 * It is worth having in addition to re-parsing with `lisa.tptp`'s own parser: an *independent* checker rejects
 * things ours accepts, and it is the checker CASC itself applies to a submitted derivation. It caught the
 * applied-naming-atom defect (`X0(X1)` — "Variables cannnot have arguments") that our round-trip did not.
 *
 * What it does **not** check is that the derivation follows from its leaves — a proof naming two distinct
 * Skolem constants identically is syntactically perfect. That needs a separate assertion (or GDV, which is
 * only available online); see `CascProverTest`.
 *
 * The binary is a Linux ELF, so on Windows it is invoked through WSL. When it cannot be run at all — no TPTP
 * distribution, no WSL — the tests that use it cancel with a warning rather than fail, so the suite stays
 * portable; the same trade [[TptpCorpus]] makes, and just as deliberately.
 */
object Tptp4X:

  private def isWindows: Boolean = System.getProperty("os.name").toLowerCase.contains("win")

  /** `$TPTP/Scripts/tptp4X`, if the distribution is present. */
  lazy val binary: Option[File] =
    TptpCorpus.root.map(r => new File(r, "Scripts/tptp4X")).filter(_.isFile)

  /** `C:\a\b` → `/mnt/c/a/b`; already-POSIX paths pass through. */
  private def wslPath(f: File): String =
    val p = f.getAbsolutePath.replace('\\', '/')
    if p.length > 2 && p(1) == ':' then s"/mnt/${p(0).toLower}${p.substring(2)}" else p

  private def run(input: File): Option[(Int, String)] =
    binary.flatMap { exe =>
      val cmd =
        if isWindows then java.util.List.of("wsl", "-e", wslPath(exe), "-q2", wslPath(input))
        else java.util.List.of(exe.getAbsolutePath, "-q2", input.getAbsolutePath)
      try
        val p = new ProcessBuilder(cmd).redirectErrorStream(true).start()
        p.getOutputStream.close()
        val out = Using(scala.io.Source.fromInputStream(p.getInputStream))(_.mkString).getOrElse("")
        Some((if p.waitFor(60, java.util.concurrent.TimeUnit.SECONDS) then p.exitValue else { p.destroyForcibly(); -1 }, out))
      catch case _: Throwable => None // no WSL, wrong architecture, not executable — treat as unavailable
    }

  /** Probed once: can we actually run it here? Checks against a trivially valid clause rather than trusting
    * that the file exists — the binary is useless on a machine with no WSL, and that must not read as a pass. */
  lazy val available: Boolean =
    val probe = Files.createTempFile("tptp4x-probe-", ".p")
    try
      Files.writeString(probe, "cnf(probe,plain,( p(a) | ~q(X) )).\n")
      run(probe.toFile).exists { case (code, _) => code == 0 }
    finally Files.deleteIfExists(probe)

  private val warned = new AtomicBoolean(false)

  /** Cancel the calling test — having said why, once — when the checker cannot be run. */
  def orCancel(what: String): Unit =
    if !available && warned.compareAndSet(false, true) then
      println(
        s"""|
            |${"-" * 100}
            |-- tptp4X is not runnable here, so the TPTP syntax checks are being CANCELLED, not run.
            |-- Needs $$TPTP/Scripts/tptp4X (present: ${binary.isDefined})${if isWindows then ", and WSL to run the Linux binary" else ""}.
            |${"-" * 100}
            |""".stripMargin)
    org.scalatest.Assertions.assume(available, s"tptp4X is unavailable, so $what cannot be checked")

  /** Check a TPTP document. `None` if accepted; `Some(diagnostic)` if rejected. */
  def check(content: String): Option[String] =
    val f = Files.createTempFile("tptp4x-", ".p")
    try
      Files.writeString(f, content)
      run(f.toFile) match
        case Some((0, out)) if !out.contains("ERROR") => None
        case Some((code, out)) => Some(s"exit=$code${if out.trim.isEmpty then "" else s"\n${out.trim.linesIterator.take(5).mkString("\n")}"}")
        case None => Some("tptp4X could not be run")
    finally Files.deleteIfExists(f)
