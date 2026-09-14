package lisa.automation.superposition
package bench

import java.io.File
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Path
import scala.io.Codec
import scala.io.Source
import scala.jdk.StreamConverters._
import scala.util.Using

/**
 * Builds the problem lists that [[ProblemList]] reads, into the classpath resources.
 *
 * {{{
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.BuildDatasets"
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.BuildDatasets seed=7 size=50"
 * }}}
 *
 * From the TPTP problems whose SPC is refutable and first-order, writes `tptp-eligible-fof.txt`,
 * `tptp-eligible-cnf.txt`, and `tptp<size>.txt`, a seeded draw disjoint from the CASC-J13 list. Existing lists are
 * kept; delete one to rebuild it. The CASC list is only checked for missing problems.
 *
 *   - `seed=<n>`    the draw's seed, default 42
 *   - `size=<n>`    how many problems to draw, default 400
 *   - `root=<dir>`  the repository, if not found above the working directory
 */
object BuildDatasets:

  /**
   * A problem and its Specialist Problem Class.
   */
  private case class Entry(path: String, spc: String):
    def form: String = spc.takeWhile(_ != '_') // FOF or CNF

  /**
   * Refutable and first order: what this prover can attempt.
   */
  private val eligibleSpc = "^(FOF_(THM|UNS|CAX)|CNF_UNS)_".r

  def main(args: Array[String]): Unit =
    val opts = args.flatMap(a => a.split("=", 2) match { case Array(k, v) => Some(k -> v); case _ => None }).toMap
    val seed = opts.get("seed").map(_.toLong).getOrElse(42L)
    val size = opts.get("size").map(_.toInt).getOrElse(400)

    val tptp = BenchUtil.tptpRootOrExplain().getOrElse(sys.exit(2))
    val repo = opts.get("root").map(new File(_)).orElse(repositoryRoot).getOrElse {
      println("Could not find the repository from the working directory; pass root=<path>.")
      sys.exit(2)
    }
    val resources = new File(repo, "lisa-sets/src/main/resources/lisa/automation/superposition")
    if !resources.isDirectory then
      println(s"no resources directory at $resources")
      sys.exit(2)

    // ── the pool ────────────────────────────────────────────────────────────────────────────────
    val scanned = scan(tptp)
    println(s"scanned ${scanned.size} problems with an SPC header")
    val pool = scanned.filter(e => eligibleSpc.findPrefixOf(e.spc).isDefined)
    println(s"pool: ${describe(pool)} refutable first-order problems")

    val cascFile = new File(resources, "casc-j13-fof.txt")
    if !cascFile.isFile then
      println(s"no CASC list at $cascFile")
      sys.exit(2)
    val casc = readLines(cascFile).toSet
    // Sorted, so the output does not depend on file system order.
    val eligible = pool.sortBy(_.path)

    // ── the whole pool, by form ─────────────────────────────────────────────────────────────────
    writeIfAbsent(new File(resources, "tptp-eligible-fof.txt"), eligible.filter(_.form == "FOF").map(_.path))
    writeIfAbsent(new File(resources, "tptp-eligible-cnf.txt"), eligible.filter(_.form == "CNF").map(_.path))

    // ── the draw ────────────────────────────────────────────────────────────────────────────────
    // Shuffled as [[ProblemList.sample]] does.
    val drawPool = eligible.filterNot(e => casc(e.path))
    println(s"draw pool: ${describe(drawPool)} after excluding the ${casc.size} CASC problems")
    val drawn = new scala.util.Random(seed).shuffle(drawPool).take(size).sortBy(_.path)
    writeIfAbsent(new File(resources, s"tptp$size.txt"), drawn.map(_.path))

    // ── verify the CASC list ────────────────────────────────────────────────────────────────────
    // A missing path would silently shrink a run.
    val missing = casc.toSeq.sorted.filterNot(p => new File(tptp, p).isFile)
    missing.foreach(p => println(s"  missing: $p"))
    if missing.nonEmpty then
      println(s"${missing.size} CASC problems are not in this TPTP installation")
      sys.exit(1)
    println(s"verified ${cascFile.getName}: all ${casc.size} problems present")

  /**
   * Every library problem with the SPC from its header. Only the first lines are read, since files can be huge,
   * and as Latin-1 so that a stray byte cannot throw.
   */
  private def scan(tptp: File): Vector[Entry] =
    val root = tptp.toPath.resolve("Problems")
    val files = Using(Files.walk(root, 2))(_.toScala(Vector).filter(p => Files.isRegularFile(p) && p.toString.endsWith(".p"))).get
    files.flatMap { p =>
      val spc = Using(Source.fromFile(p.toFile)(using Codec.ISO8859)) { src =>
        src.getLines().take(120).collectFirst { case l if l.startsWith("% SPC") => l.dropWhile(_ != ':').drop(1).trim }
      }.toOption.flatten
      spc.map(s => Entry(relative(root.getParent, p), s))
    }

  /**
   * A library-relative path, always with `/`: the lists are read on every platform.
   */
  private def relative(base: Path, p: Path): String = base.relativize(p).toString.replace('\\', '/')

  /**
   * `n (f FOF, c CNF)`, the shape of a set of problems in one phrase.
   */
  private def describe(es: Seq[Entry]): String =
    val fof = es.count(_.form == "FOF")
    s"${es.size} ($fof FOF, ${es.size - fof} CNF)"

  /**
   * The repository: the nearest enclosing directory holding both `build.sbt` and `lisa-sets`.
   */
  private def repositoryRoot: Option[File] =
    Iterator
      .iterate(new File(".").getAbsoluteFile.getCanonicalFile)(_.getParentFile)
      .takeWhile(_ != null)
      .find(d => new File(d, "build.sbt").isFile && new File(d, "lisa-sets").isDirectory)

  private def readLines(f: File): Vector[String] =
    Using(Source.fromFile(f))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get

  /**
   * Write `lines` to `f` unless it exists, ending lines in `\n` so the file is the same on every platform.
   */
  private def writeIfAbsent(f: File, lines: Seq[String]): Unit =
    if f.exists then println(s"kept  ${f.getName}: already exists, delete it to rebuild")
    else
      Files.writeString(f.toPath, lines.map(_ + "\n").mkString, java.nio.charset.StandardCharsets.UTF_8)
      println(s"wrote ${f.getName}: ${lines.size} problems")
