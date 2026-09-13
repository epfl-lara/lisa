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
 * Builds the problem lists that [[ProblemList]] reads, directly into the classpath resources.
 *
 * {{{
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.BuildDatasets"
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.BuildDatasets seed=7 size=50"
 * }}}
 *
 * The pool is every problem of the TPTP library whose SPC marks it refutable and first-order. From it this
 * writes:
 *
 *   - `tptp-eligible-fof.txt` and `tptp-eligible-cnf.txt`, the whole pool split by form;
 *   - `tptp<size>.txt`, a seeded draw of `size` problems from the pool minus the CASC-J13 problems, so that
 *     the draw and the CASC list are independent halves of a benchmark.
 *
 * A list that already exists is left as it is, so the committed lists never change under a rerun and only a
 * missing one is written; delete a list to rebuild it. The CASC list cannot be rebuilt from the library, being
 * the competition's own, so it is only checked: every path in it must resolve.
 *
 * @param seed the draw's seed (default 42)
 * @param size how many problems to draw (default 400)
 * @param root the repository, if it cannot be found by walking up from the working directory
 */
object BuildDatasets:

  /** A problem and its Specialist Problem Class. */
  private case class Entry(path: String, spc: String):
    def form: String = spc.takeWhile(_ != '_') // FOF or CNF

  /** Refutable and first order: all this prover can attempt at all. */
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
    // Sorted, so neither the lists nor the draw depend on the order the file system handed the library over.
    val eligible = pool.sortBy(_.path)

    // ── the whole pool, by form ─────────────────────────────────────────────────────────────────
    writeIfAbsent(new File(resources, "tptp-eligible-fof.txt"), eligible.filter(_.form == "FOF").map(_.path))
    writeIfAbsent(new File(resources, "tptp-eligible-cnf.txt"), eligible.filter(_.form == "CNF").map(_.path))

    // ── the draw ────────────────────────────────────────────────────────────────────────────────
    //
    // Shuffled exactly as [[ProblemList.sample]] shuffles, so there is one notion of "seeded draw" in the project.
    val drawPool = eligible.filterNot(e => casc(e.path))
    println(s"draw pool: ${describe(drawPool)} after excluding the ${casc.size} CASC problems")
    val drawn = new scala.util.Random(seed).shuffle(drawPool).take(size).sortBy(_.path)
    writeIfAbsent(new File(resources, s"tptp$size.txt"), drawn.map(_.path))

    // ── verify the CASC list ────────────────────────────────────────────────────────────────────
    //
    // Every path must resolve, or a run silently measures fewer problems than it reports.
    val missing = casc.toSeq.sorted.filterNot(p => new File(tptp, p).isFile)
    missing.foreach(p => println(s"  missing: $p"))
    if missing.nonEmpty then
      println(s"${missing.size} CASC problems are not in this TPTP installation")
      sys.exit(1)
    println(s"verified ${cascFile.getName}: all ${casc.size} problems present")

  /**
   * Every problem in the library with the Specialist Problem Class from its header: `FOF_THM_RFO_SEQ` is a
   * first-order formula problem whose status is Theorem, with equality. Problems without the header — there
   * are none in a well-formed installation — are dropped.
   *
   * The header sits within the first hundred lines or so, after the `Syntax` block, so reading stops there
   * rather than at the end of a file that may be hundreds of megabytes. Latin-1, because the decoder must not
   * throw on a stray byte in a comment.
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

  /** A library-relative path, always with `/`: the lists are read on every platform. */
  private def relative(base: Path, p: Path): String = base.relativize(p).toString.replace('\\', '/')

  /** `n (f FOF, c CNF)`, the shape of a set of problems in one phrase. */
  private def describe(es: Seq[Entry]): String =
    val fof = es.count(_.form == "FOF")
    s"${es.size} ($fof FOF, ${es.size - fof} CNF)"

  /** The repository: the nearest enclosing directory holding both `build.sbt` and `lisa-sets`. */
  private def repositoryRoot: Option[File] =
    Iterator
      .iterate(new File(".").getAbsoluteFile.getCanonicalFile)(_.getParentFile)
      .takeWhile(_ != null)
      .find(d => new File(d, "build.sbt").isFile && new File(d, "lisa-sets").isDirectory)

  private def readLines(f: File): Vector[String] =
    Using(Source.fromFile(f))(_.getLines().map(_.trim).filter(_.nonEmpty).toVector).get

  /**
   * Write `lines` to `f` unless it already exists, saying which happened. Each line ends in `\n` rather than the
   * platform's separator, so a list built on Windows is byte for byte the list built anywhere else.
   */
  private def writeIfAbsent(f: File, lines: Seq[String]): Unit =
    if f.exists then println(s"kept  ${f.getName}: already exists, delete it to rebuild")
    else
      Files.writeString(f.toPath, lines.map(_ + "\n").mkString, java.nio.charset.StandardCharsets.UTF_8)
      println(s"wrote ${f.getName}: ${lines.size} problems")
