package lisa.automation.superposition
package bench

import java.io.File
import java.io.PrintWriter
import java.nio.file.Files
import scala.io.Source
import scala.sys.process.*
import scala.util.Using

/**
 * Runs every configuration of one experiment file and writes one CSV per configuration, one combined CSV, and a
 * provenance record, then prints and writes a report over the combined CSV with [[ExperimentReport]].
 *
 * {{{
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.RunExperiment <experiment> [key=value]…"
 *
 *   ... portfolio-cert limit=3 timeout=20000      a dry run over three problems
 *   ... portfolio-uncert dataset=tptp400          the same experiment on the other dataset
 *   ... path/to/my-experiment.conf                an experiment file of your own
 * }}}
 *
 * The experiment is a file path, or the name of a packaged experiment: `portfolio-uncert` and `portfolio-cert` run
 * each strategy of the portfolio alone on the CASC-J13 FOF problems, without and with certification.
 *
 * Every `key=value` goes to the harness and overrides the file, except these read here:
 *
 *   - `results=<dir>`  where the CSVs go; default `results/` beside the directory holding the experiment file, or
 *                      in the working directory for a packaged experiment
 *   - `force=on`       re-run configurations whose CSV already exists; by default they are skipped, so an
 *                      interrupted run resumes by being started again
 *   - `baseline=<configuration>`, `minHypotheses=<n>`   given to the report, see [[ExperimentReport]]
 *
 * A configuration that fails does not stop the others; the failures are listed at the end and the exit status
 * is non-zero.
 *
 * One `sbt runMain` for the whole experiment, rather than one per configuration. sbt 2 is client/server, and a
 * second `runMain` in the same shell attaches to the server the first one started, leaking its environment and
 * sometimes hanging. A problem still runs in its own forked JVM, as the harness always does.
 *
 * A `portfolio` line is read and ignored: its strategies run here one after another, which measures each of them
 * but not the portfolio, since they do not share a wall clock. Only a launcher that starts them together, one per
 * core, measures that.
 */
object RunExperiment:

  /** The harness entry point every configuration goes through, and the class a forked child re-enters. */
  private def harness(args: Seq[String]): Unit = FofEvaluation.main(args.toArray)

  def main(args: Array[String]): Unit =
    val (confArg, rest) = args.toSeq.partition(a => !a.contains('='))
    val chosen = confArg.headOption.getOrElse {
      Console.err.println("usage: RunExperiment <experiment.conf | portfolio-uncert | portfolio-cert> [key=value]…")
      sys.exit(2)
    }
    val (experiment, lines, confDir, source) = loadExperiment(chosen).getOrElse {
      Console.err.println(s"no such experiment: $chosen (neither a file nor a packaged experiment)")
      sys.exit(2)
    }

    val tptp = BenchUtil.tptpRootOrExplain().getOrElse(sys.exit(2))

    val own = Set("results", "force", "baseline", "minHypotheses")
    def value(key: String, from: Seq[String]): Option[String] =
      from.reverseIterator.collectFirst { case a if a.startsWith(key + "=") => a.drop(key.length + 1) }
    val passthrough = rest.filterNot(a => own.exists(k => a.startsWith(k + "=")))
    val force = value("force", rest).exists(v => Set("on", "true", "1").contains(v.toLowerCase))

    val results = value("results", rest).map(new File(_))
      .getOrElse(confDir.map(d => new File(d.getParentFile, "results")).getOrElse(new File("results")))
    results.mkdirs()

    // ── the file: `defaults` lines apply to every configuration, every other line is one ──────────────────────
    val defaults = lines.filter(_.startsWith("defaults ")).flatMap(_.stripPrefix("defaults ").split("\\s+")).filter(_.nonEmpty)
    val configurations = lines
      .filterNot(l => l.isEmpty || l.startsWith("#") || l.startsWith("defaults ") || l == "portfolio" || l.startsWith("portfolio "))
      .map(l => l.split("\\s+").toSeq)
      .map(ws => (ws.head, ws.tail))

    val overrideDataset = value("dataset", passthrough)
    val tag = s"$experiment-${overrideDataset.orElse(value("dataset", defaults)).getOrElse("mixed")}"
    val combined = new File(results, s"$tag.csv")
    val provenance = new File(results, s"$tag.provenance")

    writeProvenance(provenance, experiment, source, lines, defaults, args.toSeq, tptp)

    // ── one configuration at a time ─────────────────────────────────────────────────────────────────────────
    var failed = Vector.empty[String]
    var header: Option[String] = None
    Using.resource(new PrintWriter(combined, "UTF-8")) { all =>
      for (name, own) <- configurations do
        val args = defaults ++ own
        val dataset = overrideDataset.orElse(value("dataset", args)).getOrElse {
          Console.err.println(s"configuration '$name' names no dataset"); sys.exit(2)
        }
        val list = resolveDataset(dataset, confDir).getOrElse {
          Console.err.println(s"no such dataset: $dataset"); sys.exit(2)
        }
        val out = new File(results, s"$tag-$name.csv")

        val ran =
          if out.length() > 0 && !force then
            println(s"=== $experiment / $name: already done, skipping (force=on to redo)")
            true
          else
            println(s"=== $experiment / $name")
            try
              harness(Seq("files", list.getPath) ++ args ++ Seq(s"dataset=$dataset", s"config=$name", s"out=${out.getPath}") ++ passthrough)
              out.isFile
            catch
              case e: Throwable =>
                Console.err.println(s"!!! $experiment / $name failed: ${e.getClass.getSimpleName}: ${e.getMessage}")
                false

        if !ran then failed :+= name
        else
          // The first configuration contributes the header, the rest only their rows.
          val rows = Using.resource(Source.fromFile(out, "UTF-8"))(_.getLines().toVector)
          if header.isEmpty then
            header = rows.headOption
            rows.headOption.foreach(all.println)
          rows.drop(1).foreach(all.println)
    }

    val count = Using.resource(Source.fromFile(combined, "UTF-8"))(_.getLines().size - 1).max(0)
    println()
    println(s"combined: $combined ($count rows)")
    println(s"recorded: $provenance")

    // The report reads the combined CSV rather than what this run holds in memory, so a fresh run and an old
    // file are reported the same way. The budget charged for an unsolved problem is the experiment's own.
    if count > 0 then
      println()
      val reportOpts = Map("budget" -> value("timeout", passthrough).orElse(value("timeout", defaults)).getOrElse("180000"))
        ++ value("baseline", rest).map("baseline" -> _)
        ++ value("minHypotheses", rest).map("minHypotheses" -> _)
      ExperimentReport.write(Seq(combined), Some(new File(results, s"$tag.md")), reportOpts)

    if failed.nonEmpty then
      Console.err.println(s"failed configurations: ${failed.mkString(" ")}")
      sys.exit(1)

  /** Where the packaged datasets and experiments live on the classpath. */
  private val resourceDir = "/lisa/automation/superposition"

  /**
   * The experiment an argument refers to: the file at that path if one exists, else the packaged experiment of that
   * name. Returns its name, its trimmed lines, the directory holding the file (none for a packaged one) and where
   * it came from, for the provenance record.
   */
  private def loadExperiment(arg: String): Option[(String, Vector[String], Option[File], String)] =
    val file = new File(arg)
    if file.isFile then
      val lines = Using.resource(Source.fromFile(file, "UTF-8"))(_.getLines().toVector).map(_.trim)
      Some((file.getName.stripSuffix(".conf"), lines, Some(file.getAbsoluteFile.getParentFile), file.getPath))
    else
      val name = arg.stripSuffix(".conf")
      val path = s"$resourceDir/$name.conf"
      Option(getClass.getResourceAsStream(path)).map { in =>
        val lines = Using.resource(Source.fromInputStream(in, "UTF-8"))(_.getLines().toVector).map(_.trim)
        (name, lines, None, s"classpath:$path")
      }

  /**
   * The problem list a dataset name refers to: a file of that name if one exists, then `datasets/<name>.txt`
   * beside the experiment directory, then the packaged list of that name on the classpath, copied to a temporary
   * file since the harness reads a list from disk.
   */
  private def resolveDataset(name: String, confDir: Option[File]): Option[File] =
    val direct = new File(name)
    val sibling = confDir.map(d => new File(d.getParentFile, s"datasets/$name.txt"))
    if direct.isFile then Some(direct)
    else if sibling.exists(_.isFile) then sibling
    else
      Option(getClass.getResourceAsStream(s"$resourceDir/$name.txt")).map { in =>
        val tmp = Files.createTempFile(s"$name-", ".txt")
        try Files.copy(in, tmp, java.nio.file.StandardCopyOption.REPLACE_EXISTING)
        finally in.close()
        tmp.toFile.deleteOnExit()
        tmp.toFile
      }

  /** What produced these results: when, where, from which revision and against which TPTP, with what settings. */
  private def writeProvenance(f: File, experiment: String, source: String, lines: Vector[String], defaults: Seq[String],
                              args: Seq[String], tptp: File): Unit =
    def quiet(cmd: Seq[String]): Option[String] =
      scala.util.Try(cmd.!!(ProcessLogger(_ => ()))).toOption.map(_.trim).filter(_.nonEmpty)
    val rev = quiet(Seq("git", "rev-parse", "HEAD")).getOrElse("unknown")
    val dirty = scala.util.Try(Seq("git", "diff", "--quiet").!(ProcessLogger(_ => ()))).toOption.exists(_ != 0)
    Using.resource(new PrintWriter(f, "UTF-8")) { w =>
      w.println(s"experiment: $experiment")
      w.println(s"file:       $source")
      w.println(s"date:       ${java.time.OffsetDateTime.now()}")
      w.println(s"host:       ${System.getProperty("os.name")} ${System.getProperty("os.version")} ${quiet(Seq("hostname")).getOrElse("")}")
      w.println(s"git:        $rev${if dirty then " (dirty)" else ""}")
      w.println(s"tptp:       ${tptp.getPath}")
      w.println(s"java:       ${System.getProperty("java.vm.name")} ${System.getProperty("java.version")}")
      w.println(s"heap:       ${Runtime.getRuntime.maxMemory / (1024 * 1024)} MB")
      w.println(s"command:    RunExperiment ${args.mkString(" ")}")
      if defaults.nonEmpty then w.println(s"defaults:   ${defaults.mkString(" ")}")
      w.println("--")
      lines.filterNot(l => l.isEmpty || l.startsWith("#")).foreach(w.println)
    }
