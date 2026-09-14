package lisa.automation.superposition
package bench

import java.io.File
import java.io.PrintWriter
import scala.io.Source
import scala.util.Using

/**
 * A summary of result CSVs written by [[RunExperiment]], printed and optionally written as Markdown.
 *
 * {{{
 *   sbt "lisa-sets/runMain lisa.automation.superposition.bench.ExperimentReport <results.csv>… [key=value]…"
 * }}}
 *
 * Several files are merged to compare runs on one dataset; do not merge files from different datasets.
 *
 *   - `out=<file.md>`             also write the report there
 *   - `budget=<ms>`               time charged for an unsolved problem, default 180000
 *   - `baseline=<configuration>`  compare every other configuration against this one
 *   - `minHypotheses=<n>`         repeat that comparison on problems with at least `n` hypotheses
 *
 * Columns are read by name.
 */
object ExperimentReport:

  def main(args: Array[String]): Unit =
    val (files, flags) = args.toSeq.partition(a => !a.contains('='))
    val opts = flags.flatMap(a => a.split("=", 2) match { case Array(k, v) => Some(k -> v); case _ => None }).toMap
    if files.isEmpty then
      Console.err.println("usage: ExperimentReport <results.csv>… [out=<file.md>] [budget=<ms>] [baseline=<configuration>] [minHypotheses=<n>]")
      sys.exit(2)
    val missing = files.filterNot(f => new File(f).isFile)
    if missing.nonEmpty then
      Console.err.println(s"no such file: ${missing.mkString(", ")}")
      sys.exit(2)
    write(files.map(new File(_)), opts.get("out").map(new File(_)), opts)

  /**
   * The report over `csvs`, printed, and also written to `out` when given.
   */
  def write(csvs: Seq[File], out: Option[File], opts: Map[String, String]): Unit =
    val rows = csvs.flatMap(readCsv).map(Row.apply).toVector
    val budget = opts.get("budget").flatMap(_.toLongOption).getOrElse(180000L)
    val md = new StringBuilder
    def say(s: String): Unit = { println(s); md ++= s; md += '\n' }

    val configs = rows.map(_.config).filter(_.nonEmpty).distinct.sorted
    val problems = rows.map(_.problem).distinct
    say("# Results\n")
    say(s"${rows.size} rows, ${problems.size} problems, configurations: ${configs.mkString(", ")}\n")

    // ── strategies ──────────────────────────────────────────────────────────────────────────────────────────
    // Only for configurations with several strategies. The last row is the union over strategies.
    val multiStrategy = configs.filter(c => rows.filter(_.config == c).map(_.strategy).distinct.size > 1)
    if multiStrategy.nonEmpty then
      say("## Strategies\n")
      say("| configuration | strategy | solved |")
      say("|---|---|---:|")
      for c <- multiStrategy do
        val rs = rows.filter(_.config == c)
        val byStrategy = rs.groupBy(_.strategy).view.mapValues(_.count(_.solved)).toSeq.sortBy(-_._2)
        for (s, n) <- byStrategy do say(s"| $c | $s | $n |")
        val any = rs.filter(_.solved).map(_.problem).distinct.size
        say(s"| **$c** | **any strategy** | **$any** |")
        byStrategy.headOption.foreach((s, n) => say(s"\nAny strategy solves $any; the best single one, $s, solves $n.\n"))

    // ── solved, and where the time went ─────────────────────────────────────────────────────────────────────
    // An unsolved problem is charged the budget, so solving fewer is not rewarded.
    say("## Solved and time\n")
    say(s"Total time is over every problem, charging an unsolved one the ${budget / 1000} s budget. Phase columns are summed over the configuration's own refutations.\n")
    say("| configuration | solved | unchecked | total time (s) | clausify | search | reconstruct | check |")
    say("|---|---:|---:|---:|---:|---:|---:|---:|")
    for c <- configs do
      val rs = rows.filter(_.config == c)
      val solved = rs.filter(_.solved).map(_.problem).toSet
      val unchecked = rs.filter(_.s("verdict") == "UNCHECKED").map(_.problem).toSet -- solved
      val perProblem = rs.groupBy(_.problem).map { (_, v) =>
        v.filter(_.solved).flatMap(_.totalMs) match
          case xs if xs.nonEmpty => xs.min
          case _ => budget.toDouble
      }
      def phase(k: String): Double = rs.filter(_.solved).flatMap(_.d(k)).sum / 1000.0
      say(
        f"| $c | ${solved.size} | ${unchecked.size} | ${perProblem.sum / 1000.0}%.0f | ${phase("clausify_ms")}%.0f | ${phase("search_ms")}%.0f | ${phase("reconstruct_ms")}%.0f | ${phase("check_ms")}%.0f |"
      )
    say("\n`unchecked` counts problems whose proof was built but whose kernel check did not finish within the budget.\n")

    // ── coverage ────────────────────────────────────────────────────────────────────────────────────────────
    // Expected rows come from every problem in the file, not from the rows a configuration has.
    val verdicts = rows.groupBy(_.s("verdict")).view.mapValues(_.size).toMap
    say("## Coverage\n")
    say("| configuration | rows | expected | |")
    say("|---|---:|---:|---:|")
    for c <- configs do
      val rs = rows.filter(_.config == c)
      val want = problems.size * rs.map(_.strategy).distinct.size.max(1)
      val pct = if want == 0 then 100.0 else 100.0 * rs.size / want
      say(f"| $c | ${rs.size} | $want | $pct%.1f%% |")
    say("\nverdicts: " + verdicts.toSeq.sortBy(-_._2).map((v, n) => s"`$v`=$n").mkString(", "))
    val lost = verdicts.getOrElse("KILLED", 0) + verdicts.getOrElse("EXHAUSTED", 0)
    if lost > 0 then
      val pct = 100.0 * lost / rows.size
      say(f"\n$lost rows ($pct%.1f%% of the file) carry no measurement, being `KILLED` or `EXHAUSTED`.")
      if pct > 10.0 then say("**Over a tenth of the rows report nothing; check that the budget leaves room for the answer to be written.**")
    say("")

    // ── near the budget ─────────────────────────────────────────────────────────────────────────────────────
    // Such a problem may not be solved on a rerun, so this count tells noise from a real difference.
    say("Solved inside the last tenth of the budget, and so able to move between runs:\n")
    say("| configuration | solved | near the budget |")
    say("|---|---:|---:|")
    for c <- configs do
      val ts = solvedTimes(rows, c)
      say(s"| $c | ${ts.size} | ${ts.count(_._2 > 0.9 * budget)} |")
    say("")

    // ── against a baseline, when `baseline=` names one ──────────────────────────────────────────────────────
    for base <- opts.get("baseline") do
      if !configs.contains(base) then Console.err.println(s"baseline '$base' is not one of: ${configs.mkString(", ")}")
      else
        val others = configs.filterNot(_ == base)
        val baseSolved = solvedTimes(rows, base).size
        say(s"## Against `$base`\n")
        say("| configuration | solved | change | attempted | both solved | time vs baseline |")
        say("|---|---:|---:|---:|---:|---:|")
        for c <- base +: others.sortBy(c => -solvedTimes(rows, c).size) do
          val n = solvedTimes(rows, c).size
          val attempted = rows.count(_.config == c)
          val (shared, a, b) = bothSolved(rows, base, c)
          val delta = if c == base then "—" else f"${n - baseSolved}%+d"
          val ratio = if c == base || shared == 0 || a == 0 then "—" else f"${b / a}%.2fx"
          say(f"| $c | $n | $delta | $attempted | $shared | $ratio |")
        say("\n`attempted` is how many rows arrived: a configuration with fewer lost problems to killed workers, so part of its change is missing attempts rather than failures.\n")

        // Only the problems where the compared mechanism can act, e.g. enough hypotheses for SInE to filter.
        for min <- opts.get("minHypotheses").flatMap(_.toIntOption) do
          val big = rows.filter(_.i("hypotheses").exists(_ >= min)).map(_.problem).toSet
          say(s"Restricted to the ${big.size} problems with at least $min hypotheses:\n")
          say("| configuration | solved | of those problems |")
          say("|---|---:|---:|")
          for c <- base +: others do
            val n = rows.count(r => r.config == c && r.solved && big.contains(r.problem))
            say(s"| $c | $n | ${rows.count(r => r.config == c && big.contains(r.problem))} |")
          say("")

    // ── clausification-only runs ────────────────────────────────────────────────────────────────────────────
    // No search, so only proof sizes and times, over the problems every such configuration clausified.
    val clausifyOnly = configs.filter(c => rows.exists(r => r.config == c && r.s("verdict") == "CLAUSIFIED"))
    if clausifyOnly.nonEmpty then
      val done = clausifyOnly.map(c => c -> rows.filter(r => r.config == c && r.s("verdict") == "CLAUSIFIED").map(r => r.problem -> r).toMap).toMap
      val shared = clausifyOnly.map(c => done(c).keySet).reduce(_ intersect _)
      say("## Clausification\n")
      say(s"Over the ${shared.size} problems every configuration clausified.\n")
      say("| configuration | clausify (s) | check (s) | proof steps | raw size | shared size | sharing |")
      say("|---|---:|---:|---:|---:|---:|---:|")
      for c <- clausifyOnly do
        val rs = shared.toSeq.map(done(c))
        def sum(k: String): Double = rs.flatMap(_.d(k)).sum
        val raw = sum("raw_size")
        val shr = sum("shared_size")
        say(f"| $c | ${sum("clausify_ms") / 1000.0}%.1f | ${sum("check_ms") / 1000.0}%.1f | ${sum("proof_steps")}%.0f | $raw%.0f | $shr%.0f | ${if shr > 0 then raw / shr else 0.0}%.1fx |")
      say("")
      say("| configuration | clausified | of problems seen |")
      say("|---|---:|---:|")
      for c <- clausifyOnly do say(s"| $c | ${done(c).size} | ${rows.count(_.config == c)} |")
      say("")

    // ── how checking time grows with proof size ─────────────────────────────────────────────────────────────
    // Slope of log(check time) on log(size): above 1, checking degrades as proofs grow.
    val checked = rows.filter(r => r.solved && r.d("check_ms").exists(_ > 0))
    if checked.nonEmpty then
      say("## Checking time against proof size\n")
      say("| size measure | proofs | slope of log(check) on log(size) | reading |")
      say("|---|---:|---:|---|")
      for size <- Seq("proof_steps", "raw_size", "shared_size") do
        val pts = checked.flatMap(r => for s <- r.d(size) if s > 0; c <- r.d("check_ms") if c > 0 yield (math.log(s), math.log(c)))
        if pts.size >= 3 then
          val (xs, ys) = pts.unzip
          val mx = xs.sum / xs.size
          val my = ys.sum / ys.size
          val sxy = pts.map((x, y) => (x - mx) * (y - my)).sum
          val sxx = xs.map(x => (x - mx) * (x - mx)).sum
          val slope = if sxx == 0 then Double.NaN else sxy / sxx
          val reading =
            if slope < 0.9 then "sub-linear: the cost per unit falls as proofs grow"
            else if slope < 1.15 then "linear: a constant cost per unit"
            else "super-linear: checking degrades as proofs grow"
          say(f"| $size | ${pts.size} | $slope%.2f | $reading |")
      say("")

    // ── the proofs themselves ───────────────────────────────────────────────────────────────────────────────
    val refutations = rows.count(_.solved)
    val bad = rows.count(_.s("verdict") == "BAD_PROOF")
    val sorry = rows.count(r => r.solved && r.s("uses_sorry") == "true")
    val unchecked = rows.count(_.s("verdict") == "UNCHECKED")
    say("## Proofs\n")
    say(s"- refutations: $refutations")
    say(s"- rejected by the kernel: **$bad**")
    say(s"- valid only through a `Sorry`: **$sorry**")
    if unchecked > 0 then say(s"- built but not checked within the budget: $unchecked")
    say("")

    out.foreach { f =>
      Option(f.getAbsoluteFile.getParentFile).foreach(_.mkdirs())
      Using.resource(new PrintWriter(f, "UTF-8"))(_.print(md.toString))
      println(s"wrote ${f.getPath}")
    }

  // ── rows ──────────────────────────────────────────────────────────────────────────────────────────────────

  private final case class Row(m: Map[String, String]):
    def s(k: String): String = m.getOrElse(k, "")
    def d(k: String): Option[Double] = s(k).toDoubleOption
    def i(k: String): Option[Int] = s(k).toIntOption
    def config: String = s("config")
    def strategy: String = s("strategy")
    def solved: Boolean = s("verdict") == "REFUTED"

    /**
     * The problem's file name without its directory, since some runs record a full path and others do not.
     */
    def problem: String =
      val p = s("problem")
      p.substring(math.max(p.lastIndexOf('/'), p.lastIndexOf('\\')) + 1)

    /**
     * What the run cost end to end; a phase a configuration does not run is absent, not zero.
     */
    def totalMs: Option[Double] =
      for c <- d("clausify_ms"); s <- d("search_ms")
      yield c + s + d("reconstruct_ms").getOrElse(0.0) + d("check_ms").getOrElse(0.0)

  /**
   * The time of each problem `config` solved: the fastest of its strategies, as the first to finish wins.
   */
  private def solvedTimes(rows: Vector[Row], config: String): Map[String, Double] =
    rows
      .filter(r => r.config == config && r.solved)
      .groupBy(_.problem)
      .flatMap { (p, v) =>
        val ts = v.flatMap(_.totalMs); if ts.isEmpty then None else Some(p -> ts.min)
      }

  /**
   * The problems both configurations solved, and what each spent on them.
   */
  private def bothSolved(rows: Vector[Row], a: String, b: String): (Int, Double, Double) =
    val ta = solvedTimes(rows, a)
    val tb = solvedTimes(rows, b)
    val shared = ta.keySet intersect tb.keySet
    (shared.size, shared.toSeq.map(ta).sum, shared.toSeq.map(tb).sum)

  // ── CSV ───────────────────────────────────────────────────────────────────────────────────────────────────

  private def readCsv(file: File): Vector[Map[String, String]] =
    Using.resource(Source.fromFile(file, "UTF-8")) { src =>
      val lines = src.getLines().toVector
      if lines.isEmpty then Vector.empty
      else
        val header = splitCsv(lines.head)
        lines.tail.filter(_.trim.nonEmpty).map(l => header.zip(splitCsv(l)).toMap)
    }

  /**
   * One CSV line, honouring quotes, which the `detail` column needs.
   */
  private def splitCsv(line: String): Vector[String] =
    val out = Vector.newBuilder[String]
    val cur = new StringBuilder
    var quoted = false
    var i = 0
    while i < line.length do
      val c = line.charAt(i)
      if quoted then
        if c == '"' then
          if i + 1 < line.length && line.charAt(i + 1) == '"' then { cur += '"'; i += 1 }
          else quoted = false
        else cur += c
      else if c == '"' then quoted = true
      else if c == ',' then { out += cur.toString; cur.clear() }
      else cur += c
      i += 1
    out += cur.toString
    out.result()
