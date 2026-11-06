package lisa.utils

import lisa.utils.kernel.*

import java.io.{BufferedInputStream, DataInputStream, InputStream}
import java.nio.file.{Files, Path}
import java.util.zip.ZipFile
import scala.jdk.CollectionConverters.*
import scala.util.Using
import scala.util.control.NonFatal

/** Check named binary proof bundles against their declared imports, without admitting trusted steps. */
object SerializedProofCheck:
  case class Result(name: String, steps: Int, imports: Int, readNanos: Long, checkNanos: Long)

  /** Read both streams completely and check every proof in a bundle. Leave stream ownership to the caller. */
  def check(trees: InputStream, proofs: InputStream): Seq[Result] =
    val treeInput = new DataInputStream(new BufferedInputStream(trees))
    val proofInput = new DataInputStream(new BufferedInputStream(proofs))
    val start = System.nanoTime()
    val bundle = Serialization.proofsFromDataStream(treeInput, proofInput)
    val readNanos = System.nanoTime() - start
    require(bundle.nonEmpty, "Empty proof bundle")
    require(treeInput.read() == -1 && proofInput.read() == -1, "Trailing data in proof bundle")
    bundle.zipWithIndex.map { case ((name, proof, _), index) =>
      require(!proof.steps.exists {
        case _: Sorry | _: Axiom | _: Assume => true
        case _ => false
      }, s"$name: trusted proof step")
      val checkStart = System.nanoTime()
      val theorem = proof.check.fold(error => throw new IllegalArgumentException(s"$name: $error", error), identity)
      require(!theorem.usesSorry && theorem.axioms.isEmpty, s"$name: trusted proof dependency")
      require(theorem.assumptions.subsetOf(proof.imports.toSet), s"$name: undeclared proof assumption")
      Result(name, proof.steps.length, proof.imports.length, if index == 0 then readNanos else 0L, System.nanoTime() - checkStart)
    }

  /** Check every .trees/.proof pair in a ZIP archive and write a tab-separated result log. */
  def main(args: Array[String]): Unit =
    require(args.length == 2 || args.length == 3, "Usage: SerializedProofCheck <archive.zip> <results.tsv> [entry-regex]")
    val selection = args.lift(2).map(_.r)
    Using.resources(new ZipFile(args(0)), Files.newBufferedWriter(Path.of(args(1)))): (archive, output) =>
      val entries = archive.entries().asScala.filterNot(_.isDirectory).toVector
      require(entries.map(_.getName).distinct.size == entries.size, "Duplicate archive entry")
      val names = entries.map(_.getName).toSet
      val prefixes = names.collect {
        case name if name.endsWith(".trees") => name.stripSuffix(".trees")
        case name if name.endsWith(".proof") => name.stripSuffix(".proof")
      }.toVector.sorted.filter(prefix => selection.forall(_.matches(prefix)))
      require(prefixes.nonEmpty, "No serialized proofs found")
      output.write("file\tname\tstatus\tsteps\timports\tread_ns\tcheck_ns\tdetail\n")
      var passed = 0
      var failed = 0
      var totalSteps = 0L
      prefixes.foreach: prefix =>
        println(s"CHECK $prefix")
        try
          require(names(prefix + ".trees") && names(prefix + ".proof"), s"Missing paired stream: $prefix")
          val results = Using.resources(archive.getInputStream(archive.getEntry(prefix + ".trees")), archive.getInputStream(archive.getEntry(prefix + ".proof")))(check)
          results.foreach: result =>
            output.write(s"$prefix\t${result.name}\tPASS\t${result.steps}\t${result.imports}\t${result.readNanos}\t${result.checkNanos}\t\n")
            totalSteps += result.steps
          passed += 1
          println(s"PASS $prefix (${results.map(_.steps).sum} steps)")
        catch
          case NonFatal(error) =>
            failed += 1
            val detail = s"${error.getClass.getSimpleName}: ${error.getMessage}".replace('\n', ' ').replace('\t', ' ')
            output.write(s"$prefix\t\tFAIL\t0\t0\t0\t0\t$detail\n")
            System.err.println(s"FAIL $prefix: $detail")
        output.flush()
      println(s"RESULT bundles=${prefixes.size} passed=$passed failed=$failed steps=$totalSteps (relative to declared imports)")
      require(failed == 0, s"$failed proof bundles failed; see ${args(1)}")
