package lisa.utils.prooflib

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import lisa.SetTheoryLibrary
import lisa.kernel.proof.SCProofChecker

/** Verify cold generation and real reuse in separate JVMs and an isolated directory. */
object LibraryCacheCheck:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private def snapshot(): Map[String, (Long, java.nio.file.attribute.FileTime)] =
    val directory = Path.of("cache")
    if !Files.exists(directory) then Map.empty
    else
      val entries = Files.list(directory)
      try entries.iterator.asScala.filter(Files.isRegularFile(_)).map: path =>
        path.getFileName.toString -> (Files.size(path), Files.getLastModifiedTime(path))
      .toMap
      finally entries.close()

  def main(args: Array[String]): Unit =
    require(args.toList == List("cold") || args.toList == List("warm"))
    val warm = args(0) == "warm"
    val before = snapshot()
    require(warm == before.nonEmpty, "Expected an empty cold cache or a populated warm cache")
    require(SetTheoryLibrary.last.isEmpty, "Enable caching before any theorem or definition")
    SetTheoryLibrary.withCache()
    require(SetTheoryLibrary._withCache, "Caching was not enabled")
    val started = System.nanoTime()
    val output = new java.io.ByteArrayOutputStream
    Console.withOut(output):
      lisa.maths.SetTheory.Ordinals.TransfiniteRecursion.main(Array.empty)
    val log = output.toString(java.nio.charset.StandardCharsets.UTF_8)
    print(log)
    require(!log.contains("Error while reading theorems from file"), "A cached proof failed to load")
    val elapsed = (System.nanoTime() - started) / 1e9
    val theorems = List(lisa.maths.SetTheory.Ordinals.TransfiniteRecursion.transfiniteRecursion)
    theorems.foreach: theorem =>
      val cached = theorem.highProof.isEmpty
      println(s"CACHE_CHECK ${theorem.fullName}: cached=$cached")
      require(!theorem.innerJustification.withSorry, s"Admitted dependency in ${theorem.fullName}")
      require(theorem.kernelProof.exists(proof => SCProofChecker.checkSCProof(proof).isValid))
    val after = snapshot()
    println(f"CACHE_CHECK mode=${args(0)} elapsed=$elapsed%.3fs files=${after.size} bytes=${after.values.map(_._1).sum}")
    if warm then
      val rewritten = before.keySet.intersect(after.keySet).filter(name => before(name) != after(name))
      val added = after.keySet -- before.keySet
      val removed = before.keySet -- after.keySet
      println(s"CACHE_CHECK rewritten=${rewritten.size} added=${added.size} removed=${removed.size}")
      require(rewritten.isEmpty && added.isEmpty && removed.isEmpty, s"Warm cache changed: rewritten=$rewritten; added=$added; removed=$removed")
    require(theorems.forall(_.highProof.isEmpty == warm), "Unexpected cache hits or misses")
    println("CACHE_CHECK PASSED")
