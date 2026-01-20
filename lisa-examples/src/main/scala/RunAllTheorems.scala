import java.net.URI
import java.nio.file.{Files, Path, Paths}
import java.util.jar.JarFile
import scala.jdk.CollectionConverters.*

/**
 * Runtime checker for LISA proof modules.
 *
 * `sbt compile` only typechecks Scala; this runner forces initialization of every compiled
 * Scala `object ... extends lisa.Main` under `lisa.maths.*`, which triggers theorem checking.
 *
 * Usage:
 *   - `sbt "lisa-examples/runMain RunAllTheorems"` (checks `lisa.maths`)
 *   - `sbt "lisa-examples/runMain RunAllTheorems --prefix lisa.maths.MathlibPort"`
 */
object RunAllTheorems {

  private final case class Config(prefixes: List[String], mode: String)

  private def parseArgs(args: Array[String]): Config = {
    val prefixes = args.toList
      .sliding(2, 1)
      .collect { case List("--prefix", p) => p }
      .toList

    val mode =
      if args.contains("--in-process") then "in-process"
      else "subprocess"

    Config(prefixes = if prefixes.nonEmpty then prefixes else List("lisa.maths"), mode = mode)
  }

  private def basesFromResources(loader: ClassLoader, pkgPath: String): (List[Path], List[Path]) = {
    val segments = pkgPath.split('/').filter(_.nonEmpty).toList
    val urls = loader.getResources(pkgPath).asScala.toList

    val (dirUrls, jarUrls) = urls.partition(_.getProtocol == "file")

    val dirs = dirUrls.flatMap { url =>
      try {
        var p = Paths.get(url.toURI)
        segments.foreach(_ => p = p.getParent)
        Some(p)
      } catch {
        case _: Exception => None
      }
    }.distinct

    val jars = jarUrls.flatMap { url =>
      try {
        // e.g. jar:file:/.../foo.jar!/lisa/maths
        val spec = url.getFile
        val bang = spec.indexOf("!/")
        val jarPart = if bang >= 0 then spec.substring(0, bang) else spec
        val jarUri = if jarPart.startsWith("file:") then URI(jarPart) else URI("file:" + jarPart)
        Some(Paths.get(jarUri))
      } catch {
        case _: Exception => None
      }
    }.distinct

    (dirs, jars)
  }

  private def classNamesUnder(base: Path, pkgPath: String): List[String] = {
    val root = base.resolve(pkgPath)
    if !Files.isDirectory(root) then return Nil

    val it = Files.walk(root).iterator().asScala
    it.filter(p => Files.isRegularFile(p) && p.getFileName.toString.endsWith("$.class"))
      .map { p =>
        val rel = base.relativize(p).toString.replace(java.io.File.separatorChar, '.')
        rel.stripSuffix(".class")
      }
      .toList
  }

  private def classNamesInJar(jarPath: Path, pkgPath: String): List[String] = {
    if !Files.isRegularFile(jarPath) then return Nil
    val prefix = if pkgPath.endsWith("/") then pkgPath else pkgPath + "/"
    val jar = JarFile(jarPath.toFile)
    try {
      jar.entries().asScala
        .map(_.getName)
        .filter(n => n.startsWith(prefix) && n.endsWith("$.class"))
        .map(_.replace('/', '.').stripSuffix(".class"))
        .toList
    } finally jar.close()
  }

  def main(args: Array[String]): Unit = {
    val config = parseArgs(args)
    val pkgPath = "lisa/maths"

    val loader = Thread.currentThread().getContextClassLoader
    val (dirBases, jarBases) = basesFromResources(loader, pkgPath)

    val allCandidates =
      (dirBases.flatMap(b => classNamesUnder(b, pkgPath)) ++ jarBases.flatMap(j => classNamesInJar(j, pkgPath)))
        .distinct
        .sorted
    val filteredByPrefix =
      allCandidates.filter(n => config.prefixes.exists(p => n.startsWith(p + ".") || n == p || n.startsWith(p + "$")))

    val mainClass = classOf[lisa.Main]

    val toCheck = filteredByPrefix.flatMap { name =>
      try {
        val cls = Class.forName(name, false, loader)
        if mainClass.isAssignableFrom(cls) then Some(name) else None
      } catch {
        case _: ClassNotFoundException => None
        case _: NoClassDefFoundError   => None
      }
    }

    println(s"[RunAllTheorems] prefixes: ${config.prefixes.mkString(", ")}")
    println(s"[RunAllTheorems] mode: ${config.mode}")
    println(s"[RunAllTheorems] found ${toCheck.size} modules extending lisa.Main under `lisa.maths`")

    if config.mode == "in-process" then {
      println(
        "[RunAllTheorems] WARNING: --in-process can fail due to global symbol redefinitions (DEF). Prefer default subprocess mode."
      )

      var checked = 0
      toCheck.foreach { name =>
        checked += 1
        if checked % 25 == 0 || checked == 1 || checked == toCheck.size then
          println(s"[RunAllTheorems] checking ($checked/${toCheck.size}) $name")

        val cls = Class.forName(name, true, loader)
        cls.getField("MODULE$").get(null)
      }

      println(s"[RunAllTheorems] OK: checked $checked modules (in-process)")
    } else {
      val cp = System.getProperty("java.class.path")
      val javaBin =
        Paths.get(System.getProperty("java.home"), "bin", if System.getProperty("os.name").toLowerCase.contains("win") then "java.exe" else "java").toString

      var checked = 0
      toCheck.foreach { name =>
        checked += 1
        if checked % 10 == 0 || checked == 1 || checked == toCheck.size then
          println(s"[RunAllTheorems] checking ($checked/${toCheck.size}) $name")

        val pb = new ProcessBuilder(javaBin, "-cp", cp, "RunOneTheoremModule", name)
        pb.inheritIO()
        val code = pb.start().waitFor()
        if code != 0 then sys.error(s"Module failed: $name (exit $code)")
      }

      println(s"[RunAllTheorems] OK: checked $checked modules (subprocess)")
    }
  }
}
