/**
 * Helper main used by [[RunAllTheorems]] to check one proof module per JVM.
 *
 * Running many `object ... extends lisa.Main` in the same JVM can fail because `DEF(...)` registers
 * global symbols that cannot be redefined. Forking a fresh JVM per module avoids collisions.
 */
object RunOneTheoremModule {
  def main(args: Array[String]): Unit = {
    val name =
      args.headOption.getOrElse(sys.error("Usage: RunOneTheoremModule <fully.qualified.Object$>"))

    val loader = Thread.currentThread().getContextClassLoader
    val cls = Class.forName(name, true, loader)

    // Force Scala object initialization
    cls.getField("MODULE$").get(null)
  }
}

