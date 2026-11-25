import sbt.*
import sbt.Keys.*

/**
 * Provide a forked draft run with the same main-class completion as runMain.
 */
object RunDraft:
  val runDraft = inputKey[Unit]("Check a development while admitting its dependencies.")

  val settings: Seq[Def.Setting[?]] = Seq(
    runDraft / aggregate := false,
    runDraft := {
      val (main, args) = Defaults.loadForParser(Compile / discoveredMainClasses)((state, names) => Defaults.runMainParser(state, names.getOrElse(Nil))).parsed

      val options = (Compile / run / forkOptions).value
      val log = streams.value.log
      val converter = fileConverter.value
      val classpath = (Runtime / fullClasspath).value.map(entry => converter.toPath(entry.data))
      val draftOptions = options
        .withRunJVMOptions(options.runJVMOptions :+ s"-Dlisa.draft.target=$main")
        .withOutputStrategy(options.outputStrategy.getOrElse(OutputStrategy.LoggedOutput(log)))
      new ForkRun(draftOptions).run(main, classpath, args, log).get
    }
  )
